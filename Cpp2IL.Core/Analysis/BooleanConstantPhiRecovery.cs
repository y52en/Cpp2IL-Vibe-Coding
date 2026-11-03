using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// An untyped SSA phi of native 0/1 constants may be consumed with a known
// managed bool. Prove every incoming value and every use before giving that
// closed, nonescaping network Boolean storage. Never infer bool from width,
// a return signature alone, or an arbitrary integer mask.
public static class BooleanConstantPhiRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not {} graph) return 0;
        var instructions=graph.Instructions.ToArray();
        var seeds=instructions.Where(i=>i.OpCode is OpCode.And or OpCode.Or or OpCode.Xor
            && i.NativeFloatingPointSize==0 && !i.NativeIntegerSourceView
            && i.Operands.Count==3 && i.Operands.Skip(1).Any(o=>o is LocalVariable {Type.FullName:"System.Boolean"})
            && i.Operands.Skip(1).Any(o=>o is LocalVariable {Type:null})).ToArray();
        if(seeds.Length==0)return 0;
        var definitions=instructions.Where(i=>i.Destination is LocalVariable)
            .GroupBy(i=>(LocalVariable)i.Destination!).Where(g=>g.Count()==1).ToDictionary(g=>g.Key,g=>g.Single());
        var homes=graph.Blocks.SelectMany(b=>b.Instructions.Select(i=>(i,b))).GroupBy(x=>x.i)
            .Where(g=>g.Count()==1).ToDictionary(g=>g.Key,g=>g.Single().b);
        var implicitWrites=instructions.Where(i=>i.ImplicitDefinition!=null)
            .Select(i=>(i.ImplicitDefinition!.Value.Number,i.ImplicitDefinition.Value.Name)).ToHashSet();
        var changed=0;
        foreach(var seed in seeds)
        foreach(var source in seed.Operands.Skip(1).OfType<LocalVariable>().Where(l=>l.Type==null).ToArray())
        {
            var nodes=new Dictionary<LocalVariable,Instruction>();var visiting=new HashSet<LocalVariable>();
            bool Constant(IOperand value)=>value is Immediate {Value:0 or 1};
            bool Collect(LocalVariable local)
            {
                if(visiting.Contains(local))return false;
                if(nodes.ContainsKey(local))return true;
                if(nodes.Count+visiting.Count>=64 || local.Type!=null || method.ParameterLocals.Contains(local)
                    || implicitWrites.Contains((local.Register.Number,local.Register.Name))
                    || !definitions.TryGetValue(local,out var definition) || !homes.TryGetValue(definition,out var home))return false;
                visiting.Add(local);
                bool Value(IOperand value)=>Constant(value) || value is LocalVariable input && Collect(input);
                var valid=definition switch
                {
                    {OpCode:OpCode.Move,Operands:[_,var input],NativeIntegerSourceView:false,NativeFloatingPointSize:0}=>Value(input),
                    {OpCode:OpCode.Or,Operands:[_,Immediate {Value:0 or 1},Immediate {Value:0 or 1}],
                        NativeIntegerSourceView:false,NativeFloatingPointSize:0}=>true,
                    {OpCode:OpCode.Phi}=>definition.Operands.Count==home.Predecessors.Count+1
                        && home.Predecessors.Count>0 && home.Predecessors.Distinct().Count()==home.Predecessors.Count
                        && definition.Operands.Skip(1).All(Value),
                    _=>false
                };
                visiting.Remove(local);
                if(valid)nodes[local]=definition;
                return valid;
            }
            if(!Collect(source))continue;
            var safe=true;
            foreach(var pair in nodes)
            foreach(var use in instructions)
            {
                var writeIndex=use.OpCode is OpCode.Call or OpCode.IndirectCall?1:0;
                for(var n=0;n<use.Operands.Count;n++)
                {
                    var operand=use.Operands[n];
                    if(n==writeIndex && ReferenceEquals(operand,use.Destination))continue;
                    if(!ForwardNullCheckRecovery.Uses(operand,pair.Key))continue;
                    if(!ReferenceEquals(operand,pair.Key)
                        || !(ReferenceEquals(use,seed) || use.Destination is LocalVariable output
                            && nodes.TryGetValue(output,out var definition) && ReferenceEquals(definition,use)))
                    {safe=false;break;}
                    if(use.OpCode==OpCode.Phi)
                    {
                        var home=homes[use];
                        if(n==0 || n>home.Predecessors.Count || home.Predecessors[n-1].Instructions.Count==0
                            || !ReferenceEquals(pair.Value,home.Predecessors[n-1].Instructions[^1])
                                && !ForwardNullCheckRecovery.DefinitionDominates(graph,pair.Value,home.Predecessors[n-1].Instructions[^1]))
                        {safe=false;break;}
                    }
                    else if(!ForwardNullCheckRecovery.DefinitionDominates(graph,pair.Value,use))
                    {safe=false;break;}
                }
                if(!safe)break;
            }
            if(!safe)continue;
            foreach(var local in nodes.Keys)
            {local.Type=method.AppContext.SystemTypes.SystemBooleanType;changed++;}
        }
        return changed;
    }
}
