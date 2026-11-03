using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class BooleanConstantPhiRecoveryTests
{
    [TestCase("valid",true)]
    [TestCase("reverse",true)]
    [TestCase("or-constant",true)]
    [TestCase("fallthrough",true)]
    [TestCase("nested-copy",true)]
    [TestCase("or-consumer",true)]
    [TestCase("xor-consumer",true)]
    [TestCase("noncanonical",false)]
    [TestCase("negative",false)]
    [TestCase("known-int",false)]
    [TestCase("unknown-input",false)]
    [TestCase("cycle",false)]
    [TestCase("duplicate-def",false)]
    [TestCase("escaped",false)]
    [TestCase("no-bool-anchor",false)]
    [TestCase("wrong-edge",false)]
    [TestCase("malformed-phi",false)]
    [TestCase("integer-consumer",false)]
    [TestCase("integer-view",false)]
    public void OnlyAClosedCanonicalConstantNetworkWithBooleanUseIsTyped(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        LocalVariable Local(string name)=>new(name,new Register(null,name));
        var flag=Local("flag");flag.Type=t.SystemBooleanType;flag.ParameterIndex=0;
        var leftValue=Local("left");var rightValue=Local("right");var joined=Local("joined");var result=Local("result");
        var graph=new ISILControlFlowGraph([]);var guard=new Block{ID=2};var left=new Block{ID=3};
        var right=new Block{ID=4};var merge=new Block{ID=5};
        graph.Blocks=[graph.EntryBlock,graph.ExitBlock,guard,left,right,merge];
        foreach(var block in graph.Blocks){block.Predecessors.Clear();block.Successors.Clear();}
        void Edge(Block a,Block b){a.Successors.Add(b);b.Predecessors.Add(a);}
        Edge(graph.EntryBlock,guard);Edge(guard,left);Edge(guard,right);Edge(left,merge);Edge(right,merge);Edge(merge,graph.ExitBlock);
        graph.EntryBlock.Instructions=[new(0,OpCode.Jump,guard)];guard.Instructions=[new(1,OpCode.ConditionalJump,left,flag)];
        var leftWrite=new Instruction(2,OpCode.Move,leftValue,new Immediate(0));
        var rightWrite=new Instruction(4,OpCode.Move,rightValue,new Immediate(1));
        left.Instructions=[leftWrite,new(3,OpCode.Jump,merge)];right.Instructions=[rightWrite,new(5,OpCode.Jump,merge)];
        var phi=new Instruction(-1,OpCode.Phi,joined,leftValue,rightValue);
        var consume=new Instruction(6,OpCode.And,result,joined,flag);
        merge.Instructions=[phi,consume,new(7,OpCode.Return)];
        var method=new InjectedMethodAnalysisContext(t.SystemObjectType,"Caller",t.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[t.SystemBooleanType])
            {ControlFlowGraph=graph,ParameterLocals=[flag],Locals=[flag,leftValue,rightValue,joined,result]};
        if(shape=="reverse"){merge.Predecessors.Reverse();phi.SetOperands(joined,rightValue,leftValue);}
        if(shape=="or-constant"){rightWrite.OpCode=OpCode.Or;rightWrite.SetOperands(rightValue,new Immediate(0),new Immediate(1));}
        if(shape=="fallthrough")right.Instructions.RemoveAt(1);
        if(shape=="nested-copy")
        {
            var alias=Local("alias");method.Locals.Add(alias);
            merge.Instructions.Insert(1,new(8,OpCode.Move,alias,joined));consume.SetOperand(1,alias);
        }
        if(shape=="or-consumer")consume.OpCode=OpCode.Or;
        if(shape=="xor-consumer")consume.OpCode=OpCode.Xor;
        if(shape=="noncanonical")rightWrite.SetOperand(1,new Immediate(2));
        if(shape=="negative")rightWrite.SetOperand(1,new Immediate(-1));
        if(shape=="known-int")rightValue.Type=t.SystemInt32Type;
        if(shape=="unknown-input")rightWrite.SetOperand(1,Local("unknown"));
        if(shape=="cycle")rightWrite.SetOperand(1,joined);
        if(shape=="duplicate-def")left.Instructions.Insert(1,new(8,OpCode.Move,leftValue,new Immediate(1)));
        if(shape=="escaped")merge.Instructions.Insert(1,new(8,OpCode.CallVoid,new StringLiteral("observe"),new AddressOf(joined)));
        if(shape=="no-bool-anchor")flag.Type=t.SystemInt32Type;
        if(shape=="wrong-edge")phi.SetOperands(joined,rightValue,leftValue);
        if(shape=="malformed-phi")phi.SetOperands(joined,leftValue);
        if(shape=="integer-consumer")merge.Instructions.Insert(1,new(8,OpCode.Add,Local("sum"),joined,new Immediate(9)));
        if(shape=="integer-view")rightWrite.NativeIntegerSourceView=true;
        var before=graph.Instructions.Select(i=>i.ToString()).ToArray();
        var beforeOpcodes=graph.Instructions.Select(i=>i.OpCode).ToArray();
        Assert.That(BooleanConstantPhiRecovery.Run(method),Is.EqualTo(expected?(shape=="nested-copy"?4:3):0));
        if(!expected)
        {
            Assert.That(graph.Instructions.Select(i=>i.ToString()),Is.EqualTo(before));
            Assert.That(joined.Type,Is.Null);return;
        }
        Assert.That(leftValue.Type,Is.SameAs(t.SystemBooleanType));
        Assert.That(rightValue.Type,Is.SameAs(t.SystemBooleanType));
        Assert.That(joined.Type,Is.SameAs(t.SystemBooleanType));
        Assert.That(graph.Instructions.Select(i=>i.OpCode),Is.EqualTo(beforeOpcodes));
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(result.Type,Is.SameAs(t.SystemBooleanType));
        Assert.That(BooleanConstantPhiRecovery.Run(method),Is.Zero);
        // Native AND/OR/XOR and C# bool operations coincide for every proven
        // incoming 0/1 and flag. There is no pointer/noncanonical mask case.
        foreach(var value in new[]{0,1})foreach(var bit in new[]{0,1})
        {
            var native=consume.OpCode==OpCode.And?(value&bit):consume.OpCode==OpCode.Or?(value|bit):(value^bit);
            var managed=consume.OpCode==OpCode.And?((value!=0)&(bit!=0)):consume.OpCode==OpCode.Or?((value!=0)|(bit!=0)):((value!=0)^(bit!=0));
            Assert.That(native,Is.EqualTo(managed?1:0));
        }
    }
}
