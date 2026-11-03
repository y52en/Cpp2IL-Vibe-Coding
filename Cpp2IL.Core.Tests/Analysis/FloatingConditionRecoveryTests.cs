using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class FloatingConditionRecoveryTests
{
    [TestCase("ordered-greater-complement", true)]
    [TestCase("double", true)]
    [TestCase("value-return", true)]
    [TestCase("value-negated-equality", true)]
    [TestCase("value-different-pair", true)]
    [TestCase("value-source-address", false)]
    [TestCase("negated-boolean-equality", true)]
    [TestCase("negated-boolean-inequality", true)]
    [TestCase("late-type-single", true)]
    [TestCase("late-type-double", true)]
    [TestCase("compound-and", true)]
    [TestCase("compound-or", true)]
    [TestCase("compound-different-pair", false)]
    [TestCase("compound-source-address", false)]
    [TestCase("less-or-equal", true)]
    [TestCase("not-equal", true)]
    [TestCase("integer-input", false)]
    [TestCase("different-pair", false)]
    [TestCase("source-reassigned", false)]
    [TestCase("source-address", false)]
    [TestCase("flag-reassigned", false)]
    [TestCase("late-definition", false)]
    [TestCase("unsupported-unordered-only", false)]
    public void FourWayTruthProofPreservesNaNInfinityAndSignedZero(string shape, bool expected)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var type = shape == "integer-input" ? t.SystemInt32Type : shape.EndsWith("double") ? t.SystemDoubleType : t.SystemSingleType;
        var x = new LocalVariable("x", new(null, "x"), type);
        LocalVariable Flag(string name) => new(name, new(null, name), t.SystemBooleanType);
        var y=new LocalVariable("y",new(null,"y"),type);var other=Flag("other");var combined=Flag("combined");
        var compound=shape.StartsWith("compound-");
        var less=Flag("less");var equal=Flag("equal");var greater=Flag("greater");var partial=Flag("partial");
        var ordered=Flag("ordered");var unordered=Flag("unordered");var same=Flag("same");var negated=Flag("negated");var result=Flag("result");
        var instructions = new List<Instruction>
        {
            new(0,OpCode.CheckLess,less,x,new Immediate(0)),new(1,OpCode.CheckEqual,equal,x,new Immediate(0)),
            new(2,OpCode.CheckGreater,greater,x,shape.EndsWith("different-pair") ? new FloatLiteral(1) : new Immediate(0)),
            new(3,OpCode.Or,partial,less,equal),new(4,OpCode.Or,ordered,partial,greater),
            new(5,OpCode.Not,unordered,ordered),new(6,OpCode.CheckEqual,same,less,unordered),
            new(7,OpCode.Not,negated,same),new(8,OpCode.Or,result,negated,equal)
        };
        if(shape=="value-negated-equality")instructions[^1]=new(8,OpCode.Not,result,same);
        if(shape.StartsWith("negated-boolean-"))
        {
            instructions[6]=new(6,shape=="negated-boolean-equality"?OpCode.CheckEqual:OpCode.CheckNotEqual,same,less,unordered);
            instructions[^1]=new(8,OpCode.Not,result,same);
        }
        if(shape=="less-or-equal")instructions[^1]=new(8,OpCode.Or,result,less,equal);
        if(shape=="not-equal")
        {instructions[7]=new(7,OpCode.Or,negated,less,greater);instructions[^1]=new(8,OpCode.Or,result,negated,unordered);}
        if(shape=="unsupported-unordered-only")instructions[^1]=new(8,OpCode.Move,result,unordered);
        if(shape=="source-reassigned")instructions.Insert(0,new(9,OpCode.Move,x,new FloatLiteral(1)));
        if(shape.EndsWith("source-address"))instructions.Insert(0,new(9,OpCode.CallVoid,new StringLiteral("escape"),new AddressOf(x)));
        if(shape=="flag-reassigned")instructions.Add(new(9,OpCode.Move,result,new Immediate(1)));
        if(compound)
        {
            instructions.Add(new(20,OpCode.CheckGreater,other,y,new Immediate(0)));
            instructions.Add(new(21,shape=="compound-or"?OpCode.Or:OpCode.And,combined,result,other));
        }
        var graph = new ISILControlFlowGraph([]);var guard=new Block{ID=2};var yes=new Block{ID=3};var no=new Block{ID=4};
        graph.Blocks=[graph.EntryBlock,graph.ExitBlock,guard,yes,no];
        foreach(var b in graph.Blocks){b.Predecessors.Clear();b.Successors.Clear();}
        void Edge(Block a,Block b){a.Successors.Add(b);b.Predecessors.Add(a);}
        Edge(graph.EntryBlock,guard);Edge(guard,yes);Edge(guard,no);Edge(yes,graph.ExitBlock);Edge(no,graph.ExitBlock);
        graph.EntryBlock.Instructions=[new(10,OpCode.Jump,guard)];
        var jump=new Instruction(11,OpCode.ConditionalJump,yes,compound?combined:result);
        var valueConsumer=shape.StartsWith("value-");
        if(valueConsumer)instructions.Add(new(11,OpCode.Return,result));
        else instructions.Insert(shape=="late-definition"?0:instructions.Count,jump);
        guard.Instructions=instructions;
        yes.Instructions=[new(12,OpCode.Return,new Immediate(1))];no.Instructions=[new(13,OpCode.Return,new Immediate(0))];
        var method=new InjectedMethodAnalysisContext(t.SystemObjectType,"Caller",t.SystemBooleanType,MethodAttributes.Public|MethodAttributes.Static,[])
        {ControlFlowGraph=graph,ParameterLocals=compound?[x,y]:[x],Locals=[x,y,other,combined,less,equal,greater,partial,ordered,unordered,same,negated,result]};
        if(shape.StartsWith("late-type-"))
        {
            // The early pass must decline an unresolved scalar. Once the exact
            // type is recovered, the same graph must satisfy the same proof.
            x.Type=null;
            Assert.That(FloatingConditionRecovery.Run(method),Is.Zero);
            x.Type=type;
        }
        var original=graph.Instructions.Select(i=>i.ToString()).ToArray();
        var samples=new[]{double.NaN,double.NegativeInfinity,-2d,-0d,0d,(double)float.Epsilon,2d,double.PositiveInfinity};
        var inputs=samples.SelectMany(value=>samples.Select(otherValue=>(value,otherValue))).ToArray();
        var before=expected?inputs.Select(p=>Execute(graph,x,p.value,y,p.otherValue)).ToArray():[];
        var recovered=valueConsumer?FloatingConditionRecovery.RunValues(method):FloatingConditionRecovery.Run(method);
        if(valueConsumer && expected)Assert.That(recovered,Is.GreaterThan(0));
        else Assert.That(recovered,Is.EqualTo(expected?1:0));
        if(!expected){Assert.That(graph.Instructions.Select(i=>i.ToString()),Is.EqualTo(original));return;}
        Assert.That(inputs.Select(p=>Execute(graph,x,p.value,y,p.otherValue)),Is.EqualTo(before));
        Assert.That(jump.Operands[0],Is.SameAs(yes),"Do not invert CFG successors or change other flag consumers.");
        Assert.That(valueConsumer?FloatingConditionRecovery.RunValues(method):FloatingConditionRecovery.Run(method),Is.Zero);
        if(!compound && !valueConsumer) Assert.That(guard.Instructions.Last(i=>i.OpCode is OpCode.CheckGreater or OpCode.CheckLessOrEqual or OpCode.CheckNotEqual or OpCode.CheckGreaterOrEqual)
            .Operands[1],Is.SameAs(x));
    }

    private static double Execute(ISILControlFlowGraph graph,LocalVariable x,double input,LocalVariable y,double otherInput)
    {
        var values=new Dictionary<LocalVariable,double>{{x,input},{y,otherInput}};
        double V(IOperand o)=>o switch{LocalVariable l=>values[l],Immediate n=>n.Value,FloatLiteral n=>n.Value,DoubleLiteral n=>n.Value,_=>throw new InvalidOperationException()};
        var block=graph.EntryBlock;
        for(var step=0;step<32;step++)
        {
            Block? next=null;
            foreach(var i in block.Instructions)
            {
                var a=i.Operands;
                if(i.OpCode==OpCode.Return)return V(a[0]);
                if(i.OpCode==OpCode.Jump){next=(Block)a[0];continue;}
                if(i.OpCode==OpCode.ConditionalJump){next=V(a[1])!=0?(Block)a[0]:block.Successors.Single(b=>!ReferenceEquals(b,a[0]));continue;}
                var first=V(a[1]);var second=a.Count>2?V(a[2]):0;
                values[(LocalVariable)a[0]]=i.OpCode switch
                {OpCode.Move=>first,OpCode.Not=>first==0?1:0,OpCode.And=>(first!=0&&second!=0)?1:0,OpCode.Or=>(first!=0||second!=0)?1:0,
                 OpCode.CheckLess=>first<second?1:0,OpCode.CheckEqual=>first==second?1:0,OpCode.CheckGreater=>first>second?1:0,
                 OpCode.CheckLessOrEqual=>first<=second?1:0,OpCode.CheckGreaterOrEqual=>first>=second?1:0,OpCode.CheckNotEqual=>first!=second?1:0,_=>throw new InvalidOperationException()};
            }
            block=next??block.Successors.Single();
        }
        throw new InvalidOperationException("Fixture did not terminate.");
    }
}
