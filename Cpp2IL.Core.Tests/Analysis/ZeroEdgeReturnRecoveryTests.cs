using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ZeroEdgeReturnRecoveryTests
{
    [TestCase("equal", true)]
    [TestCase("zero-left", true)]
    [TestCase("not-equal", true)]
    [TestCase("inverted-flag", true)]
    [TestCase("long-result", true)]
    [TestCase("unknown-width", false)]
    [TestCase("narrow-width", false)]
    [TestCase("integer-view", false)]
    [TestCase("nonzero-constant", false)]
    [TestCase("alternate-predecessor", false)]
    [TestCase("source-redefined", false)]
    [TestCase("source-after-predicate", false)]
    [TestCase("source-address", false)]
    [TestCase("condition-redefined", false)]
    [TestCase("different-return", false)]
    [TestCase("reference-result", false)]
    [TestCase("bridge", true)]
    [TestCase("two-bridges", true)]
    [TestCase("copy-return", true)]
    [TestCase("copy-bridge", true)]
    [TestCase("bridge-alternate-predecessor", false)]
    [TestCase("bridge-cycle", false)]
    [TestCase("copy-redefined", false)]
    [TestCase("copy-address", false)]
    [TestCase("copy-nonzero", false)]
    public void OnlyAFullWidthZeroEdgeCanReplaceTheSameStableReturnedValue(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var t = app.SystemTypes;
        LocalVariable Local(string name) => new(name, new Register(null, name));
        var source = Local("source"); var flag = Local("flag"); var result = Local("result");
        var get = new InjectedMethodAnalysisContext(t.SystemObjectType, "Get", t.SystemStringType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var checkReturnType = shape == "long-result" ? t.SystemInt64Type : t.SystemBooleanType;
        var check = new InjectedMethodAnalysisContext(t.SystemObjectType, "Check", checkReturnType,
            MethodAttributes.Public | MethodAttributes.Static, [t.SystemStringType]);
        var graph = new ISILControlFlowGraph([]);
        var guard = new Block {ID = 2}; var nullBlock = new Block {ID = 3}; var nonnull = new Block {ID = 4};
        graph.Blocks = [graph.EntryBlock, graph.ExitBlock, guard, nullBlock, nonnull];
        foreach (var block in graph.Blocks) { block.Predecessors.Clear(); block.Successors.Clear(); }
        void Edge(Block a, Block b) { a.Successors.Add(b); b.Predecessors.Add(a); }
        Edge(graph.EntryBlock, guard); Edge(guard, nullBlock); Edge(guard, nonnull);
        Edge(nullBlock, graph.ExitBlock); Edge(nonnull, graph.ExitBlock);
        var producer = new Instruction(0, OpCode.Call, get, source);
        graph.EntryBlock.Instructions = [producer, new(1, OpCode.Jump, guard)];
        var predicate = new Instruction(2, OpCode.CheckEqual, flag, source, new Immediate(0))
            {NativeComparisonSize = app.Binary.PointerSizeBytes};
        var jump = new Instruction(3, OpCode.ConditionalJump, nullBlock, flag);
        guard.Instructions = [predicate, jump];
        var returned = new Instruction(4, OpCode.Return, source);
        nullBlock.Instructions = [returned];
        nonnull.Instructions = [new(5, OpCode.Call, check, result, source), new(6, OpCode.Return, result)];
        var returnType = shape == "reference-result" ? t.SystemStringType
            : shape == "long-result" ? t.SystemInt64Type : t.SystemBooleanType;
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Caller", returnType,
            MethodAttributes.Public | MethodAttributes.Static, [])
            {ControlFlowGraph = graph, ParameterLocals = [], Locals = [source, flag, result]};
        if (shape == "zero-left") predicate.SetOperands(flag, new Immediate(0), source);
        if (shape == "not-equal") { predicate.OpCode = OpCode.CheckNotEqual; jump.SetOperand(0, nonnull); }
        if (shape == "inverted-flag")
        {
            var inverse = Local("inverse");
            guard.Instructions.Insert(1, new(7, OpCode.Not, inverse, flag)); jump.SetOperands(nonnull, inverse);
        }
        if (shape == "unknown-width") predicate.NativeComparisonSize = 0;
        if (shape == "narrow-width") predicate.NativeComparisonSize = app.Binary.PointerSizeBytes / 2;
        if (shape == "integer-view") predicate.NativeIntegerSourceView = true;
        if (shape == "nonzero-constant") predicate.SetOperand(2, new Immediate(1));
        if (shape == "alternate-predecessor") Edge(nonnull, nullBlock);
        if (shape == "source-redefined") nullBlock.Instructions.Insert(0, new(7, OpCode.Move, source, new Immediate(1)));
        if (shape == "source-after-predicate")
        { graph.EntryBlock.Instructions.Remove(producer); guard.Instructions.Insert(1, producer); }
        if (shape == "source-address") guard.Instructions.Insert(1, new(7, OpCode.CallVoid, check, new AddressOf(source)));
        if (shape == "condition-redefined") guard.Instructions.Insert(1, new(7, OpCode.Move, flag, new Immediate(0)));
        if (shape == "different-return") returned.SetOperand(0, result);
        if (shape is "bridge" or "two-bridges" or "copy-bridge" or "bridge-alternate-predecessor" or "bridge-cycle")
        {
            var bridge = new Block {ID = 5}; graph.Blocks.Add(bridge);
            nullBlock.Successors.Clear(); graph.ExitBlock.Predecessors.Remove(nullBlock);
            nullBlock.Instructions = [new(8, OpCode.Jump, bridge)];
            bridge.Instructions = [returned]; Edge(nullBlock, bridge); Edge(bridge, graph.ExitBlock);
            if (shape == "bridge-alternate-predecessor") Edge(nonnull, bridge);
            if (shape == "two-bridges")
            {
                var second = new Block {ID = 6}; graph.Blocks.Add(second);
                bridge.Successors.Clear(); graph.ExitBlock.Predecessors.Remove(bridge);
                bridge.Instructions = [new(9, OpCode.Jump, second)];
                second.Instructions = [returned]; Edge(bridge, second); Edge(second, graph.ExitBlock);
            }
            if (shape == "bridge-cycle")
            {
                bridge.Successors.Clear(); graph.ExitBlock.Predecessors.Remove(bridge);
                bridge.Instructions = [new(9, OpCode.Jump, nullBlock)]; Edge(bridge, nullBlock);
            }
        }
        if (shape.StartsWith("copy-"))
        {
            var alias = Local("alias"); method.Locals.Add(alias);
            nullBlock.Instructions.Insert(0, new(10, OpCode.Move, alias, source)); returned.SetOperand(0, alias);
            if (shape == "copy-redefined") nullBlock.Instructions.Insert(1, new(11, OpCode.Move, alias, new Immediate(1)));
            if (shape == "copy-address") nullBlock.Instructions.Insert(1, new(11, OpCode.CallVoid, check, new AddressOf(alias)));
            if (shape == "copy-nonzero") nullBlock.Instructions[0].SetOperand(1, new Immediate(1));
        }
        var before = graph.Instructions.Select(i => i.ToString()).ToArray();
        var observations = expected ? new[] {Execute(graph, 0), Execute(graph, 123)} : [];
        Assert.That(ZeroEdgeReturnRecovery.Run(method), Is.EqualTo(expected ? 1 : 0));
        if (!expected)
        {
            Assert.That(graph.Instructions.Select(i => i.ToString()), Is.EqualTo(before));
            return;
        }
        Assert.That(returned.Operands[0], Is.TypeOf<Immediate>());
        Assert.That(((Immediate)returned.Operands[0]).Value, Is.Zero);
        Assert.That(new[] {Execute(graph, 0), Execute(graph, 123)}, Is.EqualTo(observations));
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(source.Type, Is.SameAs(t.SystemStringType), "Return typing must not poison the reference-producing call.");
        Assert.That(result.Type, Is.SameAs(checkReturnType));
        Assert.That(ZeroEdgeReturnRecovery.Run(method), Is.Zero, "The recovery is idempotent.");
    }

    [TestCase("shared", true)]
    [TestCase("reversed-predecessors", true)]
    [TestCase("not-equal", true)]
    [TestCase("inverted", true)]
    [TestCase("narrow", false)]
    [TestCase("unknown-width", false)]
    [TestCase("integer-view", false)]
    [TestCase("wrong-edge", false)]
    [TestCase("malformed-phi", false)]
    [TestCase("duplicate-predecessor", false)]
    [TestCase("redefined-source", false)]
    [TestCase("escaped-source", false)]
    [TestCase("other-joined-use", false)]
    [TestCase("reference-result", false)]
    public void SharedReturnPhiRewritesOnlyTheProvenZeroIncomingEdge(string shape, bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        LocalVariable Local(string name)=>new(name,new Register(null,name));
        var source=Local("source");var flag=Local("flag");var success=Local("success");var joined=Local("joined");
        var get=new InjectedMethodAnalysisContext(t.SystemObjectType,"Get",t.SystemStringType,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        var check=new InjectedMethodAnalysisContext(t.SystemObjectType,"Check",t.SystemBooleanType,
            MethodAttributes.Public|MethodAttributes.Static,[t.SystemStringType]);
        var graph=new ISILControlFlowGraph([]);
        var guard=new Block{ID=2};var nonnull=new Block{ID=3};var join=new Block{ID=4};
        graph.Blocks=[graph.EntryBlock,graph.ExitBlock,guard,nonnull,join];
        foreach(var block in graph.Blocks){block.Predecessors.Clear();block.Successors.Clear();}
        void Edge(Block a,Block b){a.Successors.Add(b);b.Predecessors.Add(a);}
        Edge(graph.EntryBlock,guard);Edge(guard,join);Edge(guard,nonnull);Edge(nonnull,join);Edge(join,graph.ExitBlock);
        graph.EntryBlock.Instructions=[new(0,OpCode.Call,get,source),new(1,OpCode.Jump,guard)];
        var predicate=new Instruction(2,OpCode.CheckEqual,flag,source,new Immediate(0))
            {NativeComparisonSize=app.Binary.PointerSizeBytes};
        var branch=new Instruction(3,OpCode.ConditionalJump,join,flag);guard.Instructions=[predicate,branch];
        nonnull.Instructions=[new(4,OpCode.Call,check,success,source),new(5,OpCode.Jump,join)];
        var phi=new Instruction(-1,OpCode.Phi,joined,source,success);
        join.Instructions=[phi,new(6,OpCode.Return,joined)];
        var method=new InjectedMethodAnalysisContext(t.SystemObjectType,"Caller",
            shape=="reference-result"?t.SystemStringType:t.SystemBooleanType,
            MethodAttributes.Public|MethodAttributes.Static,[])
            {ControlFlowGraph=graph,ParameterLocals=[],Locals=[source,flag,success,joined]};
        if(shape=="reversed-predecessors"){join.Predecessors.Reverse();phi.SetOperands(joined,success,source);}
        if(shape=="not-equal"){predicate.OpCode=OpCode.CheckNotEqual;branch.SetOperand(0,nonnull);}
        if(shape=="inverted"){
            var inverse=Local("inverse");method.Locals.Add(inverse);
            guard.Instructions.Insert(1,new(7,OpCode.Not,inverse,flag));branch.SetOperands(nonnull,inverse);
        }
        if(shape=="narrow")predicate.NativeComparisonSize=app.Binary.PointerSizeBytes/2;
        if(shape=="unknown-width")predicate.NativeComparisonSize=0;
        if(shape=="integer-view")predicate.NativeIntegerSourceView=true;
        if(shape=="wrong-edge")phi.SetOperands(joined,success,source);
        if(shape=="malformed-phi")phi.SetOperands(joined,source);
        if(shape=="duplicate-predecessor")join.Predecessors.Add(guard);
        if(shape=="redefined-source")nonnull.Instructions.Insert(0,new(8,OpCode.Move,source,new Immediate(1)));
        if(shape=="escaped-source")guard.Instructions.Insert(1,new(8,OpCode.CallVoid,check,new AddressOf(source)));
        if(shape=="other-joined-use")join.Instructions.Insert(1,new(8,OpCode.CallVoid,check,joined));
        var before=graph.Instructions.Select(i=>i.ToString()).ToArray();
        var observations=expected?new[]{Execute(graph,0),Execute(graph,123)}:[];
        Assert.That(ZeroEdgeReturnRecovery.Run(method),Is.EqualTo(expected?1:0));
        if(!expected){Assert.That(graph.Instructions.Select(i=>i.ToString()),Is.EqualTo(before));return;}
        var index=join.Predecessors.IndexOf(guard)+1;
        Assert.That(phi.Operands[index],Is.TypeOf<Immediate>());
        Assert.That(((Immediate)phi.Operands[index]).Value,Is.Zero);
        Assert.That(phi.Operands[join.Predecessors.IndexOf(nonnull)+1],Is.SameAs(success));
        Assert.That(new[]{Execute(graph,0),Execute(graph,123)},Is.EqualTo(observations));
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(source.Type,Is.SameAs(t.SystemStringType));
        Assert.That(joined.Type,Is.SameAs(t.SystemBooleanType));
        Assert.That(success.Type,Is.SameAs(t.SystemBooleanType));
        Assert.That(ZeroEdgeReturnRecovery.Run(method),Is.Zero);
    }

    private static long Execute(ISILControlFlowGraph graph, long input)
    {
        var values = new Dictionary<LocalVariable, long>();
        long Value(IOperand operand) => operand is Immediate immediate ? immediate.Value : values[(LocalVariable)operand];
        var block = graph.EntryBlock;
        Block? previous = null;
        for (var steps = 0; steps < 32; steps++)
        {
            Block? next = null;
            foreach (var instruction in block.Instructions)
            {
                var operands = instruction.Operands;
                switch (instruction.OpCode)
                {
                    case OpCode.Phi:
                        values[(LocalVariable)operands[0]]=Value(operands[block.Predecessors.IndexOf(previous!)+1]);
                        break;
                    case OpCode.Move: values[(LocalVariable)operands[0]] = Value(operands[1]); break;
                    case OpCode.Call:
                        values[(LocalVariable)operands[1]] = ((MethodAnalysisContext)operands[0]).Name == "Get" ? input : 1;
                        break;
                    case OpCode.CheckEqual: values[(LocalVariable)operands[0]] = Value(operands[1]) == Value(operands[2]) ? 1 : 0; break;
                    case OpCode.CheckNotEqual: values[(LocalVariable)operands[0]] = Value(operands[1]) != Value(operands[2]) ? 1 : 0; break;
                    case OpCode.Not: values[(LocalVariable)operands[0]] = Value(operands[1]) == 0 ? 1 : 0; break;
                    case OpCode.Jump: next = (Block)operands[0]; break;
                    case OpCode.ConditionalJump:
                        next = Value(operands[1]) != 0 ? (Block)operands[0] : block.Successors.Single(b => !ReferenceEquals(b, operands[0]));
                        break;
                    case OpCode.Return: return Value(operands[0]);
                    default: throw new System.InvalidOperationException("Unexpected fixture instruction.");
                }
            }
            previous=block;
            block = next ?? block.Successors.Single();
        }
        throw new System.InvalidOperationException("Fixture failed to terminate.");
    }
}
