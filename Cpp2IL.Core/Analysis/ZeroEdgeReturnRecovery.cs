using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// A native pointer register can be returned as integral zero on its null edge.
// Substitute that proven zero before return-signature typing can turn the
// register's reference-producing call (and every non-null use) into a bool.
public static class ZeroEdgeReturnRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        var resultType = method.ReturnType.IsEnumType ? method.ReturnType.EnumUnderlyingType : method.ReturnType;
        if (resultType?.FullName is not ("System.Boolean" or "System.Byte" or "System.SByte" or "System.Char"
            or "System.Int16" or "System.UInt16" or "System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64")
            || method.ControlFlowGraph is not {} graph) return 0;
        var definitions = graph.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).ToDictionary(g => g.Key, g => g.ToArray());
        var changes = 0;
        foreach (var guard in graph.Blocks)
        {
            if (guard.Successors.Count != 2 || guard.Successors.Distinct().Count() != 2
                || guard.Instructions.LastOrDefault() is not
                    {OpCode: OpCode.ConditionalJump, Operands: [Block target, LocalVariable condition]}
                || !guard.Successors.Contains(target)) continue;
            var inverted = false;
            var seen = new HashSet<LocalVariable>();
            var flag = condition;
            Instruction? predicate = null;
            var before = guard.Instructions.Count - 1;
            while (seen.Count < 8 && seen.Add(flag) && definitions.TryGetValue(flag, out var flagWrites)
                   && flagWrites.Length == 1)
            {
                var definition = flagWrites[0];
                var position = guard.Instructions.IndexOf(definition);
                if (position < 0 || position >= before) break;
                before = position;
                if (definition is {OpCode: OpCode.Not, Operands: [_, LocalVariable previous]})
                { inverted = !inverted; flag = previous; continue; }
                predicate = definition;
                break;
            }
            if (predicate is not {OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, var a, var b]}
                || predicate.NativeComparisonSize != method.AppContext.Binary.PointerSizeBytes
                || predicate.NativeIntegerSourceView) continue;
            var source = a is Immediate {Value: 0} ? b as LocalVariable : b is Immediate {Value: 0} ? a as LocalVariable : null;
            if (source == null || graph.Instructions.Any(i => i.Operands.Any(o => AddressExposed(o, source)))) continue;
            if (definitions.TryGetValue(source, out var writes))
            {
                if (writes.Length != 1 || method.ParameterLocals.Contains(source)
                    || !ForwardNullCheckRecovery.DefinitionDominates(graph, writes[0], predicate)) continue;
            }
            else if (!method.ParameterLocals.Contains(source)) continue;
            var nullBlock = (predicate.OpCode == OpCode.CheckEqual) != inverted
                ? target : guard.Successors.Single(block => !ReferenceEquals(block, target));
            // A shared return epilogue is not null-only, but its SSA input
            // corresponding to this exact guard edge is. Rewrite that input,
            // never the producer or an input from a different predecessor.
            // Do this before backward phi typing can contaminate the producer.
            var edge = nullBlock.Predecessors.IndexOf(guard);
            if (edge >= 0 && nullBlock.Predecessors.Distinct().Count() == nullBlock.Predecessors.Count)
                foreach (var phi in nullBlock.Instructions)
                {
                    if (phi is not {OpCode: OpCode.Phi, Destination: LocalVariable joined}
                        || phi.Operands.Count != nullBlock.Predecessors.Count + 1
                        || !ReferenceEquals(phi.Operands[edge + 1], source)
                        || method.ParameterLocals.Contains(joined)
                        || !definitions.TryGetValue(joined, out var joinedWrites) || joinedWrites.Length != 1
                        || graph.Instructions.Any(i => i.Operands.Any(o => AddressExposed(o, joined)))) continue;
                    var uses = graph.Instructions.Where(i => !ReferenceEquals(i, phi)
                        && i.Operands.Any(o => Contains(o, joined))).ToArray();
                    if (uses.Length == 0 || uses.Any(i => i is not
                        {OpCode: OpCode.Return, Operands: [LocalVariable returned]}
                        || !ReferenceEquals(returned, joined)
                        || !ForwardNullCheckRecovery.DefinitionDominates(graph, phi, i))) continue;
                    phi.SetOperand(edge + 1, new Immediate(0));
                    changes++;
                }
            // A join could enter this block from the non-null route. Restrict
            // the proof to its unique guard edge and direct return, before SSA
            // destruction or phi copies introduce alternate values.
            if (nullBlock.Predecessors.Count != 1 || !ReferenceEquals(nullBlock.Predecessors[0], guard)) continue;
            var zeroValues = new HashSet<LocalVariable> {source};
            var visited = new HashSet<Block>();
            var current = nullBlock;
            while (visited.Add(current))
            {
                foreach (var instruction in current.Instructions)
                {
                    // Only a single-definition copy evaluated on this proven
                    // edge inherits zero. Never infer values through a phi,
                    // arithmetic, a call, a redefinition or escaped storage.
                    if (instruction is {OpCode: OpCode.Move, Operands: [LocalVariable alias, LocalVariable value]}
                        && zeroValues.Contains(value) && !method.ParameterLocals.Contains(alias)
                        && definitions.TryGetValue(alias, out var copies) && copies.Length == 1
                        && !graph.Instructions.Any(i => i.Operands.Any(o => AddressExposed(o, alias))))
                        zeroValues.Add(alias);
                    if (instruction is {OpCode: OpCode.Return, Operands: [LocalVariable returned]}
                        && zeroValues.Contains(returned))
                    { instruction.SetOperand(0, new Immediate(0)); changes++; }
                }
                // Follow only an unconditional edge with no alternate entry.
                // In particular a shared epilogue is not a null-only block.
                if (current.Successors.Count != 1
                    || current.Instructions.LastOrDefault() is not {OpCode: OpCode.Jump, Operands: [Block next]}
                    || !ReferenceEquals(current.Successors[0], next)
                    || next.Predecessors.Count != 1 || !ReferenceEquals(next.Predecessors[0], current)) break;
                current = next;
            }
        }
        return changes;
    }

    private static bool Contains(IOperand operand, LocalVariable local) => operand switch
    {
        LocalVariable value => ReferenceEquals(value, local),
        AddressOf address => Contains(address.Target, local),
        MemoryOperand memory => memory.Base != null && Contains(memory.Base, local)
            || memory.Index != null && Contains(memory.Index, local),
        FieldReference field => ReferenceEquals(field.Local, local) || field.Parent != null && Contains(field.Parent, local),
        ArrayAccess array => ReferenceEquals(array.Array, local) || Contains(array.Index, local),
        ArrayLength array => ReferenceEquals(array.Array, local),
        _ => false
    };

    private static bool AddressExposed(IOperand operand, LocalVariable local) => operand switch
    {
        AddressOf address => Contains(address.Target, local),
        MemoryOperand memory => memory.Base != null && AddressExposed(memory.Base, local)
            || memory.Index != null && AddressExposed(memory.Index, local),
        FieldReference field => field.Parent != null && AddressExposed(field.Parent, local),
        ArrayAccess array => AddressExposed(array.Index, local),
        _ => false
    };
}
