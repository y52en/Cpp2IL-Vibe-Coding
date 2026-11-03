using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// A floating comparison has four outcomes, not the integer trichotomy.
// Prove a boolean flag DAG against all four, including unordered (NaN).
public static class FloatingConditionRecovery
{
    private static readonly (int Mask, OpCode Code)[] Relations =
    [(1, OpCode.CheckLess), (2, OpCode.CheckEqual), (4, OpCode.CheckGreater),
     (3, OpCode.CheckLessOrEqual), (6, OpCode.CheckGreaterOrEqual), (13, OpCode.CheckNotEqual)];

    public static int Run(MethodAnalysisContext method) => RunCore(method, false);

    // Boolean flag expressions also feed returns, selects, stores and calls.
    // Prove each complete logical value independently at its definition; do
    // not distribute a truth table across comparisons of different pairs.
    public static int RunValues(MethodAnalysisContext method) => RunCore(method, true);

    private static int RunCore(MethodAnalysisContext method, bool values)
    {
        if (method.ControlFlowGraph is not {} graph) return 0;
        var instructions = graph.Instructions.ToArray();
        if (!instructions.Any(i => i.Operands is [_, LocalVariable {Type.FullName: "System.Single" or "System.Double"}, _]
            && Relations.Any(r => r.Code == i.OpCode))) return 0;
        var writes = instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).ToDictionary(g => g.Key, g => g.ToArray());
        var homes = graph.Blocks.SelectMany(b => b.Instructions.Select(i => (i, b))).ToDictionary(p => p.i, p => p.b);
        var dominance = new DominatorInfo(graph);
        bool Before(Instruction a, Instruction b) => ReferenceEquals(homes[a], homes[b])
            ? homes[a].Instructions.IndexOf(a) < homes[b].Instructions.IndexOf(b) : dominance.Dominates(homes[a], homes[b]);
        bool Stable(LocalVariable value, Instruction use) =>
            !instructions.Any(i => i.Operands.Any(o => o is AddressOf {Target: LocalVariable local} && ReferenceEquals(local, value))
                || i.ImplicitDefinition != null && Equals(i.ImplicitDefinition, value.Register))
            && (writes.TryGetValue(value, out var definitions)
                ? definitions.Length == 1 && !method.ParameterLocals.Contains(value) && Before(definitions[0], use)
                : method.ParameterLocals.Contains(value));
        var changed = 0;
        var consumers = values
            ? instructions.Where(i => i.OpCode != OpCode.ConditionalJump)
                .SelectMany(i => i.Operands.OfType<LocalVariable>()
                    .Where(v => v.Type?.FullName == "System.Boolean" && !ReferenceEquals(i.Destination, v))
                    .Distinct().Select(v => (Use: i, Condition: v))).ToArray()
            : instructions.Where(i => i.OpCode == OpCode.ConditionalJump
                    && i.Operands is [_, LocalVariable])
                .Select(i => (Use: i, Condition: (LocalVariable)i.Operands[1])).ToArray();
        foreach (var (branch, condition) in consumers)
        {
            if (!writes.TryGetValue(condition, out var roots) || roots.Length != 1 || !Before(roots[0], branch)) continue;
            // Preserve the whole-condition proof first. If independent floating
            // pairs are joined by AND/OR, prove only complete immediate children:
            // never combine different operand pairs or rewrite CFG successors.
            var candidates = new List<Instruction> { roots[0] };
            if (roots[0].OpCode is OpCode.And or OpCode.Or)
                foreach (var operand in roots[0].Operands.Skip(1))
                    if (operand is LocalVariable {Type.FullName: "System.Boolean"} flag
                        && writes.TryGetValue(flag, out var definitions) && definitions.Length == 1
                        && Before(definitions[0], roots[0]) && !candidates.Contains(definitions[0]))
                        candidates.Add(definitions[0]);
            foreach (var root in candidates)
            {
                if (root is {OpCode: OpCode.Not, Operands: [_, LocalVariable directCondition]}
                    && writes.TryGetValue(directCondition, out var directWrites) && directWrites.Length == 1
                    && Relations.Any(r => r.Code == directWrites[0].OpCode)
                    && directWrites[0].Operands is [_, LocalVariable {Type.FullName: "System.Single" or "System.Double"}, _]) continue;
                IOperand? left = null, right = null; string? scalar = null;
                var cache = new Dictionary<LocalVariable, int>(); var active = new HashSet<LocalVariable>();
                bool Same(IOperand a, IOperand b) => ReferenceEquals(a, b) || a.Equals(b);
                bool FloatingPair(IOperand a, IOperand b, Instruction use)
                {
                    if (a is not LocalVariable {Type.FullName: "System.Single" or "System.Double"} value || !Stable(value, use)) return false;
                    var type = value.Type!.FullName;
                    if (b is LocalVariable other)
                    { if (other.Type?.FullName != type || !Stable(other, use)) return false; }
                    else if (!(b is Immediate {Value: 0} || type == "System.Single" && b is FloatLiteral || type == "System.Double" && b is DoubleLiteral)) return false;
                    if (left == null) {left = a; right = b; scalar = type; return true;}
                    return scalar == type && Same(left, a) && Same(right!, b);
                }
                int? Evaluate(IOperand operand, Instruction use, int depth)
                {
                    if (depth > 48 || cache.Count > 64) return null;
                    if (operand is Immediate {Value: 0}) return 0;
                    if (operand is Immediate {Value: 1}) return 15;
                    if (operand is not LocalVariable value || !writes.TryGetValue(value, out var defs) || defs.Length != 1) return null;
                    var definition = defs[0];
                    if (!ReferenceEquals(definition, root) && !Before(definition, use)) return null;
                    if (cache.TryGetValue(value, out var known)) return known;
                    if (!active.Add(value)) return null;
                    int? result = null;
                    if (definition.Operands is [_, var a, var b]
                        && Relations.Any(r => r.Code == definition.OpCode) && FloatingPair(a, b, definition))
                        result = Relations.Single(r => r.Code == definition.OpCode).Mask;
                    else if (value.Type?.FullName == "System.Boolean")
                    {
                        if (definition.Operands is [_, var one] && definition.OpCode is OpCode.Move or OpCode.Not)
                        {
                            var mask = Evaluate(one, definition, depth + 1);
                            if (mask != null) result = definition.OpCode == OpCode.Not ? mask ^ 15 : mask;
                        }
                        else if (definition.Operands is [_, var x, var y]
                            && definition.OpCode is OpCode.And or OpCode.Or or OpCode.Xor or OpCode.CheckEqual or OpCode.CheckNotEqual)
                        {
                            var first = Evaluate(x, definition, depth + 1); var second = Evaluate(y, definition, depth + 1);
                            if (first != null && second != null) result = definition.OpCode switch
                            {OpCode.And => first & second, OpCode.Or => first | second, OpCode.CheckEqual => (first ^ second) ^ 15, _ => first ^ second};
                        }
                    }
                    active.Remove(value);
                    if (result != null) cache[value] = result.Value;
                    return result;
                }
                var truth = Evaluate(root.Operands[0], branch, 0);
                if (truth == null || left == null || cache.Count < 2) continue;
                var relation = Relations.FirstOrDefault(r => r.Mask == truth);
                var invert = relation.Mask == 0;
                if (invert) relation = Relations.FirstOrDefault(r => r.Mask == (truth ^ 15));
                if (relation.Mask == 0) continue;
                var rhs = right is Immediate {Value: 0}
                    ? scalar == "System.Single" ? (IOperand)new FloatLiteral(0) : new DoubleLiteral(0) : right!;
                var destination = root.Operands[0];
                if (invert)
                {
                    // Keep the original condition's truth value and every use;
                    // do not invert a shared flag or change CFG successor meaning.
                    var direct = new LocalVariable("floatingCondition" + method.Locals.Count,
                        new Register(null, "floatingCondition" + method.Locals.Count), method.AppContext.SystemTypes.SystemBooleanType);
                    method.Locals.Add(direct);
                    var compare = new Instruction(root.Index, relation.Code, direct, left, rhs);
                    homes[root].Instructions.Insert(homes[root].Instructions.IndexOf(root), compare);
                    // Later complete values in the same pass may consume this
                    // shared flag; retain the new definition/dominance witness.
                    writes[direct] = [compare];
                    homes[compare] = homes[root];
                    root.OpCode = OpCode.Not; root.SetOperands(destination, direct);
                }
                else {root.OpCode = relation.Code; root.SetOperands(destination, left, rhs);}
                changed++;
                if (ReferenceEquals(root, roots[0])) break;
            }
        }
        return changed;
    }
}
