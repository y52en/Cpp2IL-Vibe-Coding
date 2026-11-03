using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

// ADD object, exact field offset is an address, not a field value or a local
// temporary. Recover only known ref/out parameters and unambiguous complete
// metadata fields. Keep the native address computation and original call order.
public static class ByRefFieldArgumentRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not {} graph || method.AppContext.Binary.PointerSizeBytes != 8) return 0;
        var instructions = graph.Instructions.ToArray();
        if (!instructions.Any(i => i.OpCode == OpCode.Add && i.NativeArithmeticSize == 8)) return 0;
        var writes = instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).ToDictionary(g => g.Key, g => g.ToArray());
        var dominance = new DominatorInfo(graph);
        bool Before(Instruction definition, Instruction use)
        {
            var a = graph.Blocks.Single(b => b.Instructions.Contains(definition));
            var b = graph.Blocks.Single(b => b.Instructions.Contains(use));
            return ReferenceEquals(a, b) ? a.Instructions.IndexOf(definition) < a.Instructions.IndexOf(use) : dominance.Dominates(a, b);
        }
        var changes = 0;
        foreach (var call in instructions)
        {
            if (call.OpCode is not (OpCode.Call or OpCode.CallVoid)
                || call.Operands.FirstOrDefault() is not MethodAnalysisContext callee) continue;
            var first = (call.OpCode == OpCode.CallVoid ? 1 : 2) + (callee.IsStatic ? 0 : 1);
            for (var parameter = 0; parameter < callee.Parameters.Count && first + parameter < call.Operands.Count; parameter++)
            {
                if (callee.Parameters[parameter].ParameterType is not ByRefTypeAnalysisContext {ElementType: {} element}
                    || element.HasAnyGenericParameters()
                    || call.Operands[first + parameter] is not LocalVariable pointer
                    || !writes.TryGetValue(pointer, out var addressWrites) || addressWrites.Length != 1
                    || addressWrites[0] is not {OpCode: OpCode.Add, NativeArithmeticSize: 8,
                        Operands: [_, LocalVariable {Type: {} rootType} root, Immediate {Value: >= 0} offset] } address
                    || !Before(address, call)) continue;
                var owner = rootType is ByRefTypeAnalysisContext {ElementType: {IsValueType: true} value} ? value : rootType;
                if (owner.HasAnyGenericParameters()
                    || (ReferenceEquals(owner, rootType) && (owner.IsValueType || owner.Type is not
                        (Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST or Il2CppTypeEnum.IL2CPP_TYPE_STRING)))) continue;
                if (instructions.Any(i => i.ImplicitDefinition != null
                    && (Equals(i.ImplicitDefinition, root.Register) || Equals(i.ImplicitDefinition, pointer.Register)))) continue;
                if (writes.TryGetValue(root, out var rootWrites))
                {
                    if (rootWrites.Length != 1 || method.ParameterLocals.Contains(root) || !Before(rootWrites[0], address)) continue;
                }
                else if (!method.ParameterLocals.Contains(root)) continue;
                var referenceSlot = !element.IsValueType && element.Type is
                    Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_STRING or Il2CppTypeEnum.IL2CPP_TYPE_OBJECT
                    or Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY or Il2CppTypeEnum.IL2CPP_TYPE_ARRAY or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST;
                var size = element.IsValueType ? TypeSizes.UnboxedSize(element, 8) : referenceSlot ? 8 : 0;
                if (size <= 0 || size > int.MaxValue) continue;
                var field = NestedFieldAccess.FindAddress(owner, root, offset.Value, (int)size, method);
                if (field == null || !ReferenceEquals(field.Field.FieldType, element)) continue;
                var writable = true;
                for (var part = field; part != null; part = part.Parent)
                    writable &= (part.Field.Attributes & FieldAttributes.InitOnly) == 0;
                if (!writable) continue;
                call.SetOperand(first + parameter, new AddressOf(field));
                changes++;
            }
        }
        return changes;
    }
}
