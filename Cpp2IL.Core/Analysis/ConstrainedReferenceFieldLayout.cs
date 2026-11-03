using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Class constraints prove inherited field ownership, not arbitrary value sizes.
// Never change the receiver type or infer a field from its desired result type.
public static class ConstrainedReferenceFieldLayout
{
    private static TypeAnalysisContext? ClassConstraint(GenericParameterTypeAnalysisContext parameter,
        HashSet<GenericParameterTypeAnalysisContext> active)
    {
        if (active.Count >= 32 || !active.Add(parameter)
            || (parameter.Attributes & GenericParameterAttributes.NotNullableValueTypeConstraint) != 0)
            return null;
        try
        {
            TypeAnalysisContext? result = null;
            foreach (var constraint in parameter.ConstraintTypes)
            {
                var candidate = constraint is GenericParameterTypeAnalysisContext parent
                    ? ClassConstraint(parent, active) : constraint;
                if (candidate == null)
                {
                    if (constraint is GenericParameterTypeAnalysisContext) return null;
                    continue;
                }
                if (candidate.IsValueType || (candidate.Attributes & TypeAttributes.Interface) != 0
                    || candidate.FullName is "System.Object" or "System.ValueType" or "System.Enum")
                    continue;
                if (result != null && !ReferenceEquals(result, candidate)) return null;
                result = candidate;
            }
            return result;
        }
        finally { active.Remove(parameter); }
    }

    internal static bool IsReferenceStorage(TypeAnalysisContext type)
    {
        if (type is GenericParameterTypeAnalysisContext parameter)
            return (parameter.Attributes & GenericParameterAttributes.NotNullableValueTypeConstraint) == 0
                && ((parameter.Attributes & GenericParameterAttributes.ReferenceTypeConstraint) != 0
                    || ClassConstraint(parameter, []) != null);
        return !type.IsValueType && type is not PointerTypeAnalysisContext and not ByRefTypeAnalysisContext;
    }

    public static FieldAnalysisContext? Find(GenericParameterTypeAnalysisContext receiver, long offset, int width)
    {
        if (offset < 0 || offset > int.MaxValue || width is not (1 or 2 or 4 or 8)
            || ClassConstraint(receiver, []) is not {} owner)
            return null;
        var fields = GenericInstanceFieldLayout.InheritedFields(owner, allowOpenReferenceFields: true);
        var matches = fields?.Where(f => f.Offset == offset && f.Size == width).ToArray();
        return matches is { Length: 1 } ? matches[0].Field : null;
    }
}
