using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class ConstrainedReferenceFieldTests
{
    private static InjectedTypeAnalysisContext Type(ApplicationAnalysisContext app, string name)
        => new(app.SystemTypes.SystemObjectType.DeclaringAssembly, "Test", name,
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);

    private static GenericParameterTypeAnalysisContext Parameter(InjectedTypeAnalysisContext owner,
        string name = "T", GenericParameterAttributes attributes = GenericParameterAttributes.None)
    {
        var parameter = new GenericParameterTypeAnalysisContext(name, owner.GenericParameters.Count,
            Il2CppTypeEnum.IL2CPP_TYPE_VAR, attributes, owner);
        owner.GenericParameters.Add(parameter);
        return parameter;
    }

    [TestCase(false)]
    [TestCase(true)]
    public void LoadsAndStoresRetainConstraintFieldAndReceiverIdentity(bool store)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var constraint = Type(app, "Constraint");
        var field = constraint.InjectFieldContext("Value", app.SystemTypes.SystemStringType, FieldAttributes.Public);
        field.Offset = 16;
        var owner = Type(app, "Consumer"); var parameter = Parameter(owner);
        parameter.ConstraintTypes.Add(constraint);
        var receiver = new LocalVariable("receiver", new(null, "X0"), parameter);
        var value = new LocalVariable("value", new(null, "X1"), app.SystemTypes.SystemStringType);
        var memory = new MemoryOperand(receiver, addend: 16);
        var instruction = store ? new Instruction(0, OpCode.Move, memory, value) { NativeWriteSize = 8 }
            : new Instruction(0, OpCode.Move, value, memory) { NativeReadSize = 8 };
        var method = new InjectedMethodAnalysisContext(owner, "Access", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []) { ControlFlowGraph = new([instruction, new(1, OpCode.Return)]) };
        Assert.That(MetadataResolver.ResolveFieldOffsets(method), Is.True);
        var reference = (FieldReference)instruction.Operands[store ? 0 : 1];
        Assert.That(reference.Field, Is.SameAs(field));
        Assert.That(reference.Local, Is.SameAs(receiver));
        Assert.That(receiver.Type, Is.SameAs(parameter));
        Assert.That(field.Offset, Is.EqualTo(16));
    }

    [TestCase(16, 8, true)]
    [TestCase(16, 4, false)]
    [TestCase(17, 8, false)]
    [TestCase(16, 0, false)]
    [TestCase(-1, 8, false)]
    public void OffsetAndWidthMustMatchExactly(int offset, int width, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var owner = Type(app, "Owner");
        var constraint = Type(app, "Constraint");
        constraint.InjectFieldContext("Value", app.SystemTypes.SystemObjectType, FieldAttributes.Public).Offset = 16;
        var parameter = Parameter(owner); parameter.ConstraintTypes.Add(constraint);
        Assert.That(ConstrainedReferenceFieldLayout.Find(parameter, offset, width) != null, Is.EqualTo(expected));
    }

    [TestCase(true)]
    [TestCase(false)]
    public void OpenGenericStorageNeedsAProvenReferenceArgument(bool reference)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var owner = Type(app, "Owner");
        var argument = Parameter(owner, "Payload", reference ? GenericParameterAttributes.ReferenceTypeConstraint : GenericParameterAttributes.None);
        var definition = Type(app, "Box"); var value = Parameter(definition);
        definition.InjectFieldContext("Value", value, FieldAttributes.Public);
        definition.InjectFieldContext("Next", app.SystemTypes.SystemStringType, FieldAttributes.Public);
        var constraint = new GenericInstanceTypeAnalysisContext(definition, [argument]);
        var receiver = Parameter(owner, "Receiver"); receiver.ConstraintTypes.Add(constraint);
        var field = ConstrainedReferenceFieldLayout.Find(receiver, 24, 8);
        Assert.That(field?.Name, Is.EqualTo(reference ? "Next" : null));
        if (field != null) Assert.That(field.DeclaringType, Is.SameAs(constraint));
        Assert.That(GenericInstanceFieldLayout.FindInheritedFieldAtOffset(constraint, 24, 8), Is.Null,
            "legacy lookup remains conservative for open parameters");
    }

    [TestCase("none")]
    [TestCase("interface")]
    [TestCase("value")]
    [TestCase("ambiguous")]
    [TestCase("cycle")]
    public void NonClassOrAmbiguousConstraintsCannotAuthorizeAField(string reason)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var owner = Type(app, "Owner");
        var receiver = Parameter(owner); var constraint = Type(app, "Constraint");
        constraint.InjectFieldContext("Value", app.SystemTypes.SystemObjectType, FieldAttributes.Public).Offset = 16;
        if (reason == "interface") constraint.Attributes = TypeAttributes.Public | TypeAttributes.Interface | TypeAttributes.Abstract;
        if (reason == "value") receiver.Attributes = GenericParameterAttributes.NotNullableValueTypeConstraint;
        if (reason != "none") receiver.ConstraintTypes.Add(constraint);
        if (reason == "ambiguous") receiver.ConstraintTypes.Add(Type(app, "Other"));
        if (reason == "cycle") receiver.ConstraintTypes.Add(receiver);
        Assert.That(ConstrainedReferenceFieldLayout.Find(receiver, 16, 8), Is.Null);
    }
}
