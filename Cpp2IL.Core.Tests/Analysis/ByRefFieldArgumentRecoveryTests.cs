using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ByRefFieldArgumentRecoveryTests
{
    [TestCase("static-void", true)]
    [TestCase("instance-void", true)]
    [TestCase("returning-call", true)]
    [TestCase("struct-byref", true)]
    [TestCase("single", true)]
    [TestCase("narrow-add", false)]
    [TestCase("unknown-add-width", false)]
    [TestCase("padding", false)]
    [TestCase("negative-offset", false)]
    [TestCase("overlap", false)]
    [TestCase("same-width-wrong-type", false)]
    [TestCase("readonly", false)]
    [TestCase("root-reassigned", false)]
    [TestCase("pointer-reassigned", false)]
    [TestCase("root-after-address", false)]
    [TestCase("address-after-call", false)]
    [TestCase("implicit-root-clobber", false)]
    [TestCase("implicit-pointer-clobber", false)]
    [TestCase("unknown-root", false)]
    [TestCase("runtime-root", false)]
    [TestCase("undefined-root", false)]
    [TestCase("by-value", false)]
    [TestCase("reference-element", false)]
    [TestCase("string-field", true)]
    [TestCase("object-field", true)]
    [TestCase("array-field", true)]
    [TestCase("reference-padding", false)]
    [TestCase("reference-overlap", false)]
    [TestCase("reference-readonly", false)]
    [TestCase("reference-wrong-type", false)]
    [TestCase("pointer-element", false)]
    [TestCase("reference-root-byref", false)]
    public void ExactFieldAddressesKeepRefAliasAndCallOrder(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var t = app.SystemTypes;
        var owner = new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly, "Fixture", "Holder",
            shape == "struct-byref" ? t.SystemValueTypeType : t.SystemObjectType, TypeAttributes.Public);
        TypeAnalysisContext element = shape == "single" ? t.SystemSingleType
            : shape is "string-field" or "reference-padding" or "reference-overlap" or "reference-readonly" or "reference-wrong-type" ? t.SystemStringType
            : shape == "object-field" ? t.SystemObjectType
            : shape == "array-field" ? new ArrayTypeAnalysisContext(t.SystemStringType, 1) : t.SystemInt32Type;
        var field = new InjectedFieldAnalysisContext("Value", shape == "same-width-wrong-type" ? t.SystemSingleType : element,
            FieldAttributes.Public | (shape is "readonly" or "reference-readonly" ? FieldAttributes.InitOnly : 0), owner, 24);
        owner.Fields.Add(field);
        if (shape is "overlap" or "reference-overlap") owner.Fields.Add(new InjectedFieldAnalysisContext("Alias", element, FieldAttributes.Public, owner, 24));
        TypeAnalysisContext rootType = shape == "struct-byref" ? new ByRefTypeAnalysisContext(owner) : owner;
        if (shape == "runtime-root") rootType = new RuntimeClassTypeAnalysisContext(owner, owner.DeclaringAssembly);
        if (shape == "reference-root-byref") rootType = new ByRefTypeAnalysisContext(owner);
        var root = new LocalVariable("root", new(null, "root"), shape == "unknown-root" ? null : rootType);
        var other = new LocalVariable("other", new(null, "other"), rootType);
        var pointer = new LocalVariable("address", new(null, "address"));
        var receiver = new LocalVariable("receiver", new(null, "receiver"), t.SystemObjectType);
        var result = new LocalVariable("result", new(null, "result"), t.SystemInt32Type);
        var address = new Instruction(0, OpCode.Add, pointer, root, new Immediate(shape is "padding" or "reference-padding" ? 25 : shape == "negative-offset" ? -1 : 24))
            {NativeArithmeticSize = shape == "narrow-add" ? 4 : shape == "unknown-add-width" ? 0 : 8};
        var isStatic = shape != "instance-void";
        var parameter = shape == "by-value" ? element : new ByRefTypeAnalysisContext(
            shape is "reference-element" or "reference-wrong-type" ? t.SystemObjectType
            : shape == "pointer-element" ? element.MakePointerType() : element);
        var target = new InjectedMethodAnalysisContext(t.SystemObjectType, "Mutate", shape == "returning-call" ? t.SystemInt32Type : t.SystemVoidType,
            MethodAttributes.Public | (isStatic ? MethodAttributes.Static : 0), [parameter]);
        var operands = new List<IOperand> {target};
        if (shape == "returning-call") operands.Add(result);
        if (!isStatic) operands.Add(receiver);
        operands.Add(pointer);
        var call = new Instruction(1, shape == "returning-call" ? OpCode.Call : OpCode.CallVoid, operands);
        var index = operands.Count - 1;
        var instructions = new List<Instruction> {address, call, new(2, OpCode.Return)};
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Caller", t.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, [])
            {ParameterLocals = [root, other, receiver], Locals = [root, other, receiver, pointer, result]};
        if (shape == "undefined-root") method.ParameterLocals.Remove(root);
        if (shape == "root-reassigned") instructions.Insert(1, new(3, OpCode.Move, root, other));
        if (shape == "pointer-reassigned") instructions.Insert(1, new(3, OpCode.Move, pointer, new Immediate(0)));
        if (shape == "root-after-address") { method.ParameterLocals.Remove(root); instructions.Insert(1, new(3, OpCode.Move, root, other)); }
        if (shape == "address-after-call") { instructions.Remove(address); instructions.Insert(1, address); }
        if (shape is "implicit-root-clobber" or "implicit-pointer-clobber")
            instructions.Insert(1, new Instruction(3, OpCode.CallVoid, new StringLiteral("opaque"))
                {ImplicitDefinition = shape == "implicit-root-clobber" ? root.Register : pointer.Register});
        method.ControlFlowGraph = new(instructions);
        var before = method.ControlFlowGraph.Instructions.ToArray();
        var original = call.Operands[index];
        Assert.That(ByRefFieldArgumentRecovery.Run(method), Is.EqualTo(expected ? 1 : 0));
        Assert.That(method.ControlFlowGraph.Instructions, Is.EqualTo(before), "Do not insert/reorder calls or field reads.");
        if (!expected) { Assert.That(call.Operands[index], Is.SameAs(original)); return; }
        Assert.That(call.Operands[index], Is.TypeOf<AddressOf>());
        var recovered = (FieldReference)((AddressOf)call.Operands[index]).Target;
        Assert.That(recovered.Field, Is.SameAs(field)); Assert.That(recovered.Local, Is.SameAs(root));
        if (shape is "string-field" or "object-field" or "array-field")
            Assert.That(NestedFieldAccess.Find(owner, root, 24, 8, method), Is.Null,
                "Address recovery must not broaden ordinary memory-read interpretation.");
        // A write through the ref argument must affect the original field, not
        // a temporary local. Both forms select the same concrete storage cell.
        var values = new Dictionary<long, long> {{1024 + 24, 7}};
        long rawAddress = 1024 + ((Immediate)address.Operands[2]).Value;
        long recoveredAddress = 1024 + recovered.Offset;
        Assert.That(recoveredAddress, Is.EqualTo(rawAddress));
        values[recoveredAddress] = 19;
        Assert.That(values[rawAddress], Is.EqualTo(19));
        Assert.That(ByRefFieldArgumentRecovery.Run(method), Is.Zero);
    }
}
