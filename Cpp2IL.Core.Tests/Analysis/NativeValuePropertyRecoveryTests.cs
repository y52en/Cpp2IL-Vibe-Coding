using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeValuePropertyRecoveryTests
{
    private static (InjectedTypeAnalysisContext Owner,InjectedFieldAnalysisContext Field,InjectedMethodAnalysisContext Getter) Fixture(string shape)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Fixture","Value",shape=="class"?t.SystemObjectType:t.SystemValueTypeType,TypeAttributes.Public);
        var scalar=shape=="double"?t.SystemDoubleType:t.SystemSingleType;
        var field=new InjectedFieldAnalysisContext("private_storage",scalar,shape=="public-field"?FieldAttributes.Public:FieldAttributes.Private,owner,0);owner.Fields.Add(field);
        var attributes=shape=="private-getter"?MethodAttributes.Private:MethodAttributes.Public;
        if(shape=="static")attributes|=MethodAttributes.Static;
        if(shape=="virtual")attributes|=MethodAttributes.Virtual;
        var getter=new InjectedMethodAnalysisContext(owner,"get_ArbitraryPublicName",scalar,attributes,shape=="parameter"?[t.SystemInt32Type]:[]);
        if(shape!="not-property")owner.Properties.Add(new InjectedPropertyAnalysisContext("ArbitraryPublicName",scalar,getter,null,PropertyAttributes.None,owner));
        return(owner,field,getter);
    }

    private static byte[] Code(int width=4,int offset=16)
    {
        var bytes=new byte[8];BitConverter.GetBytes((width==4?0xbd400000u:0xfd400000u)|((uint)(offset/width)<<10)).CopyTo(bytes,0);
        BitConverter.GetBytes(0xd65f03c0u).CopyTo(bytes,4);return bytes;
    }

    [TestCase("single",true)]
    [TestCase("double",true)]
    [TestCase("class",false)]
    [TestCase("public-field",false)]
    [TestCase("private-getter",false)]
    [TestCase("static",false)]
    [TestCase("virtual",false)]
    [TestCase("parameter",false)]
    [TestCase("not-property",false)]
    [TestCase("wrong-offset",false)]
    [TestCase("unboxed-offset",false)]
    [TestCase("extra-instruction",false)]
    [TestCase("not-return",false)]
    public void OnlyExactPublicBoxedPropertyLeafProvesPrivateValueField(string shape,bool expected)
    {
        var f=Fixture(shape);var width=shape=="double"?8:4;
        var bytes=Code(width,shape=="wrong-offset"?20:shape=="unboxed-offset"?0:16);
        if(shape=="extra-instruction")bytes=bytes.Concat(new byte[4]).ToArray();
        if(shape=="not-return")bytes[4]=0;
        var attributes=f.Field.Attributes;
        Assert.That(NativeValuePropertyRecovery.Prove(f.Getter,f.Field,bytes,out var actual),Is.EqualTo(expected));
        if(expected)Assert.That(actual,Is.EqualTo(width));
        Assert.That(f.Field.Attributes,Is.EqualTo(attributes),"Never widen backing-field visibility.");
    }

    [TestCase("value",true)]
    [TestCase("value-lane",true)]
    [TestCase("byref",true)]
    [TestCase("byref-unknown-width",false)]
    [TestCase("partial",false)]
    [TestCase("different-type",false)]
    [TestCase("own-field",false)]
    [TestCase("wrong-offset",false)]
    public void GetterRunsAtTheSameReadWithoutMovingOrCopyingOtherStorage(string shape,bool expected)
    {
        var f=Fixture("single");var t=f.Owner.AppContext.SystemTypes;
        Assert.That(NativeValuePropertyRecovery.Prove(f.Getter,f.Field,Code(),out var width),Is.True);
        var byref=shape.StartsWith("byref");
        TypeAnalysisContext type=byref?new ByRefTypeAnalysisContext(f.Owner):shape=="different-type"?t.SystemObjectType:f.Owner;
        var source=new LocalVariable("source",new(null,"source"),type);var result=new LocalVariable("result",new(null,"result"),t.SystemSingleType);
        var field=new FieldReference(f.Field,source,shape=="wrong-offset"?4:0);
        var read=new Instruction(0,OpCode.Move,result,field){NativeReadSize=shape is "value-lane" or "byref-unknown-width"?0:shape=="partial"?2:4};
        var method=new InjectedMethodAnalysisContext(shape=="own-field"?f.Owner:t.SystemObjectType,"Caller",t.SystemSingleType,MethodAttributes.Public|MethodAttributes.Static,[])
        {Locals=[source,result],ParameterLocals=[source],ControlFlowGraph=new([read,new(1,OpCode.Return,result)])};
        var before=method.ControlFlowGraph.Instructions.ToArray();
        var catalog=new Dictionary<FieldAnalysisContext,NativeValuePropertyRecovery.Contract>{{f.Field,new(f.Getter,width)}};
        Assert.That(NativeValuePropertyRecovery.Recover(method,catalog),Is.EqualTo(expected?1:0));
        Assert.That(method.ControlFlowGraph.Instructions,Is.EqualTo(before));
        if(!expected){Assert.That(read.OpCode,Is.EqualTo(OpCode.Move));Assert.That(read.Operands[1],Is.SameAs(field));return;}
        Assert.That(read.OpCode,Is.EqualTo(OpCode.Call));Assert.That(read.Operands[0],Is.SameAs(f.Getter));
        if(byref)Assert.That(read.Operands[2],Is.SameAs(source));
        else Assert.That(((AddressOf)read.Operands[2]).Target,Is.SameAs(source));
        Assert.That(f.Field.Attributes&FieldAttributes.FieldAccessMask,Is.EqualTo(FieldAttributes.Private));
        Assert.That(NativeValuePropertyRecovery.Recover(method,catalog),Is.Zero);
    }
}
