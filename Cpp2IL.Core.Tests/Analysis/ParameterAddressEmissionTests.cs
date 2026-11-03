using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using AType=AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;
using AField=AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes;
using AMethod=AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes;

namespace Cpp2IL.Core.Tests.Analysis;

public class ParameterAddressEmissionTests
{
    [TestCase("first-value")]
    [TestCase("sparse-second-value")]
    [TestCase("copied-local")]
    [TestCase("byref-second")]
    public void RecoveredGetterReadsActualStructArgumentInsteadOfDefaultLocal(string shape)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var runtime=ModuleDefinition.FromFile(typeof(float).Assembly.Location);
        t.SystemSingleType.PutExtraData("AsmResolverType",runtime.GetAllTypes().Single(x=>x.FullName=="System.Single"));
        var data=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Fixture","Data",t.SystemValueTypeType,TypeAttributes.Public|TypeAttributes.SequentialLayout);
        var field=new InjectedFieldAnalysisContext("Hidden",t.SystemSingleType,FieldAttributes.Private,data,0);data.Fields.Add(field);
        var getter=new InjectedMethodAnalysisContext(data,"get_Value",t.SystemSingleType,MethodAttributes.Public,[]);
        data.Properties.Add(new InjectedPropertyAnalysisContext("Value",t.SystemSingleType,getter,null,PropertyAttributes.None,data));
        var assembly=new AssemblyDefinition("ParameterAddress"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("ParameterAddress.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));assembly.Modules.Add(module);
        var dataDef=new TypeDefinition("Fixture","Data",AType.Public|AType.Sealed|AType.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System","ValueType"));
        var owner=new TypeDefinition("Fixture","Generated",AType.Public,module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(dataDef);module.TopLevelTypes.Add(owner);data.PutExtraData("AsmResolverType",dataDef);
        var storage=new FieldDefinition("Hidden",AField.Private,new FieldSignature(module.CorLibTypeFactory.Single));dataDef.Fields.Add(storage);field.PutExtraData("AsmResolverField",storage);
        var getterDef=new MethodDefinition("get_Value",AMethod.Public|AMethod.SpecialName,MethodSignature.CreateInstance(module.CorLibTypeFactory.Single));dataDef.Methods.Add(getterDef);
        getterDef.CilMethodBody=new CilMethodBody();getterDef.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        getterDef.CilMethodBody.Instructions.Add(CilOpCodes.Ldfld,storage);getterDef.CilMethodBody.Instructions.Add(CilOpCodes.Ret);getter.PutExtraData("AsmResolverMethod",getterDef);
        var byref=shape=="byref-second";var ordinal=shape is "sparse-second-value" or "byref-second"?1:0;
        TypeAnalysisContext inputType=byref?new ByRefTypeAnalysisContext(data):data;
        var source=new LocalVariable("v0",new(null,"incoming"),inputType){ParameterIndex=ordinal};
        var temp=new LocalVariable("v0",new(null,"temporary"),data);var result=new LocalVariable("result",new(null,"result"),t.SystemSingleType);
        var selected=shape=="copied-local"?temp:source;
        var read=new Instruction(1,OpCode.Move,result,new FieldReference(field,selected,0)){NativeReadSize=4};
        var steps=new List<Instruction>();if(shape=="copied-local")steps.Add(new(0,OpCode.Move,temp,source));steps.Add(read);steps.Add(new(2,OpCode.Return,result));
        var context=new InjectedMethodAnalysisContext(t.SystemObjectType,"Run",t.SystemSingleType,MethodAttributes.Public|MethodAttributes.Static,
            [data,byref?new ByRefTypeAnalysisContext(data):data],["outer","inner"])
        {ParameterLocals=[source],Locals=[source,temp,result],AnalysisWarnings=[],ControlFlowGraph=new(steps)};
        var code=Convert.FromHexString("001040BDC0035FD6"); // LDR S0,[X0,#16]; RET
        Assert.That(NativeValuePropertyRecovery.Prove(getter,field,code,out var width),Is.True);
        Assert.That(NativeValuePropertyRecovery.Recover(context,new Dictionary<FieldAnalysisContext,NativeValuePropertyRecovery.Contract>{{field,new(getter,width)}}),Is.EqualTo(1));
        var dataSig=dataDef.ToTypeSignature(true);
        var method=new MethodDefinition("Run",AMethod.Public|AMethod.Static,MethodSignature.CreateStatic(module.CorLibTypeFactory.Single,
            [dataSig,byref?new ByReferenceTypeSignature(dataSig):dataSig]));owner.Methods.Add(method);
        method.ParameterDefinitions.Add(new ParameterDefinition(1,"renamed_outer",0));method.ParameterDefinitions.Add(new ParameterDefinition(2,"renamed_inner",0));
        IlGenerator.GenerateIl(context,method);
        Assert.That(method.CilMethodBody!.Instructions.Any(i=>i.OpCode==CilOpCodes.Ldarga),Is.EqualTo(!byref && shape!="copied-local"));
        using var stream=new MemoryStream();module.Write(stream);var generated=Assembly.Load(stream.ToArray());
        var run=generated.GetType("Fixture.Generated")!.GetMethod("Run")!;var type=generated.GetType("Fixture.Data")!;
        object Value(float value){var instance=Activator.CreateInstance(type)!;type.GetField("Hidden",BindingFlags.NonPublic|BindingFlags.Instance)!.SetValue(instance,value);return instance;}
        object[] args=[Value(17.25f),Value(-91.5f)];
        Assert.That(run.Invoke(null,args),Is.EqualTo(ordinal==0?17.25f:-91.5f));
        Assert.That(field.Attributes&FieldAttributes.FieldAccessMask,Is.EqualTo(FieldAttributes.Private));
    }
}
