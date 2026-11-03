using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using AsmTypeAttributes = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;
using AsmMethodAttributes = AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes;

namespace Cpp2IL.Core.Tests;

public class FloatingComparisonEmissionTests
{
    [TestCase(OpCode.CheckEqual, false, false)]
    [TestCase(OpCode.CheckEqual, false, true)]
    [TestCase(OpCode.CheckEqual, true, false)]
    [TestCase(OpCode.CheckEqual, true, true)]
    [TestCase(OpCode.CheckNotEqual, false, false)]
    [TestCase(OpCode.CheckNotEqual, false, true)]
    [TestCase(OpCode.CheckNotEqual, true, false)]
    [TestCase(OpCode.CheckNotEqual, true, true)]
    [TestCase(OpCode.CheckLess, false, false)]
    [TestCase(OpCode.CheckLess, false, true)]
    [TestCase(OpCode.CheckLess, true, false)]
    [TestCase(OpCode.CheckLess, true, true)]
    [TestCase(OpCode.CheckGreater, false, false)]
    [TestCase(OpCode.CheckGreater, false, true)]
    [TestCase(OpCode.CheckGreater, true, false)]
    [TestCase(OpCode.CheckGreater, true, true)]
    [TestCase(OpCode.CheckLessOrEqual, false, false)]
    [TestCase(OpCode.CheckLessOrEqual, false, true)]
    [TestCase(OpCode.CheckLessOrEqual, true, false)]
    [TestCase(OpCode.CheckLessOrEqual, true, true)]
    [TestCase(OpCode.CheckGreaterOrEqual, false, false)]
    [TestCase(OpCode.CheckGreaterOrEqual, false, true)]
    [TestCase(OpCode.CheckGreaterOrEqual, true, false)]
    [TestCase(OpCode.CheckGreaterOrEqual, true, true)]
    public void ExecutedFloatingIlPreservesOrderedNaNComparisons(OpCode opcode, bool wide, bool invert)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var input=wide ? app.SystemTypes.SystemDoubleType : app.SystemTypes.SystemSingleType;
        var left=new LocalVariable("left",new Register(null,"X0"),input);
        var right=new LocalVariable("right",new Register(null,"X1"),input);
        var result=new LocalVariable("result",new Register(null,"C"),app.SystemTypes.SystemBooleanType);
        var caller=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Compare",app.SystemTypes.SystemBooleanType,MethodAttributes.Public|MethodAttributes.Static,[input,input]);
        caller.ControlFlowGraph=new([new Instruction(0,opcode,result,left,right){UnsignedComparison=false},new(1,OpCode.Return,result)]);
        caller.Locals=[left,right,result];caller.ParameterLocals=[left,right];caller.AnalysisWarnings=[];
        var assembly=new AssemblyDefinition("FloatingTest"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("FloatingTest.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));assembly.Modules.Add(module);
        var type=new TypeDefinition("Test","Generated",AsmTypeAttributes.Public,module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(type);
        var scalar=wide ? module.CorLibTypeFactory.Double : module.CorLibTypeFactory.Single;
        var method=new MethodDefinition("Compare",AsmMethodAttributes.Public|AsmMethodAttributes.Static,MethodSignature.CreateStatic(module.CorLibTypeFactory.Boolean,[scalar,scalar]));type.Methods.Add(method);
        // Exercise the actual instruction emitter and execute its output.
        // The tiny fixture supplies CLR primitive signatures directly instead
        // of pretending the game's complete corlib was exported into this DLL.
        method.ParameterDefinitions.Add(new ParameterDefinition(1,"left",0));
        method.ParameterDefinitions.Add(new ParameterDefinition(2,"right",0));
        method.CilMethodBody=new CilMethodBody(){InitializeLocals=true};
        var booleanLocal=new CilLocalVariable(module.CorLibTypeFactory.Boolean);
        method.CilMethodBody.LocalVariables.Add(booleanLocal);
        var locals=new Dictionary<LocalVariable,CilLocalVariable>{{result,booleanLocal}};
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        emit.Invoke(null,[new Instruction(0,opcode,result,left,right){UnsignedComparison=false},caller,method,locals,method]);
        if(invert) // Exercise both the relation and its use under boolean negation.
            emit.Invoke(null,[new Instruction(2,OpCode.Not,result,result),caller,method,locals,method]);
        emit.Invoke(null,[new Instruction(3,OpCode.Return,result),caller,method,locals,method]);
        if(opcode is OpCode.CheckLessOrEqual or OpCode.CheckGreaterOrEqual)
            Assert.That(method.CilMethodBody.Instructions.Any(i=>i.OpCode==
                (opcode==OpCode.CheckLessOrEqual?CilOpCodes.Cgt_Un:CilOpCodes.Clt_Un)),Is.True);
        using var stream=new MemoryStream();module.Write(stream);
        var generated=System.Reflection.Assembly.Load(stream.ToArray()).GetType("Test.Generated")!.GetMethod("Compare")!;
        var samples=new[]{double.NaN,double.NegativeInfinity,-2d,-0d,0d,(double)float.Epsilon,2d,double.PositiveInfinity};
        foreach(var a in samples)
        foreach(var b in samples)
        {
            double x=wide?a:(float)a;double y=wide?b:(float)b;
            var expected=opcode switch
            {OpCode.CheckEqual=>x==y,OpCode.CheckNotEqual=>x!=y,OpCode.CheckLess=>x<y,
             OpCode.CheckGreater=>x>y,OpCode.CheckLessOrEqual=>x<=y,_=>x>=y};
            object px=wide?(object)x:(float)x;object py=wide?(object)y:(float)y;
            Assert.That(generated.Invoke(null,[px,py]),Is.EqualTo(invert?!expected:expected),$"{opcode} ({x},{y}) negate={invert}");
        }
    }

}
