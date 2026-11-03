using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Restore public properties from inlined private value-type field reads.
// A two-instruction original boxed getter must be exactly LDR S0/D0; RET.
// No private-name/property-name convention or SDK visibility change is used.
public static class NativeValuePropertyRecovery
{
    internal sealed record Contract(MethodAnalysisContext Getter, int Width);
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,Lazy<Dictionary<FieldAnalysisContext,Contract>>> Catalogs=new();

    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph==null || !CheckedUnboxRecovery.Supports(method.AppContext))return 0;
        return Recover(method,Catalogs.GetValue(method.AppContext,a=>new(()=>Build(a))).Value);
    }

    private static Dictionary<FieldAnalysisContext,Contract> Build(ApplicationAnalysisContext app)
    {
        var entries=new Dictionary<FieldAnalysisContext,List<Contract>>();var binary=app.Binary;
        foreach(var getter in app.MethodsByAddress.Values.SelectMany(v=>v).Distinct())
        {
            if(getter.DeclaringType is not {IsValueType:true} owner || getter.UnderlyingPointer==0
                || getter.UnderlyingPointer%4!=0 || app.GetAddressOfNextFunctionStart(getter.UnderlyingPointer)!=getter.UnderlyingPointer+8
                || !binary.TryMapVirtualAddressToRaw(getter.UnderlyingPointer,out var raw) || raw<0 || raw>binary.RawLength-8)continue;
            var bytes=binary.GetRawBinaryContent().Slice((int)raw,8);
            foreach(var field in owner.Fields)
            {
                if(!Prove(getter,field,bytes,out var width))continue;
                if(!entries.TryGetValue(field,out var list))entries[field]=list=[];
                list.Add(new(getter,width));
            }
        }
        // x and xMin can both be identical proven single-field getters. All
        // candidates have the SAME field, return type and exact byte effect;
        // stable lexical choice is not an assumption about their names.
        return entries.ToDictionary(p=>p.Key,p=>p.Value.OrderBy(c=>c.Getter.Name,StringComparer.Ordinal).First());
    }

    internal static bool Prove(MethodAnalysisContext getter,FieldAnalysisContext field,ReadOnlySpan<byte> bytes,out int width)
    {
        width=0;
        if(bytes.Length!=8 || BitConverter.ToUInt32(bytes[4..])!=0xd65f03c0u
            || getter.DeclaringType is not {IsValueType:true} owner || owner.HasAnyGenericParameters()
            || owner.IsGenericInstance || getter.IsStatic || getter.IsVirtual || getter.Parameters.Count!=0
            || getter.GenericParameters.Count!=0 || getter.Visibility!=MethodAttributes.Public
            || owner.Properties.Count(p=>ReferenceEquals(p.Getter,getter))!=1
            || !ReferenceEquals(field.DeclaringType,owner) || !owner.Fields.Contains(field) || field.IsStatic
            || field.Offset<0 || (field.Attributes&FieldAttributes.FieldAccessMask)==FieldAttributes.Public
            || (field.Attributes&FieldAttributes.Literal)!=0 || !TrivialConstructorRecovery.SameType(field.FieldType,getter.ReturnType))return false;
        var size=field.FieldType.FullName switch {"System.Single"=>4,"System.Double"=>8,_=>0};
        if(size==0 || field.Offset>int.MaxValue-16)return false;
        var offset=field.Offset+16;var word=BitConverter.ToUInt32(bytes[..4]);
        var encoding=size==4?0xbd400000u:0xfd400000u;
        if((word&0xffc003ffu)!=encoding || ((word>>10)&4095)*size!=offset)return false;
        width=size;return true;
    }

    internal static int Recover(MethodAnalysisContext method,IReadOnlyDictionary<FieldAnalysisContext,Contract> catalog)
    {
        if(method.ControlFlowGraph is not {} graph)return 0;
        var changes=0;
        foreach(var instruction in graph.Instructions)
        {
            if(instruction is not {OpCode:OpCode.Move,NativeWriteSize:0,
                Operands:[LocalVariable result,FieldReference {Parent:null} field]}
                || !catalog.TryGetValue(field.Field,out var contract) || field.Offset!=field.Field.Offset
                || TrivialConstructorRecovery.SameType(method.DeclaringType,field.Field.DeclaringType))continue;
            var owner=field.Field.DeclaringType;var receiver=field.Local;
            var byref=receiver.Type is ByRefTypeAnalysisContext {ElementType:{} element} && TrivialConstructorRecovery.SameType(element,owner);
            var value=TrivialConstructorRecovery.SameType(receiver.Type,owner);
            if(!byref && !value || instruction.NativeReadSize!=contract.Width && !(value && instruction.NativeReadSize==0))continue;
            instruction.OpCode=OpCode.Call;
            instruction.SetOperands(contract.Getter,result,byref?(IOperand)receiver:new AddressOf(receiver));
            instruction.NativeReadSize=0;instruction.NativeDirectCallTarget=contract.Getter.UnderlyingPointer;
            instruction.NativeVirtualDispatch=false;changes++;
        }
        return changes;
    }
}
