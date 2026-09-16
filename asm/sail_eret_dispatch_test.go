package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"regexp"
	"strings"
	"testing"
)

const (
	eretEncodingName = "ERET_64E_branch_reg"
	eretWord         = uint32(0xd69f03e0)
)

var sailERETDecodeHeader = regexp.MustCompile(
	`(?m)^function clause decode64 \(\(0b11010110100111110000001111100000 as op_code\) if SEE < 1726\) = \{`,
)

// TestSailArmPlainERETDispatchSource ties Oak's exact plain-ERET word and
// generated pure projection to the pinned official Arm decoder and execution
// call route. It proves neither successful dynamic execution nor the effects
// of SynchronizeContext, PSTATE restoration, traps, or the eventual branch.
func TestSailArmPlainERETDispatchSource(t *testing.T) {
	modelDir := filepath.Dir(sailArmModel)
	decodeBytes, err := os.ReadFile(sailArmModel)
	if err != nil {
		requireOracle(t, "sail-arm AArch64 decoder not present: "+err.Error())
	}
	aarch64Bytes, err := os.ReadFile(filepath.Join(modelDir, "aarch64.sail"))
	if err != nil {
		requireOracle(t, "sail-arm aarch64 model not present: "+err.Error())
	}
	decode := string(decodeBytes)
	aarch64 := string(aarch64Bytes)

	classes, err := parseSailDecodeClasses(sailArmModel)
	if err != nil {
		t.Fatal(err)
	}
	classMatches := 0
	for _, class := range classes {
		if class.mask == 0xffffffff && class.value == eretWord &&
			class.fn == "branch_unconditional_eret" {
			classMatches++
		}
	}
	if classMatches != 1 {
		t.Fatalf("plain ERET decode class count = %d, want 1", classMatches)
	}

	officialClause, _, err := sailUniqueArm(decode, sailERETDecodeHeader)
	if err != nil {
		t.Fatal(err)
	}
	wantOfficialClause := "SEE=1726;" +
		"op4:bits(5)=op_code[4..0];" +
		"Rn:bits(5)=op_code[9..5];" +
		"M:bits(1)=[op_code[10]];" +
		"A:bits(1)=[op_code[11]];" +
		"op2:bits(5)=op_code[20..16];" +
		"branch_unconditional_eret_decode(op4,Rn,M,A,op2)"
	if compact := strings.Join(strings.Fields(officialClause), ""); compact != wantOfficialClause {
		t.Fatalf("official plain ERET decode clause changed:\n--- have\n%s\n--- want\n%s",
			compact, wantOfficialClause)
	}

	decodeBody, err := sailFunctionBody(aarch64, "branch_unconditional_eret_decode")
	if err != nil {
		t.Fatal(err)
	}
	wantDecodeBody := "__unconditional=true;" +
		"ifPSTATE.EL==EL0then{throw(Error_Undefined())};" +
		"letpac=A==0b1;" +
		"letuse_key_a=M==0b0;" +
		"if~(pac)&op4!=0b00000then{throw(Error_Undefined())}else" +
		"{ifpac&(~(HavePACExt())|op4!=0b11111)then{throw(Error_Undefined())}};" +
		"ifRn!=0b11111then{throw(Error_Undefined())};" +
		"__PostDecode();" +
		"branch_unconditional_eret(pac,use_key_a)"
	if compact := strings.Join(strings.Fields(decodeBody), ""); compact != wantDecodeBody {
		t.Fatalf("official plain ERET decode body changed:\n--- have\n%s\n--- want\n%s",
			compact, wantDecodeBody)
	}

	executionBody, err := sailFunctionBody(aarch64, "branch_unconditional_eret")
	if err != nil {
		t.Fatal(err)
	}
	wantExecutionBody := "AArch64_CheckForERetTrap(pac,use_key_a);" +
		"target:bits(64)=ELR();" +
		"ifpacthen{ifuse_key_athen{target=AuthIA(ELR(),SP())}else" +
		"{target=AuthIB(ELR(),SP())}};" +
		"AArch64_ExceptionReturn(target,SPSR())"
	if compact := strings.Join(strings.Fields(executionBody), ""); compact != wantExecutionBody {
		t.Fatalf("official plain ERET execution route changed:\n--- have\n%s\n--- want\n%s",
			compact, wantExecutionBody)
	}

	trapBody, err := sailFunctionBody(aarch64, "AArch64_CheckForERetTrap")
	if err != nil {
		t.Fatal(err)
	}
	wantTrapPrefix := "letroute_to_el2=((HaveNVExt()&EL2Enabled())&" +
		"PSTATE.EL==EL1)&[HCR_EL2[42]]==0b1;"
	if compact := strings.Join(strings.Fields(trapBody), ""); !strings.HasPrefix(compact, wantTrapPrefix) || strings.Count(compact, wantTrapPrefix) != 1 {
		t.Fatalf("official dedicated ERET trap predicate changed: %q", trapBody)
	}
	trapArm, _, err := sailUniqueArm(trapBody,
		regexp.MustCompile(`(?m)^\s*if route_to_el2 then \{`))
	if err != nil {
		t.Fatal(err)
	}
	const takeERetTrap = "AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)"
	if strings.Count(trapBody, takeERetTrap) != 1 || strings.Count(trapArm, takeERetTrap) != 1 {
		t.Fatalf("official ERET trap exception is not uniquely guarded by route_to_el2")
	}

	elrBody, _, err := sailUniqueArm(aarch64,
		regexp.MustCompile(`(?m)^function aget_ELR__0 el = \{`))
	if err != nil {
		t.Fatal(err)
	}
	wantELRBody := "r:bits(64)=undefined:bits(64);matchel{" +
		"?if?==EL1=>{r=ELR_EL1}," +
		"?if?==EL2=>{r=ELR_EL2}," +
		"?if?==EL3=>{r=ELR_EL3}," +
		"_=>{Unreachable()}};r"
	if compact := strings.Join(strings.Fields(elrBody), ""); compact != wantELRBody {
		t.Fatalf("official ELR bank selector changed:\n--- have\n%s\n--- want\n%s",
			compact, wantELRBody)
	}
	elrEL2Body, _, err := sailUniqueArm(elrBody,
		regexp.MustCompile(`(?m)^\s*\? if \? == EL2 => \{`))
	if err != nil {
		t.Fatal(err)
	}
	if compact := strings.Join(strings.Fields(elrEL2Body), ""); compact != "r=ELR_EL2" {
		t.Fatalf("official ELR(EL2) selector changed: %q", elrEL2Body)
	}
	elrCurrentBody, err := sailFunctionBody(aarch64, "aget_ELR__1")
	if err != nil {
		t.Fatal(err)
	}
	if compact := strings.Join(strings.Fields(elrCurrentBody), ""); compact != "assert(PSTATE.EL!=EL0);ELR(PSTATE.EL)" {
		t.Fatalf("official current-EL ELR selector changed: %q", elrCurrentBody)
	}
	const elrOverload = "overload ELR = {aget_ELR__0, aget_ELR__1}"
	if strings.Count(aarch64, elrOverload) != 1 {
		t.Fatalf("official ELR overload declaration count changed")
	}
	spsrBody, err := sailFunctionBody(aarch64, "aget_SPSR")
	if err != nil {
		t.Fatal(err)
	}
	wantSPSRBody := "result:bits(32)=undefined:bits(32);" +
		"ifUsingAArch32()then{matchPSTATE.M{" +
		"?if?==M32_FIQ=>{result=SPSR_fiq}," +
		"?if?==M32_IRQ=>{result=SPSR_irq}," +
		"?if?==M32_Svc=>{result=get_SPSR_svc()}," +
		"?if?==M32_Monitor=>{result=get_SPSR_mon()}," +
		"?if?==M32_Abort=>{result=SPSR_abt}," +
		"?if?==M32_Hyp=>{result=get_SPSR_hyp()}," +
		"?if?==M32_Undef=>{result=SPSR_und}," +
		"_=>{Unreachable()}}}else{matchPSTATE.EL{" +
		"?if?==EL1=>{result=SPSR_EL1}," +
		"?if?==EL2=>{result=SPSR_EL2}," +
		"?if?==EL3=>{result=SPSR_EL3}," +
		"_=>{Unreachable()}}};result"
	if compact := strings.Join(strings.Fields(spsrBody), ""); compact != wantSPSRBody {
		t.Fatalf("official current-EL SPSR selector changed:\n--- have\n%s\n--- want\n%s",
			compact, wantSPSRBody)
	}
	spsrEL2Body, _, err := sailUniqueArm(spsrBody,
		regexp.MustCompile(`(?m)^\s*\? if \? == EL2 => \{`))
	if err != nil {
		t.Fatal(err)
	}
	if compact := strings.Join(strings.Fields(spsrEL2Body), ""); compact != "result=SPSR_EL2" {
		t.Fatalf("official SPSR(EL2) selector changed: %q", spsrEL2Body)
	}

	exceptionReturnBody, err := sailFunctionBody(aarch64, "AArch64_ExceptionReturn")
	if err != nil {
		t.Fatal(err)
	}
	requireUniqueFragmentsInOrder(t, exceptionReturnBody,
		"SynchronizeContext();",
		"SetPSTATEFromPSR(spsr);",
		"ClearExclusiveLocal(ProcessorID());",
		"SendEventLocal();",
		"new_pc = AArch64_BranchAddr(new_pc)",
		"BranchToAddr(new_pc, BranchType_ERET)")

	projectionBytes, err := os.ReadFile(filepath.Join("..", "spec", "sail", "arm_primitives.sail"))
	if err != nil {
		t.Fatal(err)
	}
	projection := string(projectionBytes)
	projectionDecode, err := sailFunctionBody(projection, "decode64_plain_eret_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantProjectionDecode := "letop4:bits(5)=slice(op_code,0,5);" +
		"letRn:bits(5)=slice(op_code,5,5);" +
		"letM:bits(1)=slice(op_code,10,1);" +
		"letA:bits(1)=slice(op_code,11,1);" +
		"letop2:bits(5)=slice(op_code,16,5);" +
		"letpac:bool=A==0b1;" +
		"letuse_key_a:bool=M==0b0;" +
		"letencoding_valid:bool=op_code==0xD69F03E0;" +
		"letpre_postdecode_checks_pass:bool=encoding_valid&~(at_el0)&~(pac)&" +
		"op4==0b00000&Rn==0b11111;" +
		"struct{encoding_valid=encoding_valid,pre_postdecode_checks_pass=pre_postdecode_checks_pass," +
		"target=ExceptionReturnExecutionTarget_ERET,op4=op4,Rn=Rn,M=M,A=A," +
		"op2=op2,pac=pac,use_key_a=use_key_a}"
	if compact := strings.Join(strings.Fields(projectionDecode), ""); compact != wantProjectionDecode {
		t.Fatalf("local plain ERET decode projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantProjectionDecode)
	}
	projectionTrap, err := sailFunctionBody(projection, "eret_nv_trap_route_pure")
	if err != nil {
		t.Fatal(err)
	}
	if compact := strings.Join(strings.Fields(projectionTrap), ""); compact != "((have_nv_ext&el2_enabled)&at_el1)&hcr_nv" {
		t.Fatalf("local dedicated ERET trap projection changed: %q", projectionTrap)
	}
	projectionInputs, err := sailFunctionBody(projection, "aarch64_plain_eret_at_el2_inputs_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantProjectionInputs := "lethcr_nv:bool=state.hcr_el2[42]==bitone;" +
		"struct{dedicated_nv_trap=eret_nv_trap_route_pure(" +
		"have_nv_ext,el2_enabled,false,hcr_nv),target=state.elr_el2," +
		"spsr=state.spsr_el2}"
	if compact := strings.Join(strings.Fields(projectionInputs), ""); compact != wantProjectionInputs {
		t.Fatalf("local EL2 ERET-input projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantProjectionInputs)
	}

	var generated *isaEncoding
	for index := range isaEncodings {
		if isaEncodings[index].Name == eretEncodingName {
			generated = &isaEncodings[index]
			break
		}
	}
	if generated == nil {
		t.Fatalf("generated AArch64 table lacks %s", eretEncodingName)
	}
	wantFields := []isaField{
		{Name: "opc", Hi: 24, Width: 4},
		{Name: "op2", Hi: 20, Width: 5},
		{Name: "A", Hi: 11, Width: 1},
		{Name: "M", Hi: 10, Width: 1},
		{Name: "Rn", Hi: 9, Width: 5},
		{Name: "op4", Hi: 4, Width: 5},
	}
	if generated.Mnemonic != "eret" || generated.Mask != 0xffffffff ||
		generated.Value != eretWord || !reflect.DeepEqual(generated.Fields, wantFields) ||
		len(generated.Forms) != 1 || len(generated.Forms[0].Operands) != 0 {
		t.Fatalf("generated %s metadata drifted: %#v", eretEncodingName, *generated)
	}

	leanPath := filepath.Join("..", "spec", "lean", "Oak", "AArch64Encoding.lean")
	leanBytes, err := os.ReadFile(leanPath)
	if err != nil {
		t.Fatal(err)
	}
	leanEncoding, err := uniqueDelimitedBlock(string(leanBytes),
		"-- OAK-A64-ERET-ENC-BEGIN (generated from asm/encodings_gen.go; do not edit)",
		"-- OAK-A64-ERET-ENC-END")
	if err != nil {
		t.Fatal(err)
	}
	leanFields := make([]string, 0, len(generated.Fields))
	for _, field := range generated.Fields {
		leanFields = append(leanFields,
			fmt.Sprintf("⟨%q, %d, %d⟩", field.Name, field.Hi, field.Width))
	}
	wantLeanEncoding := fmt.Sprintf(
		"def eret : Encoding := ⟨%q, %q, 0x%08x#32, 0x%08x#32, [%s]⟩",
		generated.Name, generated.Mnemonic, generated.Value, generated.Mask,
		strings.Join(leanFields, ", "))
	if got := strings.TrimSpace(leanEncoding); got != wantLeanEncoding {
		t.Fatalf("%s ERET encoding drifted from asm/encodings_gen.go:\n--- have\n%s\n--- want\n%s",
			leanPath, got, wantLeanEncoding)
	}
	leanWord, err := uniqueDelimitedBlock(string(leanBytes),
		"-- OAK-A64-ERET-WORD-BEGIN (checked against asm/encode.go; do not edit)",
		"-- OAK-A64-ERET-WORD-END")
	if err != nil {
		t.Fatal(err)
	}
	wantLeanWord := "def eretWord : BitVec 32 := eret.value " +
		"theorem eret_word : eretWord = 0xd69f03e0#32 := by native_decide"
	if got := strings.Join(strings.Fields(leanWord), " "); got != wantLeanWord {
		t.Fatalf("%s exact ERET word block drifted:\n--- have\n%s\n--- want\n%s",
			leanPath, got, wantLeanWord)
	}

	encoded, err := encodeText(t, "eret")
	if err != nil {
		t.Fatal(err)
	}
	if encoded != eretWord {
		t.Fatalf("encode eret = %08x, want %08x", encoded, eretWord)
	}
}
