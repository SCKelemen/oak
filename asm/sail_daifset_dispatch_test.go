package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

var sailDAIFSetDecodeHeader = regexp.MustCompile(
	`(?m)^function clause decode64 \(\(0b1101010100000 @ _ : bits\(3\) @ 0b0100 @ _ : bits\(7\) @ 0b11111 as op_code\) ` +
		`if SEE < 1160\) = \{`,
)

func sailUniqueArm(source string, header *regexp.Regexp) (string, int, error) {
	matches := header.FindAllStringIndex(source, -1)
	if len(matches) != 1 {
		return "", 0, fmt.Errorf("Sail arm %q has %d matches, want 1",
			header.String(), len(matches))
	}
	return sailBalancedBody(source, matches[0][1]-1)
}

func requireUniqueFragmentsInOrder(t *testing.T, source string, fragments ...string) {
	t.Helper()
	previous := -1
	for _, fragment := range fragments {
		if count := strings.Count(source, fragment); count != 1 {
			t.Fatalf("Sail source contains %d copies of %q, want 1", count, fragment)
		}
		at := strings.Index(source, fragment)
		if at <= previous {
			t.Fatalf("Sail source fragment %q is out of order", fragment)
		}
		previous = at
	}
}

// TestSailArmDAIFSetDispatchSource pins the successful DAIFSet target and
// four-bit state-body projections to the pinned official decoder source. It
// audits the access/trap boundary but does not prove those checks admit an
// execution, that the instruction occurs, or any interrupt-delivery property.
func TestSailArmDAIFSetDispatchSource(t *testing.T) {
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
		if class.mask == 0xfff8f01f && class.value == 0xd500401f &&
			class.fn == "system_register_cpsr" {
			classMatches++
		}
	}
	if classMatches != 1 {
		t.Fatalf("PSTATE-immediate decode class count = %d, want 1", classMatches)
	}

	decodeHeaders := sailDAIFSetDecodeHeader.FindAllStringIndex(decode, -1)
	if len(decodeHeaders) != 1 {
		t.Fatalf("PSTATE-immediate decode header count = %d, want 1", len(decodeHeaders))
	}
	officialClause, _, err := sailBalancedBody(decode, decodeHeaders[0][1]-1)
	if err != nil {
		t.Fatal(err)
	}
	wantOfficialClause := "SEE=1160;" +
		"Rt:bits(5)=op_code[4..0];" +
		"op2:bits(3)=op_code[7..5];" +
		"CRm:bits(4)=op_code[11..8];" +
		"CRn:bits(4)=op_code[15..12];" +
		"op1:bits(3)=op_code[18..16];" +
		"op0:bits(2)=op_code[20..19];" +
		"L:bits(1)=[op_code[21]];" +
		"system_register_cpsr_decode(Rt,op2,CRm,CRn,op1,op0,L)"
	if compact := strings.Join(strings.Fields(officialClause), ""); compact != wantOfficialClause {
		t.Fatalf("official PSTATE-immediate decode clause changed:\n--- have\n%s\n--- want\n%s",
			compact, wantOfficialClause)
	}

	decodeBody, err := sailFunctionBody(aarch64, "system_register_cpsr_decode")
	if err != nil {
		t.Fatal(err)
	}
	compactDecode := strings.Join(strings.Fields(decodeBody), "")
	wantDecode := "__unconditional=true;" +
		"ifop1==0b000&op2==0b000then{throw(Error_See(\"CFINV\"))};" +
		"ifop1==0b000&op2==0b001then{throw(Error_See(\"XAFlag\"))};" +
		"ifop1==0b000&op2==0b010then{throw(Error_See(\"AXFlag\"))};" +
		"AArch64_CheckSystemAccess(0b00,op1,0x4,CRm,op2,0b11111,0b0);" +
		"letoperand=CRm;" +
		"field:PSTATEField=undefined:PSTATEField;" +
		"matchop1@op2{" +
		"0b000011=>{if~(HaveUAOExt())then{throw(Error_Undefined())};field=PSTATEField_UAO}," +
		"0b000100=>{if~(HavePANExt())then{throw(Error_Undefined())};field=PSTATEField_PAN}," +
		"0b000101=>{field=PSTATEField_SP}," +
		"0b011010=>{if~(HaveDITExt())then{throw(Error_Undefined())};field=PSTATEField_DIT}," +
		"0b011110=>{field=PSTATEField_DAIFSet}," +
		"0b011111=>{field=PSTATEField_DAIFClr}," +
		"_=>{throw(Error_Undefined())}" +
		"};" +
		"letfield=field;" +
		"if(op1==0b011&PSTATE.EL==EL0)&(IsInHost()|[SCTLR_EL1[9]]==0b0)then" +
		"{AArch64_SystemRegisterTrap(EL1,0b00,op2,op1,0x4,0b11111,CRm,0b0)};" +
		"__PostDecode();" +
		"system_register_cpsr(field,operand)"
	if compactDecode != wantDecode {
		t.Fatalf("official system_register_cpsr_decode body changed:\n--- have\n%s\n--- want\n%s",
			compactDecode, wantDecode)
	}
	selectorBody, _, err := sailUniqueArm(decodeBody,
		regexp.MustCompile(`(?m)^\s*0b011110\s*=>\s*\{`))
	if err != nil {
		t.Fatal(err)
	}
	if compact := strings.Join(strings.Fields(selectorBody), ""); compact != "field=PSTATEField_DAIFSet" {
		t.Fatalf("official DAIFSet selector changed: %q", selectorBody)
	}
	requireUniqueFragmentsInOrder(t, decodeBody,
		"AArch64_CheckSystemAccess(0b00, op1, 0x4, CRm, op2, 0b11111, 0b0);",
		"let operand = CRm;",
		"0b011110 => {",
		"AArch64_SystemRegisterTrap(EL1, 0b00, op2, op1, 0x4, 0b11111, CRm, 0b0)",
		"__PostDecode();",
		"system_register_cpsr(field, operand)")

	executionBody, err := sailFunctionBody(aarch64, "system_register_cpsr")
	if err != nil {
		t.Fatal(err)
	}
	daifSetBody, _, err := sailUniqueArm(executionBody,
		regexp.MustCompile(`(?m)^\s*PSTATEField_DAIFSet\s*=>\s*\{`))
	if err != nil {
		t.Fatal(err)
	}
	wantDAIFSetBody := "PSTATE.D=PSTATE.D|[operand[3]];" +
		"PSTATE.A=PSTATE.A|[operand[2]];" +
		"PSTATE.I=PSTATE.I|[operand[1]];" +
		"PSTATE.F=PSTATE.F|[operand[0]]"
	if compact := strings.Join(strings.Fields(daifSetBody), ""); compact != wantDAIFSetBody {
		t.Fatalf("official DAIFSet state body changed:\n--- have\n%s\n--- want\n%s",
			compact, wantDAIFSetBody)
	}

	projectionBytes, err := os.ReadFile(filepath.Join("..", "spec", "sail", "arm_primitives.sail"))
	if err != nil {
		t.Fatal(err)
	}
	projection := string(projectionBytes)
	targetBody, err := sailFunctionBody(projection, "system_register_cpsr_daifset_target_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantTargetBody := "ifop1@op2==0b011110then" +
		"{(true,PSTATEWriteTarget_DAIFSet,CRm)}else" +
		"{(false,PSTATEWriteTarget_DAIFSet,CRm)}"
	if compact := strings.Join(strings.Fields(targetBody), ""); compact != wantTargetBody {
		t.Fatalf("local DAIFSet target projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantTargetBody)
	}
	projectionDecodeBody, err := sailFunctionBody(projection, "decode64_pstate_write_target_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantProjectionDecode := "letop2:bits(3)=slice(op_code,5,3);" +
		"letCRm:bits(4)=slice(op_code,8,4);" +
		"letop1:bits(3)=slice(op_code,16,3);" +
		"if(op_code&0xFFF8F01F)==0xD500401Fthen" +
		"{system_register_cpsr_daifset_target_pure(op2,CRm,op1)}else" +
		"{(false,PSTATEWriteTarget_DAIFSet,CRm)}"
	if compact := strings.Join(strings.Fields(projectionDecodeBody), ""); compact != wantProjectionDecode {
		t.Fatalf("local PSTATE-immediate decoder projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantProjectionDecode)
	}
	stateBody, err := sailFunctionBody(projection, "system_register_cpsr_daifset_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantStateBody := "letd_out:bits(1)=d|[operand[3]];" +
		"leta_out:bits(1)=a|[operand[2]];" +
		"leti_out:bits(1)=i|[operand[1]];" +
		"letf_out:bits(1)=f|[operand[0]];" +
		"(d_out,a_out,i_out,f_out)"
	if compact := strings.Join(strings.Fields(stateBody), ""); compact != wantStateBody {
		t.Fatalf("local DAIFSet state projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantStateBody)
	}
}
