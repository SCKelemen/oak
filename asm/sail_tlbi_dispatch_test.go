package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

var sailVMALLS12E1ISDecodeHeader = regexp.MustCompile(
	`(?m)^function clause decode64 \(\(0b1101010100001 @ _ : bits\(19\) as op_code\) ` +
		`if SEE < 1636\) = \{`,
)

var sailVMALLS12E1ISDispatchPath = []struct {
	header  *regexp.Regexp
	elseArm bool
}{
	{regexp.MustCompile(`\bif\s+op0\s*==\s*0b01\s+then\s*\{`), false},
	{regexp.MustCompile(`\bif\s+CRn\s*==\s*0x8\s+then\s*\{`), false},
	{regexp.MustCompile(`\bif\s+op1\s*==\s*0b100\s+then\s*\{`), false},
	{regexp.MustCompile(`\bif\s+op2\s*==\s*0b001\s+then\s*\{`), true},
	{regexp.MustCompile(`\bif\s+op2\s*==\s*0b101\s+then\s*\{`), true},
	{regexp.MustCompile(`\bif\s+CRm\s*==\s*0x4\s+then\s*\{`), true},
	{regexp.MustCompile(`\bif\s+op2\s*==\s*0b110\s+then\s*\{`), false},
	{regexp.MustCompile(`\bif\s+CRm\s*==\s*0x0\s+then\s*\{`), true},
	{regexp.MustCompile(`\bif\s+CRm\s*==\s*0x1\s+then\s*\{`), true},
	{regexp.MustCompile(`\bif\s+CRm\s*==\s*0x7\s+then\s*\{`), true},
	{regexp.MustCompile(`\bif\s+CRm\s*==\s*0x3\s+then\s*\{`), false},
}

func sailBalancedBody(source string, open int) (string, int, error) {
	depth := 0
	for at := open; at < len(source); at++ {
		switch source[at] {
		case '{':
			depth++
		case '}':
			depth--
			if depth == 0 {
				return source[open+1 : at], at, nil
			}
		}
	}
	return "", 0, fmt.Errorf("unterminated Sail body at byte %d", open)
}

// sailUniqueIfArm extracts the selected braced arm of exactly one matching if.
// Each successive call receives only its parent's body, so textual ordering
// outside the branch cannot accidentally satisfy the dispatch-path audit.
func sailUniqueIfArm(source string, header *regexp.Regexp, elseArm bool) (string, error) {
	matches := header.FindAllStringIndex(source, -1)
	if len(matches) != 1 {
		return "", fmt.Errorf("Sail if header %q has %d matches, want 1",
			header.String(), len(matches))
	}
	if prefix := strings.TrimSpace(source[:matches[0][0]]); prefix != "" {
		return "", fmt.Errorf("Sail if header %q is not the arm's immediate decision: %q",
			header.String(), prefix)
	}
	open := matches[0][1] - 1
	body, close, err := sailBalancedBody(source, open)
	if err != nil || !elseArm {
		return body, err
	}
	at := close + 1
	for at < len(source) && strings.ContainsRune(" \t\r\n", rune(source[at])) {
		at++
	}
	if !strings.HasPrefix(source[at:], "else") {
		return "", fmt.Errorf("Sail if header %q has no immediate else arm", header.String())
	}
	at += len("else")
	for at < len(source) && strings.ContainsRune(" \t\r\n", rune(source[at])) {
		at++
	}
	if at >= len(source) || source[at] != '{' {
		return "", fmt.Errorf("Sail if header %q has a malformed else arm", header.String())
	}
	body, _, err = sailBalancedBody(source, at)
	return body, err
}

// TestSailArmVMALLS12E1ISDispatchSource ties Oak's pure target projection to
// the pinned official generic SYS decoder and its exact nested dispatch path.
// The official function's coarse local-model invalidation is recorded only as
// a boundary: it is not treated as proof of architectural scope or completion.
func TestSailArmVMALLS12E1ISDispatchSource(t *testing.T) {
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
		if class.mask == 0xfff80000 && class.value == 0xd5080000 && class.fn == "system_sysops" {
			classMatches++
		}
	}
	if classMatches != 1 {
		t.Fatalf("generic SYS-write decode class count = %d, want 1", classMatches)
	}
	decodeHeaders := sailVMALLS12E1ISDecodeHeader.FindAllStringIndex(decode, -1)
	if len(decodeHeaders) != 1 {
		t.Fatalf("generic SYS-write decode header count = %d, want 1", len(decodeHeaders))
	}
	officialClause, _, err := sailBalancedBody(decode, decodeHeaders[0][1]-1)
	if err != nil {
		t.Fatal(err)
	}
	wantOfficialClause := "SEE=1636;" +
		"Rt:bits(5)=op_code[4..0];" +
		"op2:bits(3)=op_code[7..5];" +
		"CRm:bits(4)=op_code[11..8];" +
		"CRn:bits(4)=op_code[15..12];" +
		"op1:bits(3)=op_code[18..16];" +
		"op0:bits(2)=op_code[20..19];" +
		"L:bits(1)=[op_code[21]];" +
		"system_sysops_decode(Rt,op2,CRm,CRn,op1,op0,L)"
	if compact := strings.Join(strings.Fields(officialClause), ""); compact != wantOfficialClause {
		t.Fatalf("official generic SYS-write decode clause changed:\n--- have\n%s\n--- want\n%s",
			compact, wantOfficialClause)
	}
	dispatchBody, err := sailFunctionBody(aarch64, "AArch64_AutoGen_SysOpsWrite")
	if err != nil {
		t.Fatal(err)
	}
	dispatchArm := dispatchBody
	for _, step := range sailVMALLS12E1ISDispatchPath {
		dispatchArm, err = sailUniqueIfArm(dispatchArm, step.header, step.elseArm)
		if err != nil {
			t.Fatal(err)
		}
	}
	if compact := strings.Join(strings.Fields(dispatchArm), ""); compact != "TLBI_VMALLS12E1IS();return()" {
		t.Fatalf("VMALLS12E1IS innermost dispatch body changed: %q", dispatchArm)
	}
	if count := strings.Count(dispatchBody, "TLBI_VMALLS12E1IS("); count != 1 {
		t.Fatalf("official SYS-write dispatch has %d VMALLS12E1IS calls, want 1", count)
	}

	decodeBody, err := sailFunctionBody(aarch64, "system_sysops_decode")
	if err != nil {
		t.Fatal(err)
	}
	compactDecode := strings.Join(strings.Fields(decodeBody), "")
	wantDecode := "__unconditional=true;" +
		"AArch64_CheckSystemAccess(0b01,op1,CRn,CRm,op2,Rt,L);" +
		"let't=UInt(Rt);" +
		"let'sys_op0=1;" +
		"let'sys_op1=UInt(op1);" +
		"let'sys_op2=UInt(op2);" +
		"let'sys_crn=UInt(CRn);" +
		"let'sys_crm=UInt(CRm);" +
		"lethas_result=L==0b1;" +
		"__PostDecode();" +
		"system_sysops(has_result,sys_crm,sys_crn,sys_op0,sys_op1,sys_op2,t)"
	if compactDecode != wantDecode {
		t.Fatalf("official system_sysops_decode body changed:\n--- have\n%s\n--- want\n%s",
			compactDecode, wantDecode)
	}

	sysopsBody, err := sailFunctionBody(aarch64, "system_sysops")
	if err != nil {
		t.Fatal(err)
	}
	wantSysops := "ifhas_resultthen" +
		"{X(t)=AArch64_SysInstrWithResult(sys_op0,sys_op1,sys_crn,sys_crm,sys_op2)}else" +
		"{AArch64_SysInstr(sys_op0,sys_op1,sys_crn,sys_crm,sys_op2,X(t))}"
	if compact := strings.Join(strings.Fields(sysopsBody), ""); compact != wantSysops {
		t.Fatalf("official system_sysops body changed:\n--- have\n%s\n--- want\n%s",
			compact, wantSysops)
	}

	sysInstrBody, err := sailFunctionBody(aarch64, "AArch64_SysInstr")
	if err != nil {
		t.Fatal(err)
	}
	wantSysInstr := "AArch64_AutoGen_SysOpsWrite(PSTATE.EL," +
		"__GetSlice_int(2,op0,0),__GetSlice_int(3,op1,0)," +
		"__GetSlice_int(4,crn,0),__GetSlice_int(3,op2,0)," +
		"__GetSlice_int(4,crm,0),0b0,val_name)"
	if compact := strings.Join(strings.Fields(sysInstrBody), ""); compact != wantSysInstr {
		t.Fatalf("official AArch64_SysInstr body changed:\n--- have\n%s\n--- want\n%s",
			compact, wantSysInstr)
	}

	targetBody, err := sailFunctionBody(aarch64, "TLBI_VMALLS12E1IS")
	if err != nil {
		t.Fatal(err)
	}
	if compact := strings.Join(strings.Fields(targetBody), ""); compact != "_TLB_Invalidate()" {
		t.Fatalf("official TLBI_VMALLS12E1IS body changed: %q", targetBody)
	}

	projectionBytes, err := os.ReadFile(filepath.Join("..", "spec", "sail", "arm_primitives.sail"))
	if err != nil {
		t.Fatal(err)
	}
	projectionBody, err := sailFunctionBody(string(projectionBytes),
		"aarch64_sysops_write_tlbi_target_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantProjection := "ifop0==0b01&op1==0b100&CRn==0x8&" +
		"op2==0b110&CRm==0x3then" +
		"{(true,TLBIOperationTarget_VMALLS12E1IS)}else" +
		"{(false,TLBIOperationTarget_VMALLS12E1IS)}"
	if compact := strings.Join(strings.Fields(projectionBody), ""); compact != wantProjection {
		t.Fatalf("local VMALLS12E1IS target projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantProjection)
	}
	projectionDecodeBody, err := sailFunctionBody(string(projectionBytes),
		"decode64_tlbi_target_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantProjectionDecode := "letop0:bits(2)=slice(op_code,19,2);" +
		"letop1:bits(3)=slice(op_code,16,3);" +
		"letCRn:bits(4)=slice(op_code,12,4);" +
		"letCRm:bits(4)=slice(op_code,8,4);" +
		"letop2:bits(3)=slice(op_code,5,3);" +
		"if(op_code&0xFFF80000)==0xD5080000then" +
		"{aarch64_sysops_write_tlbi_target_pure(op0,op1,CRn,op2,CRm)}else" +
		"{(false,TLBIOperationTarget_VMALLS12E1IS)}"
	if compact := strings.Join(strings.Fields(projectionDecodeBody), ""); compact != wantProjectionDecode {
		t.Fatalf("local generic SYS-write projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantProjectionDecode)
	}
}
