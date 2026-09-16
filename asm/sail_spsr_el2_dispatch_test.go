package asm

import (
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

var sailSPSREL2WriteDecodeHeader = regexp.MustCompile(
	`(?m)^function clause decode64 \(\(0b110101010001 @ _ : bits\(20\) as op_code\) ` +
		`if SEE < 1131\) = \{`,
)

var sailSPSREL2WriteDispatchPath = []struct {
	header  *regexp.Regexp
	elseArm bool
}{
	{regexp.MustCompile(`\bif\s+op2\s*==\s*0b000\s+then\s*\{`), false},
	{regexp.MustCompile(`\bif\s+op1\s*==\s*0b100\s+then\s*\{`), false},
	{regexp.MustCompile(`\bif\s+CRm\s*==\s*0x0\s+then\s*\{`), false},
	{regexp.MustCompile(`\bif\s+CRn\s*==\s*0xC\s+then\s*\{`), true},
	{regexp.MustCompile(`\bif\s+CRn\s*==\s*0x4\s+then\s*\{`), false},
}

var sailSPSREL1AliasDispatchPath = []struct {
	header  *regexp.Regexp
	elseArm bool
}{
	{regexp.MustCompile(`\bif\s+op2\s*==\s*0b000\s+then\s*\{`), false},
	{regexp.MustCompile(`\bif\s+op1\s*==\s*0b100\s+then\s*\{`), true},
	{regexp.MustCompile(`\bif\s+op1\s*==\s*0b000\s+then\s*\{`), false},
	{regexp.MustCompile(`\bif\s+CRm\s*==\s*0x0\s+then\s*\{`), false},
	{regexp.MustCompile(`\bif\s+CRn\s*==\s*0xC\s+then\s*\{`), true},
	{regexp.MustCompile(`\bif\s+CRn\s*==\s*0x1\s+then\s*\{`), true},
	{regexp.MustCompile(`\bif\s+CRn\s*==\s*0x6\s+then\s*\{`), true},
	{regexp.MustCompile(`\bif\s+CRn\s*==\s*0x4\s+then\s*\{`), false},
}

// TestSailArmSPSREL2WriteDispatchSource pins Oak's exact S3_4_C4_C0_0 route.
// The official model's second SPSR_EL2 assignment belongs to the distinct
// S3_0 SPSR_EL1/VHE route and is deliberately excluded from this projection.
func TestSailArmSPSREL2WriteDispatchSource(t *testing.T) {
	modelDir := filepath.Dir(sailArmModel)
	decodeBytes, err := os.ReadFile(sailArmModel)
	if err != nil {
		requireOracle(t, "sail-arm AArch64 decoder not present: "+err.Error())
	}
	aarch64Bytes, err := os.ReadFile(filepath.Join(modelDir, "aarch64.sail"))
	if err != nil {
		requireOracle(t, "sail-arm aarch64 model not present: "+err.Error())
	}
	aarchMemBytes, err := os.ReadFile(filepath.Join(modelDir, "aarch_mem.sail"))
	if err != nil {
		requireOracle(t, "sail-arm architectural memory model not present: "+err.Error())
	}
	decode := string(decodeBytes)
	aarch64 := string(aarch64Bytes)
	aarchMem := string(aarchMemBytes)

	classes, err := parseSailDecodeClasses(sailArmModel)
	if err != nil {
		t.Fatal(err)
	}
	classMatches := 0
	for _, class := range classes {
		if class.mask == 0xfff00000 && class.value == 0xd5100000 &&
			class.fn == "system_register_system" {
			classMatches++
		}
	}
	if classMatches != 1 {
		t.Fatalf("general MSR decode class count = %d, want 1", classMatches)
	}

	decodeHeaders := sailSPSREL2WriteDecodeHeader.FindAllStringIndex(decode, -1)
	if len(decodeHeaders) != 1 {
		t.Fatalf("general MSR decode header count = %d, want 1", len(decodeHeaders))
	}
	officialClause, _, err := sailBalancedBody(decode, decodeHeaders[0][1]-1)
	if err != nil {
		t.Fatal(err)
	}
	wantOfficialClause := "SEE=1131;" +
		"Rt:bits(5)=op_code[4..0];" +
		"op2:bits(3)=op_code[7..5];" +
		"CRm:bits(4)=op_code[11..8];" +
		"CRn:bits(4)=op_code[15..12];" +
		"op1:bits(3)=op_code[18..16];" +
		"o0:bits(1)=[op_code[19]];" +
		"L:bits(1)=[op_code[21]];" +
		"system_register_system_decode(Rt,op2,CRm,CRn,op1,o0,L)"
	if compact := strings.Join(strings.Fields(officialClause), ""); compact != wantOfficialClause {
		t.Fatalf("official general MSR decode clause changed:\n--- have\n%s\n--- want\n%s",
			compact, wantOfficialClause)
	}

	decodeBody, err := sailFunctionBody(aarch64, "system_register_system_decode")
	if err != nil {
		t.Fatal(err)
	}
	wantDecodeBody := "__unconditional=true;" +
		"AArch64_CheckSystemAccess(0b1@o0,op1,CRn,CRm,op2,Rt,L);" +
		"let't=UInt(Rt);" +
		"let'sys_op0=2+UInt(o0);" +
		"let'sys_op1=UInt(op1);" +
		"let'sys_op2=UInt(op2);" +
		"let'sys_crn=UInt(CRn);" +
		"let'sys_crm=UInt(CRm);" +
		"letread=L==0b1;" +
		"__PostDecode();" +
		"system_register_system(read,sys_crm,sys_crn,sys_op0,sys_op1,sys_op2,t)"
	if compact := strings.Join(strings.Fields(decodeBody), ""); compact != wantDecodeBody {
		t.Fatalf("official system_register_system_decode body changed:\n--- have\n%s\n--- want\n%s",
			compact, wantDecodeBody)
	}

	systemBody, err := sailFunctionBody(aarch64, "system_register_system")
	if err != nil {
		t.Fatal(err)
	}
	wantSystemBody := "ifreadthen" +
		"{X(t)=AArch64_SysRegRead(sys_op0,sys_op1,sys_crn,sys_crm,sys_op2)}else" +
		"{AArch64_SysRegWrite(sys_op0,sys_op1,sys_crn,sys_crm,sys_op2,X(t))}"
	if compact := strings.Join(strings.Fields(systemBody), ""); compact != wantSystemBody {
		t.Fatalf("official system_register_system body changed:\n--- have\n%s\n--- want\n%s",
			compact, wantSystemBody)
	}

	sysRegWriteBody, err := sailFunctionBody(aarch64, "AArch64_SysRegWrite")
	if err != nil {
		t.Fatal(err)
	}
	wantSysRegWriteBody := "AArch64_AutoGen_SysRegWrite(PSTATE.EL," +
		"__GetSlice_int(2,op0,0),__GetSlice_int(3,op1,0)," +
		"__GetSlice_int(4,crn,0),__GetSlice_int(3,op2,0)," +
		"__GetSlice_int(4,crm,0),0b0,val_name);" +
		"if((((op0==3&crn==12)&((op1==6|op1==4)|op1==0))&op2==2)&crm==0)&" +
		"[val_name[1]]==0b1then{TakeReset(false)};return()"
	if compact := strings.Join(strings.Fields(sysRegWriteBody), ""); compact != wantSysRegWriteBody {
		t.Fatalf("official AArch64_SysRegWrite body changed:\n--- have\n%s\n--- want\n%s",
			compact, wantSysRegWriteBody)
	}

	autoWriteBody, err := sailFunctionBody(aarch64, "AArch64_AutoGen_SysRegWrite")
	if err != nil {
		t.Fatal(err)
	}
	compactAutoWriteBody := strings.Join(strings.Fields(autoWriteBody), "")
	for name, binding := range map[string]string{
		"HCR_EL2.NV":   "let__HCR_EL2_NV=[HCR_EL2[42]];",
		"HCR_EL2.NV1":  "let__HCR_EL2_NV1=[HCR_EL2[43]];",
		"HCR_EL2.NV2":  "let__HCR_EL2_NV2=[HCR_EL2[45]];",
		"HCR_EL2.TGE":  "let__HCR_EL2_TGE=[HCR_EL2[27]];",
		"HCR_EL2.E2H":  "let__HCR_EL2_E2H=[HCR_EL2[34]];",
		"SCR_EL3.NS":   "let__SCR_EL3_NS=[SCR_EL3[0]];",
		"SCR_EL3.EEL2": "let__SCR_EL3_EEL2=[SCR_EL3[18]];",
	} {
		if count := strings.Count(compactAutoWriteBody, binding); count != 1 {
			t.Fatalf("official SysRegWrite %s alias binding count = %d, want 1", name, count)
		}
	}
	spsrEl2Branch, err := sailUniqueContainingIfArm(
		autoWriteBody,
		regexp.MustCompile(`\bif\s+op0\s*==\s*0b11\s+then\s*\{`),
		"SPSR_EL2 = slice(val_name, 0, 32)",
	)
	if err != nil {
		t.Fatal(err)
	}
	for _, step := range sailSPSREL2WriteDispatchPath {
		spsrEl2Branch, err = sailUniqueIfArm(spsrEl2Branch, step.header, step.elseArm)
		if err != nil {
			t.Fatal(err)
		}
	}
	wantSPSREL2Branch := "SPSR_EL2=slice(val_name,0,32)"
	if compact := strings.Join(strings.Fields(spsrEl2Branch), ""); compact != wantSPSREL2Branch {
		t.Fatalf("official exact SPSR_EL2 write branch changed:\n--- have\n%s\n--- want\n%s",
			compact, wantSPSREL2Branch)
	}
	if count := strings.Count(autoWriteBody, "SPSR_EL2 = slice(val_name, 0, 32)"); count != 2 {
		t.Fatalf("official SysRegWrite has %d SPSR_EL2 assignments, want exact and SPSR_EL1/VHE routes", count)
	}
	spsrEl1AliasBranch, err := sailUniqueContainingIfArm(
		autoWriteBody,
		regexp.MustCompile(`\bif\s+op0\s*==\s*0b11\s+then\s*\{`),
		"NVMem(352) = ZeroExtend(slice(val_name, 0, 32))",
	)
	if err != nil {
		t.Fatal(err)
	}
	for _, step := range sailSPSREL1AliasDispatchPath {
		spsrEl1AliasBranch, err = sailUniqueIfArm(spsrEl1AliasBranch, step.header, step.elseArm)
		if err != nil {
			t.Fatal(err)
		}
	}
	compactAliasBranch := strings.Join(strings.Fields(spsrEl1AliasBranch), "")
	wantVHECondition := "((el==EL2&__HCR_EL2_TGE==0)&__HCR_EL2_E2H==1)&" +
		"(__SCR_EL3_NS==1|__SCR_EL3_EEL2==1)|" +
		"((el==EL2&__HCR_EL2_TGE==1)&__HCR_EL2_E2H==1)&" +
		"(__SCR_EL3_NS==1|__SCR_EL3_EEL2==1)"
	wantNVCondition := "(((((el==EL1&__HCR_EL2_NV==1)&__HCR_EL2_NV1==1)&" +
		"__HCR_EL2_NV2==1)&__HCR_EL2_TGE==0)&__HCR_EL2_E2H==0)&" +
		"(__SCR_EL3_NS==1|__SCR_EL3_EEL2==1)|" +
		"(((((el==EL1&__HCR_EL2_NV==1)&__HCR_EL2_NV1==1)&" +
		"__HCR_EL2_NV2==1)&__HCR_EL2_TGE==0)&__HCR_EL2_E2H==1)&" +
		"(__SCR_EL3_NS==1|__SCR_EL3_EEL2==1)"
	wantAliasBranch := "if" + wantVHECondition +
		"then{SPSR_EL2=slice(val_name,0,32)}else{if" + wantNVCondition +
		"then{NVMem(352)=ZeroExtend(slice(val_name,0,32))}else" +
		"{SPSR_EL1=ZeroExtend(slice(val_name,0,32))}}"
	if compactAliasBranch != wantAliasBranch {
		t.Fatalf("official SPSR_EL1 alias route changed:\n--- have\n%s\n--- want\n%s",
			compactAliasBranch, wantAliasBranch)
	}
	if count := strings.Count(aarchMem, "register SPSR_EL2 : bits(32)"); count != 1 {
		t.Fatalf("official model has %d SPSR_EL2 declarations, want 1", count)
	}

	projectionBytes, err := os.ReadFile(filepath.Join("..", "spec", "sail", "arm_primitives.sail"))
	if err != nil {
		t.Fatal(err)
	}
	projection := string(projectionBytes)
	targetBody, err := sailFunctionBody(projection, "system_register_spsr_el2_target_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantTargetBody := "ifo0==0b1&op1==0b100&CRn==0x4&CRm==0x0&op2==0b000then" +
		"{(true,SystemRegisterWriteTarget_SPSR_EL2,Rt)}else" +
		"{(false,SystemRegisterWriteTarget_SPSR_EL2,Rt)}"
	if compact := strings.Join(strings.Fields(targetBody), ""); compact != wantTargetBody {
		t.Fatalf("local SPSR_EL2 target projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantTargetBody)
	}
	projectionDecodeBody, err := sailFunctionBody(projection, "decode64_system_write_spsr_el2_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantProjectionDecode := "letRt:bits(5)=slice(op_code,0,5);" +
		"letop2:bits(3)=slice(op_code,5,3);" +
		"letCRm:bits(4)=slice(op_code,8,4);" +
		"letCRn:bits(4)=slice(op_code,12,4);" +
		"letop1:bits(3)=slice(op_code,16,3);" +
		"leto0:bits(1)=slice(op_code,19,1);" +
		"if(op_code&0xFFF00000)==0xD5100000then" +
		"{system_register_spsr_el2_target_pure(o0,op1,CRn,CRm,op2,Rt)}else" +
		"{(false,SystemRegisterWriteTarget_SPSR_EL2,Rt)}"
	if compact := strings.Join(strings.Fields(projectionDecodeBody), ""); compact != wantProjectionDecode {
		t.Fatalf("local general MSR SPSR_EL2 decoder projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantProjectionDecode)
	}
	componentBody, err := sailFunctionBody(projection, "aarch64_sysregwrite_spsr_el2_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantComponentBody := "slice(val_name,0,32)"
	if compact := strings.Join(strings.Fields(componentBody), ""); compact != wantComponentBody {
		t.Fatalf("local SPSR_EL2 component projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantComponentBody)
	}
}
