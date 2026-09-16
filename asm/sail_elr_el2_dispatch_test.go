package asm

import (
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

var sailELREL2WriteDecodeHeader = regexp.MustCompile(
	`(?m)^function clause decode64 \(\(0b110101010001 @ _ : bits\(20\) as op_code\) ` +
		`if SEE < 1131\) = \{`,
)

var sailELREL2WriteDispatchPath = []struct {
	header  *regexp.Regexp
	elseArm bool
}{
	{regexp.MustCompile(`\bif\s+op2\s*==\s*0b000\s+then\s*\{`), true},
	{regexp.MustCompile(`\bif\s+op2\s*==\s*0b001\s+then\s*\{`), false},
	{regexp.MustCompile(`\bif\s+op1\s*==\s*0b100\s+then\s*\{`), false},
	{regexp.MustCompile(`\bif\s+CRm\s*==\s*0x0\s+then\s*\{`), false},
	{regexp.MustCompile(`\bif\s+CRn\s*==\s*0x4\s+then\s*\{`), false},
}

// TestSailArmELREL2WriteDispatchSource pins Oak's exact S3_4_C4_C0_1 route.
// The official model's second ELR_EL2 assignment belongs to the distinct
// S3_0 ELR_EL1/VHE route and is deliberately excluded from this projection.
func TestSailArmELREL2WriteDispatchSource(t *testing.T) {
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

	decodeHeaders := sailELREL2WriteDecodeHeader.FindAllStringIndex(decode, -1)
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
	elrEl2Branch, err := sailUniqueContainingIfArm(
		autoWriteBody,
		regexp.MustCompile(`\bif\s+op0\s*==\s*0b11\s+then\s*\{`),
		"ELR_EL2 = val_name",
	)
	if err != nil {
		t.Fatal(err)
	}
	for _, step := range sailELREL2WriteDispatchPath {
		elrEl2Branch, err = sailUniqueIfArm(elrEl2Branch, step.header, step.elseArm)
		if err != nil {
			t.Fatal(err)
		}
	}
	wantELREL2Branch := "ELR_EL2=val_name"
	if compact := strings.Join(strings.Fields(elrEl2Branch), ""); compact != wantELREL2Branch {
		t.Fatalf("official exact ELR_EL2 write branch changed:\n--- have\n%s\n--- want\n%s",
			compact, wantELREL2Branch)
	}
	if count := strings.Count(autoWriteBody, "ELR_EL2 = val_name"); count != 2 {
		t.Fatalf("official SysRegWrite has %d ELR_EL2 assignments, want exact and ELR_EL1/VHE routes", count)
	}
	if count := strings.Count(aarchMem, "register ELR_EL2 : bits(64)"); count != 1 {
		t.Fatalf("official model has %d ELR_EL2 declarations, want 1", count)
	}

	projectionBytes, err := os.ReadFile(filepath.Join("..", "spec", "sail", "arm_primitives.sail"))
	if err != nil {
		t.Fatal(err)
	}
	projection := string(projectionBytes)
	targetBody, err := sailFunctionBody(projection, "system_register_elr_el2_target_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantTargetBody := "ifo0==0b1&op1==0b100&CRn==0x4&CRm==0x0&op2==0b001then" +
		"{(true,SystemRegisterWriteTarget_ELR_EL2,Rt)}else" +
		"{(false,SystemRegisterWriteTarget_ELR_EL2,Rt)}"
	if compact := strings.Join(strings.Fields(targetBody), ""); compact != wantTargetBody {
		t.Fatalf("local ELR_EL2 target projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantTargetBody)
	}
	projectionDecodeBody, err := sailFunctionBody(projection, "decode64_system_write_elr_el2_pure")
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
		"{system_register_elr_el2_target_pure(o0,op1,CRn,CRm,op2,Rt)}else" +
		"{(false,SystemRegisterWriteTarget_ELR_EL2,Rt)}"
	if compact := strings.Join(strings.Fields(projectionDecodeBody), ""); compact != wantProjectionDecode {
		t.Fatalf("local general MSR ELR_EL2 decoder projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantProjectionDecode)
	}
	componentBody, err := sailFunctionBody(projection, "aarch64_sysregwrite_elr_el2_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantComponentBody := "val_name"
	if compact := strings.Join(strings.Fields(componentBody), ""); compact != wantComponentBody {
		t.Fatalf("local ELR_EL2 component projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantComponentBody)
	}
}
