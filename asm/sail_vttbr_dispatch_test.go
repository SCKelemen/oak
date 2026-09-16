package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

var sailVTTBRWriteDecodeHeader = regexp.MustCompile(
	`(?m)^function clause decode64 \(\(0b110101010001 @ _ : bits\(20\) as op_code\) ` +
		`if SEE < 1131\) = \{`,
)

var sailVTTBRWriteDispatchPath = []struct {
	header  *regexp.Regexp
	elseArm bool
}{
	{regexp.MustCompile(`\bif\s+op2\s*==\s*0b000\s+then\s*\{`), false},
	{regexp.MustCompile(`\bif\s+op1\s*==\s*0b100\s+then\s*\{`), false},
	{regexp.MustCompile(`\bif\s+CRm\s*==\s*0x0\s+then\s*\{`), true},
	{regexp.MustCompile(`\bif\s+CRm\s*==\s*0x1\s+then\s*\{`), false},
	{regexp.MustCompile(`\bif\s+CRn\s*==\s*0xE\s+then\s*\{`), true},
	{regexp.MustCompile(`\bif\s+CRn\s*==\s*0x1\s+then\s*\{`), true},
	{regexp.MustCompile(`\bif\s+CRn\s*==\s*0x4\s+then\s*\{`), true},
	{regexp.MustCompile(`\bif\s+CRn\s*==\s*0x5\s+then\s*\{`), true},
	{regexp.MustCompile(`\bif\s+CRn\s*==\s*0x2\s+then\s*\{`), false},
}

// sailUniqueContainingIfArm selects the true arm of the one matching if whose
// body contains marker. It is used only for the outer op0 branch; subsequent
// dispatch decisions must be immediate and unique via sailUniqueIfArm.
func sailUniqueContainingIfArm(source string, header *regexp.Regexp, marker string) (string, error) {
	var selected string
	selectedCount := 0
	for _, match := range header.FindAllStringIndex(source, -1) {
		depth := 0
		for _, char := range source[:match[0]] {
			switch char {
			case '{':
				depth++
			case '}':
				depth--
				if depth < 0 {
					return "", fmt.Errorf("unbalanced Sail braces before if header %q", header.String())
				}
			}
		}
		if depth != 0 {
			continue
		}
		body, _, err := sailBalancedBody(source, match[1]-1)
		if err != nil {
			return "", err
		}
		if strings.Contains(body, marker) {
			selected = body
			selectedCount++
		}
	}
	if selectedCount != 1 {
		return "", fmt.Errorf("Sail if header %q has %d arms containing %q, want 1",
			header.String(), selectedCount, marker)
	}
	return selected, nil
}

// TestSailArmVTTBREL2WriteDispatchSource pins Oak's component-only VTTBR_EL2
// projection to the official general-MSR route and direct/register-redirection
// branch. It does not prove access admission, X1 value provenance, occurrence,
// register-value validity, publication, or translation/context effects.
func TestSailArmVTTBREL2WriteDispatchSource(t *testing.T) {
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
		requireOracle(t, "sail-arm register model not present: "+err.Error())
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

	decodeHeaders := sailVTTBRWriteDecodeHeader.FindAllStringIndex(decode, -1)
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
		"HCR_EL2.NV2":  "let__HCR_EL2_NV2=[HCR_EL2[45]];",
		"HCR_EL2.TGE":  "let__HCR_EL2_TGE=[HCR_EL2[27]];",
		"SCR_EL3.NS":   "let__SCR_EL3_NS=[SCR_EL3[0]];",
		"SCR_EL3.EEL2": "let__SCR_EL3_EEL2=[SCR_EL3[18]];",
	} {
		if count := strings.Count(compactAutoWriteBody, binding); count != 1 {
			t.Fatalf("official SysRegWrite %s alias binding count = %d, want 1", name, count)
		}
	}
	vttbrBranch, err := sailUniqueContainingIfArm(
		autoWriteBody,
		regexp.MustCompile(`\bif\s+op0\s*==\s*0b11\s+then\s*\{`),
		"VTTBR_EL2 = val_name",
	)
	if err != nil {
		t.Fatal(err)
	}
	for _, step := range sailVTTBRWriteDispatchPath {
		vttbrBranch, err = sailUniqueIfArm(vttbrBranch, step.header, step.elseArm)
		if err != nil {
			t.Fatal(err)
		}
	}
	wantVTTBRBranch := "if(((el==EL1&__HCR_EL2_NV==1)&__HCR_EL2_NV2==1)&" +
		"__HCR_EL2_TGE==0)&(__SCR_EL3_NS==1|__SCR_EL3_EEL2==1)then" +
		"{NVMem(32)=val_name}else{VTTBR_EL2=val_name}"
	if compact := strings.Join(strings.Fields(vttbrBranch), ""); compact != wantVTTBRBranch {
		t.Fatalf("official VTTBR_EL2 write branch changed:\n--- have\n%s\n--- want\n%s",
			compact, wantVTTBRBranch)
	}
	if count := strings.Count(autoWriteBody, "VTTBR_EL2 = val_name"); count != 1 {
		t.Fatalf("official SysRegWrite has %d direct VTTBR_EL2 assignments, want 1", count)
	}
	if count := strings.Count(aarchMem, "register VTTBR_EL2 : bits(64)"); count != 1 {
		t.Fatalf("official register model has %d VTTBR_EL2 declarations, want 1", count)
	}

	projectionBytes, err := os.ReadFile(filepath.Join("..", "spec", "sail", "arm_primitives.sail"))
	if err != nil {
		t.Fatal(err)
	}
	projection := string(projectionBytes)
	targetBody, err := sailFunctionBody(projection, "system_register_vttbr_el2_target_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantTargetBody := "ifo0==0b1&op1==0b100&CRn==0x2&CRm==0x1&op2==0b000then" +
		"{(true,SystemRegisterWriteTarget_VTTBR_EL2,Rt)}else" +
		"{(false,SystemRegisterWriteTarget_VTTBR_EL2,Rt)}"
	if compact := strings.Join(strings.Fields(targetBody), ""); compact != wantTargetBody {
		t.Fatalf("local VTTBR_EL2 target projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantTargetBody)
	}
	projectionDecodeBody, err := sailFunctionBody(projection, "decode64_system_write_vttbr_el2_pure")
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
		"{system_register_vttbr_el2_target_pure(o0,op1,CRn,CRm,op2,Rt)}else" +
		"{(false,SystemRegisterWriteTarget_VTTBR_EL2,Rt)}"
	if compact := strings.Join(strings.Fields(projectionDecodeBody), ""); compact != wantProjectionDecode {
		t.Fatalf("local general MSR decoder projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantProjectionDecode)
	}
	componentBody, err := sailFunctionBody(projection, "aarch64_sysregwrite_vttbr_el2_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantComponentBody := "letredirected:bool=at_el1&hcr_nv&hcr_nv2&~(hcr_tge)&" +
		"(scr_ns|scr_eel2);ifredirectedthen{(true,old_value)}else{(false,val_name)}"
	if compact := strings.Join(strings.Fields(componentBody), ""); compact != wantComponentBody {
		t.Fatalf("local VTTBR_EL2 component projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantComponentBody)
	}
}
