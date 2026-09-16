package asm

import (
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

var sailOrdinaryBLDecodeHeader = regexp.MustCompile(
	`(?m)^function clause decode64 \(\(0b100101 @ _ : bits\(26\) as op_code\) if SEE < 1597\) = \{`,
)

// TestSailArmDirectBLDispatchSource ties Oak's ordinary BL encoding and pure
// decode projection to the pinned official Arm decoder. It audits static
// encoding, decode dispatch, BranchType_DIRCALL selection, and signed immediate
// scaling only. It does not prove architectural PC, PostDecode, the dynamic X30
// write, BranchTo, target validity, source-CFG label choice, object/link
// correctness, or observation of a transfer.
func TestSailArmDirectBLDispatchSource(t *testing.T) {
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
		if class.mask == 0xfc000000 && class.value == 0x94000000 &&
			class.fn == "branch_unconditional_immediate" {
			classMatches++
		}
	}
	if classMatches != 1 {
		t.Fatalf("ordinary BL decode class count = %d, want 1", classMatches)
	}

	officialClause, _, err := sailUniqueArm(decode, sailOrdinaryBLDecodeHeader)
	if err != nil {
		t.Fatal(err)
	}
	wantOfficialClause := "SEE=1597;" +
		"imm26:bits(26)=op_code[25..0];" +
		"op:bits(1)=[op_code[31]];" +
		"branch_unconditional_immediate_decode(imm26,op)"
	if compact := strings.Join(strings.Fields(officialClause), ""); compact != wantOfficialClause {
		t.Fatalf("official ordinary BL decode clause changed:\n--- have\n%s\n--- want\n%s",
			compact, wantOfficialClause)
	}

	decodeBody, err := sailFunctionBody(aarch64, "branch_unconditional_immediate_decode")
	if err != nil {
		t.Fatal(err)
	}
	wantDecodeBody := "__unconditional=true;" +
		"letbranch_type=ifop==0b1thenBranchType_DIRCALLelseBranchType_DIR;" +
		"letoffset=SignExtend(imm26@0b00,64);" +
		"__PostDecode();" +
		"branch_unconditional_immediate(branch_type,offset)"
	if compact := strings.Join(strings.Fields(decodeBody), ""); compact != wantDecodeBody {
		t.Fatalf("official ordinary BL decode body changed:\n--- have\n%s\n--- want\n%s",
			compact, wantDecodeBody)
	}

	// This is a source-route drift audit only. The pure projection below stops
	// before both state updates, and the Lean bridge makes no execution claim.
	executionBody, err := sailFunctionBody(aarch64, "branch_unconditional_immediate")
	if err != nil {
		t.Fatal(err)
	}
	wantExecutionBody := "ifbranch_type==BranchType_DIRCALLthen{" +
		"X(30)=PC()+4};" +
		"BranchTo(PC()+offset,branch_type)"
	if compact := strings.Join(strings.Fields(executionBody), ""); compact != wantExecutionBody {
		t.Fatalf("official ordinary BL execution route changed:\n--- have\n%s\n--- want\n%s",
			compact, wantExecutionBody)
	}

	projectionPath := filepath.Join("..", "spec", "sail", "arm_primitives.sail")
	projectionBytes, err := os.ReadFile(projectionPath)
	if err != nil {
		t.Fatal(err)
	}
	projection := string(projectionBytes)
	projectionBody, err := sailFunctionBody(projection, "decode64_ordinary_bl_immediate_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantProjectionBody := "letimm26:bits(26)=slice(op_code,0,26);" +
		"letop:bits(1)=slice(op_code,31,1);" +
		"letencoding_valid:bool=(op_code&0xFC000000)==0x94000000;" +
		"struct{encoding_valid=encoding_valid," +
		"target=DirectBranchImmediateExecutionTarget_DIRCALL," +
		"imm26=imm26,op=op,offset=branch26_offset_pure(imm26)}"
	if compact := strings.Join(strings.Fields(projectionBody), ""); compact != wantProjectionBody {
		t.Fatalf("local ordinary BL projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantProjectionBody)
	}

	defsPath := filepath.Join("..", "spec", "sail", "lean", "Out", "Defs.lean")
	defsBytes, err := os.ReadFile(defsPath)
	if err != nil {
		t.Fatal(err)
	}
	for _, fragment := range []string{
		"inductive DirectBranchImmediateExecutionTarget where | DirectBranchImmediateExecutionTarget_DIR | DirectBranchImmediateExecutionTarget_DIRCALL",
		"structure OrdinaryBImmediateDecode where",
	} {
		if count := strings.Count(string(defsBytes), fragment); count != 1 {
			t.Fatalf("generated %s contains %q %d times, want once", defsPath, fragment, count)
		}
	}
	leanPath := filepath.Join("..", "spec", "sail", "lean", "Out.lean")
	leanBytes, err := os.ReadFile(leanPath)
	if err != nil {
		t.Fatal(err)
	}
	for _, fragment := range []string{
		"def decode64_ordinary_bl_immediate_pure (op_code : (BitVec 32)) : OrdinaryBImmediateDecode :=",
		"let encoding_valid : Bool := ((op_code &&& 0xFC000000#32) == 0x94000000#32)",
		"target := DirectBranchImmediateExecutionTarget_DIRCALL\n    imm26 := imm26\n    op := op\n    offset := (branch26_offset_pure imm26)",
	} {
		if count := strings.Count(string(leanBytes), fragment); count != 1 {
			t.Fatalf("generated %s contains %q %d times, want once", leanPath, fragment, count)
		}
	}
}
