package asm

import (
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

const sailOrdinaryRETWord = uint32(0xd65f03c0)

var sailOrdinaryRETDecodeHeader = regexp.MustCompile(
	`(?m)^function clause decode64 \(\(0b1101011001011111000000 @ _ : bits\(5\) @ 0b00000 as op_code\) if SEE < 1522\) = \{`,
)

// TestSailArmOrdinaryRETDispatchSource ties Oak's canonical operandless RET
// word and generated pure projection to the pinned official Arm decoder and
// BranchType_RET call route. It proves no register value/provenance, target
// validity, PostDecode behavior, ABI return discipline, or BranchTo effect.
func TestSailArmOrdinaryRETDispatchSource(t *testing.T) {
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
		if class.mask == 0xfffffc1f && class.value == 0xd65f0000 &&
			class.fn == "branch_unconditional_register" {
			classMatches++
		}
	}
	if classMatches != 1 {
		t.Fatalf("ordinary RET decode class count = %d, want 1", classMatches)
	}

	officialClause, _, err := sailUniqueArm(decode, sailOrdinaryRETDecodeHeader)
	if err != nil {
		t.Fatal(err)
	}
	wantOfficialClause := "SEE=1522;" +
		"Rm:bits(5)=op_code[4..0];" +
		"Rn:bits(5)=op_code[9..5];" +
		"M:bits(1)=[op_code[10]];" +
		"A:bits(1)=[op_code[11]];" +
		"op2:bits(5)=op_code[20..16];" +
		"op:bits(2)=op_code[22..21];" +
		"Z:bits(1)=[op_code[24]];" +
		"branch_unconditional_register_decode(Rm,Rn,M,A,op2,op,Z)"
	if compact := strings.Join(strings.Fields(officialClause), ""); compact != wantOfficialClause {
		t.Fatalf("official ordinary RET decode clause changed:\n--- have\n%s\n--- want\n%s",
			compact, wantOfficialClause)
	}

	decodeBody, err := sailFunctionBody(aarch64, "branch_unconditional_register_decode")
	if err != nil {
		t.Fatal(err)
	}
	wantDecodeBody := "__unconditional=true;" +
		"n:int=UInt(Rn);" +
		"branch_type:BranchType=undefined:BranchType;" +
		"let'm=UInt(Rm);" +
		"letpac:bool=A==0b1;" +
		"letuse_key_a:bool=M==0b0;" +
		"source_is_sp:bool=Z==0b1&m==31;" +
		"if~(pac)&m!=0then{throw(Error_Undefined())}else{" +
		"ifpac&~(HavePACExt())then{throw(Error_Undefined())}};" +
		"matchop{" +
		"0b00=>{branch_type=BranchType_INDIR}," +
		"0b01=>{branch_type=BranchType_INDCALL}," +
		"0b10=>{branch_type=BranchType_RET}," +
		"_=>{throw(Error_Undefined())}};" +
		"ifpacthen{" +
		"ifZ==0b0&m!=31then{throw(Error_Undefined())};" +
		"ifbranch_type==BranchType_RETthen{" +
		"ifn!=31then{throw(Error_Undefined())};" +
		"n=30;source_is_sp=true}};" +
		"__PostDecode();" +
		"let'n=n;" +
		"assert(constraint((0<='n&'n<=31)));" +
		"branch_unconditional_register(branch_type,m,n,pac,source_is_sp,use_key_a)"
	if compact := strings.Join(strings.Fields(decodeBody), ""); compact != wantDecodeBody {
		t.Fatalf("official ordinary RET decode body changed:\n--- have\n%s\n--- want\n%s",
			compact, wantDecodeBody)
	}

	executionBody, err := sailFunctionBody(aarch64, "branch_unconditional_register")
	if err != nil {
		t.Fatal(err)
	}
	wantExecutionBody := "target:bits(64)=X(n);" +
		"matchbranch_type{" +
		"BranchType_INDIR=>{" +
		"ifInGuardedPagethen{" +
		"ifn==16|n==17then{BTypeNext=0b01}else{BTypeNext=0b11}" +
		"}else{BTypeNext=0b01}}," +
		"BranchType_INDCALL=>{BTypeNext=0b10}," +
		"BranchType_RET=>{BTypeNext=0b00}};" +
		"ifpacthen{" +
		"letmodifier:bits(64)=ifsource_is_spthenSP()elseX(m);" +
		"ifuse_key_athen{target=AuthIA(target,modifier)}else{" +
		"target=AuthIB(target,modifier)}};" +
		"ifbranch_type==BranchType_INDCALLthen{X(30)=PC()+4};" +
		"BranchTo(target,branch_type)"
	if compact := strings.Join(strings.Fields(executionBody), ""); compact != wantExecutionBody {
		t.Fatalf("official ordinary RET execution route changed:\n--- have\n%s\n--- want\n%s",
			compact, wantExecutionBody)
	}

	projectionPath := filepath.Join("..", "spec", "sail", "arm_primitives.sail")
	projectionBytes, err := os.ReadFile(projectionPath)
	if err != nil {
		t.Fatal(err)
	}
	projectionBody, err := sailFunctionBody(string(projectionBytes), "decode64_ordinary_ret_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantProjectionBody := "letRm:bits(5)=slice(op_code,0,5);" +
		"letRn:bits(5)=slice(op_code,5,5);" +
		"letM:bits(1)=slice(op_code,10,1);" +
		"letA:bits(1)=slice(op_code,11,1);" +
		"letop2:bits(5)=slice(op_code,16,5);" +
		"letop:bits(2)=slice(op_code,21,2);" +
		"letZ:bits(1)=slice(op_code,24,1);" +
		"letpac:bool=A==0b1;" +
		"letsource_is_sp:bool=Z==0b1&Rm==0b11111;" +
		"letuse_key_a:bool=M==0b0;" +
		"letencoding_valid:bool=(op_code&0xFFFFFC1F)==0xD65F0000;" +
		"letpre_postdecode_checks_pass:bool=encoding_valid&~(pac)&" +
		"Rm==0b00000&op==0b10;" +
		"struct{encoding_valid=encoding_valid," +
		"pre_postdecode_checks_pass=pre_postdecode_checks_pass," +
		"target=BranchRegisterExecutionTarget_RET,Rm=Rm,Rn=Rn,M=M,A=A," +
		"op2=op2,op=op,Z=Z,pac=pac,source_is_sp=source_is_sp," +
		"use_key_a=use_key_a}"
	if compact := strings.Join(strings.Fields(projectionBody), ""); compact != wantProjectionBody {
		t.Fatalf("local ordinary RET projection drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantProjectionBody)
	}

	defsPath := filepath.Join("..", "spec", "sail", "lean", "Out", "Defs.lean")
	defsBytes, err := os.ReadFile(defsPath)
	if err != nil {
		t.Fatal(err)
	}
	for _, fragment := range []string{
		"inductive BranchRegisterExecutionTarget where | BranchRegisterExecutionTarget_RET",
		"structure OrdinaryRETDecode where",
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
		"def decode64_ordinary_ret_pure (op_code : (BitVec 32)) : OrdinaryRETDecode :=",
		"let encoding_valid : Bool := ((op_code &&& 0xFFFFFC1F#32) == 0xD65F0000#32)",
		"target := BranchRegisterExecutionTarget_RET",
	} {
		if count := strings.Count(string(leanBytes), fragment); count != 1 {
			t.Fatalf("generated %s contains %q %d times, want once", leanPath, fragment, count)
		}
	}

	// The canonical word itself is pinned by the hand-encoding module and its
	// generated-table test. This source audit only asserts its static decode.
	if sailOrdinaryRETWord != 0xd65f03c0 {
		t.Fatalf("ordinary RET word = %#08x", sailOrdinaryRETWord)
	}
}
