package asm

import (
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

var sailSTR64DecodeHeader = regexp.MustCompile(
	`(?m)^function clause decode64 \(\(0b1 @ _ : bits\(1\) @ 0b11100100 @ _ : bits\(22\) as op_code\) ` +
		`if SEE < 1277\) = \{`,
)

func compactSail(source string) string {
	return strings.Join(strings.Fields(source), "")
}

// TestSailArmSTR64StoreRequestSource ties Oak's pure STR64 projection to the
// pinned official decoder and instruction body.  It intentionally stops at
// the virtual-address/data request to Mem: none of Mem's alignment, endian,
// translation, fault, tag, MMIO, physical-write, or concurrency behavior is
// projected by this test.
func TestSailArmSTR64StoreRequestSource(t *testing.T) {
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
	declarationThroughOpen := func(source, name string) string {
		t.Helper()
		valMarker := "val " + name + " :"
		functionMarker := "function " + name + " "
		if count := strings.Count(source, valMarker); count != 1 {
			t.Fatalf("official %s val declaration count = %d, want 1", name, count)
		}
		if count := strings.Count(source, functionMarker); count != 1 {
			t.Fatalf("official %s function header count = %d, want 1", name, count)
		}
		start := strings.Index(source, valMarker)
		functionStart := strings.Index(source[start:], functionMarker)
		if functionStart < 0 {
			t.Fatalf("official %s function header precedes its val declaration", name)
		}
		functionStart += start
		open := strings.IndexByte(source[functionStart:], '{')
		if open < 0 {
			t.Fatalf("official %s function header has no opening brace", name)
		}
		return compactSail(source[start : functionStart+open+1])
	}

	headers := sailSTR64DecodeHeader.FindAllStringIndex(decode, -1)
	if len(headers) != 1 {
		t.Fatalf("official SEE-1277 STR-family decode header count = %d, want 1", len(headers))
	}
	clause, _, err := sailBalancedBody(decode, headers[0][1]-1)
	if err != nil {
		t.Fatal(err)
	}
	wantClause := "SEE=1277;" +
		"Rt:bits(5)=op_code[4..0];" +
		"Rn:bits(5)=op_code[9..5];" +
		"imm12:bits(12)=op_code[21..10];" +
		"opc:bits(2)=op_code[23..22];" +
		"V:bits(1)=[op_code[26]];" +
		"size:bits(2)=op_code[31..30];" +
		"memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode(Rt,Rn,imm12,opc,V,size)"
	if got := compactSail(clause); got != wantClause {
		t.Fatalf("official SEE-1277 decode clause changed:\n--- have\n%s\n--- want\n%s", got, wantClause)
	}

	const decoderName = "memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode"
	wantDecoderHeader := "val" + decoderName + ":" +
		"(bits(5),bits(5),bits(12),bits(2),bits(1),bits(2))->" +
		"uniteffect{configuration,escape,rmem,rreg,undef,wmem,wreg}" +
		"function" + decoderName + "(Rt,Rn,imm12,opc,V,size)={"
	if got := declarationThroughOpen(aarch64, decoderName); got != wantDecoderHeader {
		t.Fatalf("official STR-family decoder signature/binders changed:\n--- have\n%s\n--- want\n%s",
			got, wantDecoderHeader)
	}
	decoder, err := sailFunctionBody(aarch64, decoderName)
	if err != nil {
		t.Fatal(err)
	}
	wantDecoder := "__unconditional=true;" +
		"letwback:bool=false;" +
		"letpostindex:bool=false;" +
		"let'scale=UInt(size);" +
		"letoffset:bits(64)=LSL(ZeroExtend(imm12,64),scale);" +
		"let'n=UInt(Rn);" +
		"let't=UInt(Rt);" +
		"letacctype:AccType=AccType_NORMAL;" +
		"memop:MemOp=undefined:MemOp;" +
		"signed:bool=undefined:bool;" +
		"regsize:int=64;" +
		"if[opc[1]]==0b0then{" +
		"memop=if[opc[0]]==0b1thenMemOp_LOADelseMemOp_STORE;" +
		"regsize=ifsize==0b11then64else32;" +
		"signed=false" +
		"}else{" +
		"ifsize==0b11then{" +
		"throw(Error_Undefined())" +
		"}else{" +
		"memop=MemOp_LOAD;" +
		"ifsize==0b10&[opc[0]]==0b1then{throw(Error_Undefined())};" +
		"regsize=if[opc[0]]==0b1then32else64;" +
		"signed=true}};" +
		"let'datasize=shl_int(8,scale);" +
		"letregsize=regsize;" +
		"letsigned=signed;" +
		"assert(regsize>=datasize);" +
		"assert(constraint('datasizein{8,16,32,64}));" +
		"__PostDecode();" +
		"memory_single_general_immediate_signed_postidx(acctype,datasize,memop,n,offset,postindex,regsize,signed,t,wback)"
	if got := compactSail(decoder); got != wantDecoder {
		t.Fatalf("official STR-family decoder changed:\n--- have\n%s\n--- want\n%s",
			got, wantDecoder)
	}

	const instructionName = "memory_single_general_immediate_signed_postidx"
	wantInstructionHeader := "val" + instructionName + ":" +
		"forall'datasize'n('postindex:Bool)'regsize('signed:Bool)'t('wback:Bool)," +
		"('n>=0&'n<=31|not(not('n==31)))&" +
		"('t>=0&'t<=31&'datasizein{8,16,32,64})." +
		"(AccType,int('datasize),MemOp,int('n),bits(64),bool('postindex)," +
		"int('regsize),bool('signed),int('t),bool('wback))->" +
		"uniteffect{configuration,escape,rmem,rreg,undef,wmem,wreg}" +
		"function" + instructionName +
		"(acctype,datasize,memop,n,offset,postindex,regsize,signed,t,wback__arg)={"
	if got := declarationThroughOpen(aarch64, instructionName); got != wantInstructionHeader {
		t.Fatalf("official STR instruction signature/binders changed:\n--- have\n%s\n--- want\n%s",
			got, wantInstructionHeader)
	}
	instruction, err := sailFunctionBody(aarch64, instructionName)
	if err != nil {
		t.Fatal(err)
	}
	pathStartMarker := "wback : bool = wback__arg;"
	pathEndMarker := "match memop {"
	if count := strings.Count(instruction, pathStartMarker); count != 1 {
		t.Fatalf("official wback initialization count = %d, want 1", count)
	}
	if count := strings.Count(instruction, pathEndMarker); count != 1 {
		t.Fatalf("official memop match count = %d, want 1", count)
	}
	pathStart := strings.Index(instruction, pathStartMarker)
	if prefix := strings.TrimSpace(instruction[:pathStart]); prefix != "" {
		t.Fatalf("official STR body has unpinned statements before wback initialization: %q", prefix)
	}
	pathEnd := strings.Index(instruction[pathStart:], pathEndMarker)
	if pathEnd < 0 {
		t.Fatal("official memop match precedes wback initialization")
	}
	pathEnd += pathStart + len(pathEndMarker)
	wantDecisivePath := "wback:bool=wback__arg;" +
		"ifHaveMTEExt()then{" +
		"letis_load_store=memop==MemOp_STORE|memop==MemOp_LOAD;" +
		"SetNotTagCheckedInstruction((is_load_store&n==31)&~(wback))};" +
		"address:bits(64)=undefined:bits(64);" +
		"data:bits('datasize)=undefined:bits('datasize);" +
		"wb_unknown:bool=false;" +
		"rt_unknown:bool=false;" +
		"c:Constraint=undefined:Constraint;" +
		"if((memop==MemOp_LOAD&wback)&n==t)&n!=31then{" +
		"c=ConstrainUnpredictable(Unpredictable_WBOVERLAPLD);" +
		"assert(c==Constraint_WBSUPPRESS|c==Constraint_UNKNOWN|c==Constraint_UNDEF|c==Constraint_NOP);" +
		"matchc{" +
		"Constraint_WBSUPPRESS=>{wback=false}," +
		"Constraint_UNKNOWN=>{wb_unknown=true}," +
		"Constraint_UNDEF=>{throw(Error_Undefined())}," +
		"Constraint_NOP=>{EndOfInstruction()}}};" +
		"if((memop==MemOp_STORE&wback)&n==t)&n!=31then{" +
		"c=ConstrainUnpredictable(Unpredictable_WBOVERLAPST);" +
		"assert(c==Constraint_NONE|c==Constraint_UNKNOWN|c==Constraint_UNDEF|c==Constraint_NOP);" +
		"matchc{" +
		"Constraint_NONE=>{rt_unknown=false}," +
		"Constraint_UNKNOWN=>{rt_unknown=true}," +
		"Constraint_UNDEF=>{throw(Error_Undefined())}," +
		"Constraint_NOP=>{EndOfInstruction()}}};" +
		"ifn==31then{ifmemop!=MemOp_PREFETCHthen{CheckSPAlignment()};address=SP()}else{address=X(n)};" +
		"if~(postindex)then{address=address+offset};" +
		"matchmemop{"
	if got := compactSail(instruction[pathStart:pathEnd]); got != wantDecisivePath {
		t.Fatalf("official decisive STR path changed:\n--- have\n%s\n--- want\n%s",
			got, wantDecisivePath)
	}

	storeHeader := regexp.MustCompile(`(?m)^[ \t]*MemOp_STORE[ \t]*=>[ \t]*\{`)
	storeHeaders := storeHeader.FindAllStringIndex(instruction, -1)
	if len(storeHeaders) != 1 {
		t.Fatalf("official MemOp_STORE arm count = %d, want 1", len(storeHeaders))
	}
	if got := compactSail(instruction[pathEnd:storeHeaders[0][1]]); got != "MemOp_STORE=>{" {
		t.Fatalf("official STORE arm is not the match's immediate first arm: %q", got)
	}
	storeArm, _, err := sailBalancedBody(instruction, storeHeaders[0][1]-1)
	if err != nil {
		t.Fatal(err)
	}
	wantStoreArm := "ifrt_unknownthen{data=undefined:bits('datasize)}else{data=X(t)};" +
		"if~(wback)then{" +
		"AArch64_SetLSInstructionSyndrome(datasize/8,false,t,regsize==64,false)};" +
		"Mem(address,datasize/8,acctype)=data"
	if got := compactSail(storeArm); got != wantStoreArm {
		t.Fatalf("official MemOp_STORE arm changed:\n--- have\n%s\n--- want\n%s",
			got, wantStoreArm)
	}

	getterStartMarker := "val aget_X :"
	getterEndMarker := "overload X = {aget_X}"
	if count := strings.Count(aarch64, getterStartMarker); count != 1 {
		t.Fatalf("official aget_X signature count = %d, want 1", count)
	}
	if count := strings.Count(aarch64, getterEndMarker); count != 1 {
		t.Fatalf("official X-getter overload count = %d, want 1", count)
	}
	getterStart := strings.Index(aarch64, getterStartMarker)
	getterEnd := strings.Index(aarch64[getterStart:], getterEndMarker)
	if getterEnd < 0 {
		t.Fatal("official X-getter overload precedes its signature")
	}
	getterEnd += getterStart + len(getterEndMarker)
	wantGetterRoute := "valaget_X:forall'width'n," +
		"('n>=0&'n<=31&'widthin{8,16,32,64})." +
		"(implicit('width),int('n))->bits('width)effect{rreg}" +
		"functionaget_X(width,n)=ifn!=31thenslice(_R[n],0,width)elseZeros(width)" +
		"overloadX={aget_X}"
	if got := compactSail(aarch64[getterStart:getterEnd]); got != wantGetterRoute {
		t.Fatalf("official X-register getter route changed:\n--- have\n%s\n--- want\n%s",
			got, wantGetterRoute)
	}

	projectionBytes, err := os.ReadFile(filepath.Join("..", "spec", "sail", "arm_primitives.sail"))
	if err != nil {
		t.Fatal(err)
	}
	projection := string(projectionBytes)
	decodeProjection, err := sailFunctionBody(projection, "decode64_str64_unsigned_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantDecodeProjection := "letRt:bits(5)=slice(op_code,0,5);" +
		"letRn:bits(5)=slice(op_code,5,5);" +
		"letimm12:bits(12)=slice(op_code,10,12);" +
		"if(op_code&0xFFC00000)==0xF9000000then{(true,Rt,Rn,imm12)}else{(false,Rt,Rn,imm12)}"
	if got := compactSail(decodeProjection); got != wantDecodeProjection {
		t.Fatalf("local STR64 decoder projection changed:\n--- have\n%s\n--- want\n%s",
			got, wantDecodeProjection)
	}
	requestProjection, err := sailFunctionBody(projection, "str64_unsigned_store_request_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantRequestProjection := "letbase:bits(64)=ifRn==0b11111thensp_valueelsern_value;" +
		"letdata:bits(64)=ifRt==0b11111thenZeros(64)elsert_value;" +
		"letoffset:bits(64)=sail_shiftleft(sail_zero_extend(imm12,64),3);" +
		"(base+offset,data)"
	if got := compactSail(requestProjection); got != wantRequestProjection {
		t.Fatalf("local STR64 request projection changed:\n--- have\n%s\n--- want\n%s",
			got, wantRequestProjection)
	}
}
