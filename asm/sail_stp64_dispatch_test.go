package asm

import (
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

var sailSTP64DecodeHeader = regexp.MustCompile(
	`(?m)^function clause decode64 \(\(_ : bits\(1\) @ 0b010100100 @ _ : bits\(22\) as op_code\) ` +
		`if SEE < 1357\) = \{`,
)

// TestSailArmSTP64StoreRequestsSource ties Oak's pure offset-STP64 projection
// to the pinned official decoder and instruction body. It stops before either
// Mem request executes. In particular, it does not project execution or
// occurrence, ordering between the two requests, atomicity or non-tearing,
// alignment, endian behavior, translation, faults, tags, MMIO, physical
// writes, CAT events, barriers, or publication.
func TestSailArmSTP64StoreRequestsSource(t *testing.T) {
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
		if count := strings.Count(source, valMarker); count != 1 {
			t.Fatalf("official %s val declaration count = %d, want 1", name, count)
		}
		functionHeader := regexp.MustCompile(`(?m)^function[ \t]+` + regexp.QuoteMeta(name) + `[ \t\r\n]*\(`)
		functionHeaders := functionHeader.FindAllStringIndex(source, -1)
		if len(functionHeaders) != 1 {
			t.Fatalf("official %s function header count = %d, want 1", name, len(functionHeaders))
		}
		start := strings.Index(source, valMarker)
		functionStart := functionHeaders[0][0]
		if functionStart < start {
			t.Fatalf("official %s function header precedes its val declaration", name)
		}
		open := strings.IndexByte(source[functionStart:], '{')
		if open < 0 {
			t.Fatalf("official %s function header has no opening brace", name)
		}
		return compactSail(source[start : functionStart+open+1])
	}
	functionBody := func(source, name string) string {
		t.Helper()
		header := regexp.MustCompile(`(?m)^function[ \t]+` + regexp.QuoteMeta(name) + `[ \t\r\n]*\(`)
		headers := header.FindAllStringIndex(source, -1)
		if len(headers) != 1 {
			t.Fatalf("function %s header count = %d, want 1", name, len(headers))
		}
		open := strings.IndexByte(source[headers[0][0]:], '{')
		if open < 0 {
			t.Fatalf("function %s has no body", name)
		}
		open += headers[0][0]
		body, _, err := sailBalancedBody(source, open)
		if err != nil {
			t.Fatal(err)
		}
		return body
	}

	headers := sailSTP64DecodeHeader.FindAllStringIndex(decode, -1)
	if len(headers) != 1 {
		t.Fatalf("official SEE-1357 pair decode header count = %d, want 1", len(headers))
	}
	clause, _, err := sailBalancedBody(decode, headers[0][1]-1)
	if err != nil {
		t.Fatal(err)
	}
	wantClause := "SEE=1357;" +
		"Rt:bits(5)=op_code[4..0];" +
		"Rn:bits(5)=op_code[9..5];" +
		"Rt2:bits(5)=op_code[14..10];" +
		"imm7:bits(7)=op_code[21..15];" +
		"L:bits(1)=[op_code[22]];" +
		"V:bits(1)=[op_code[26]];" +
		"opc:bits(2)=op_code[31..30];" +
		"memory_pair_general_offset_memory_pair_general_postidx__decode(Rt,Rn,Rt2,imm7,L,V,opc)"
	if got := compactSail(clause); got != wantClause {
		t.Fatalf("official SEE-1357 pair decode clause changed:\n--- have\n%s\n--- want\n%s", got, wantClause)
	}

	const decoderName = "memory_pair_general_offset_memory_pair_general_postidx__decode"
	wantDecoderHeader := "val" + decoderName + ":" +
		"(bits(5),bits(5),bits(5),bits(7),bits(1),bits(1),bits(2))->" +
		"uniteffect{configuration,escape,rmem,rreg,undef,wmem,wreg}" +
		"function" + decoderName + "(Rt,Rn,Rt2,imm7,L,V,opc)={"
	if got := declarationThroughOpen(aarch64, decoderName); got != wantDecoderHeader {
		t.Fatalf("official offset-pair decoder signature/binders changed:\n--- have\n%s\n--- want\n%s",
			got, wantDecoderHeader)
	}
	decoder := functionBody(aarch64, decoderName)
	wantDecoder := "__unconditional=true;" +
		"letwback:bool=false;" +
		"letpostindex:bool=false;" +
		"let'n=UInt(Rn);" +
		"let't=UInt(Rt);" +
		"let't2=UInt(Rt2);" +
		"letacctype:AccType=AccType_NORMAL;" +
		"letmemop:MemOp=ifL==0b1thenMemOp_LOADelseMemOp_STORE;" +
		"if(L@[opc[0]])==0b01|opc==0b11then{throw(Error_Undefined())};" +
		"letsigned:bool=[opc[0]]!=0b0;" +
		"let'scale=2+UInt([opc[1]]);" +
		"let'datasize=shl_int(8,scale);" +
		"assert(constraint('datasizein{8,16,32,64}));" +
		"letoffset:bits(64)=LSL(SignExtend(imm7,64),scale);" +
		"__PostDecode();" +
		"memory_pair_general_postidx(acctype,datasize,memop,n,offset,postindex,signed,t,t2,wback)"
	if got := compactSail(decoder); got != wantDecoder {
		t.Fatalf("official offset-pair decoder changed:\n--- have\n%s\n--- want\n%s", got, wantDecoder)
	}

	const instructionName = "memory_pair_general_postidx"
	wantInstructionHeader := "val" + instructionName + ":" +
		"forall'datasize'n('postindex:Bool)('signed:Bool)'t't2('wback:Bool)," +
		"('n>=0&'n<=31|not(not('n==31)))&" +
		"('t>=0&'t<=31&'datasizein{8,16,32,64})&" +
		"('t2>=0&'t2<=31)." +
		"(AccType,int('datasize),MemOp,int('n),bits(64),bool('postindex)," +
		"bool('signed),int('t),int('t2),bool('wback))->" +
		"uniteffect{configuration,escape,rmem,rreg,undef,wmem,wreg}" +
		"function" + instructionName +
		"(acctype,datasize,memop,n,offset,postindex,signed,t,t2,wback__arg)={"
	if got := declarationThroughOpen(aarch64, instructionName); got != wantInstructionHeader {
		t.Fatalf("official pair instruction signature/binders changed:\n--- have\n%s\n--- want\n%s",
			got, wantInstructionHeader)
	}
	instruction := functionBody(aarch64, instructionName)
	pathStartMarker := "wback : bool = wback__arg;"
	pathEndMarker := "match memop {"
	if count := strings.Count(instruction, pathStartMarker); count != 1 {
		t.Fatalf("official pair wback initialization count = %d, want 1", count)
	}
	if count := strings.Count(instruction, pathEndMarker); count != 1 {
		t.Fatalf("official pair memop match count = %d, want 1", count)
	}
	pathStart := strings.Index(instruction, pathStartMarker)
	if prefix := strings.TrimSpace(instruction[:pathStart]); prefix != "" {
		t.Fatalf("official pair body has unpinned statements before wback initialization: %q", prefix)
	}
	pathEnd := strings.Index(instruction[pathStart:], pathEndMarker)
	if pathEnd < 0 {
		t.Fatal("official pair memop match precedes wback initialization")
	}
	pathEnd += pathStart + len(pathEndMarker)
	wantDecisivePath := "wback:bool=wback__arg;" +
		"address:bits(64)=undefined:bits(64);" +
		"data1:bits('datasize)=undefined:bits('datasize);" +
		"data2:bits('datasize)=undefined:bits('datasize);" +
		"let'dbytes:{'n,'n==div('datasize,8).int('n)}=datasize/8;" +
		"rt_unknown:bool=false;" +
		"ifHaveMTEExt()then{" +
		"letis_load_store=memop==MemOp_STORE|memop==MemOp_LOAD;" +
		"SetNotTagCheckedInstruction((is_load_store&n==31)&~(wback))};" +
		"wb_unknown:bool=false;" +
		"if((memop==MemOp_LOAD&wback)&(t==n|t2==n))&n!=31then{" +
		"letc=ConstrainUnpredictable(Unpredictable_WBOVERLAPLD);" +
		"assert(c==Constraint_WBSUPPRESS|c==Constraint_UNKNOWN|c==Constraint_UNDEF|c==Constraint_NOP);" +
		"matchc{" +
		"Constraint_WBSUPPRESS=>{wback=false}," +
		"Constraint_UNKNOWN=>{wb_unknown=true}," +
		"Constraint_UNDEF=>{throw(Error_Undefined())}," +
		"Constraint_NOP=>{EndOfInstruction()}}};" +
		"if((memop==MemOp_STORE&wback)&(t==n|t2==n))&n!=31then{" +
		"letc=ConstrainUnpredictable(Unpredictable_WBOVERLAPST);" +
		"assert(c==Constraint_NONE|c==Constraint_UNKNOWN|c==Constraint_UNDEF|c==Constraint_NOP);" +
		"matchc{" +
		"Constraint_NONE=>{rt_unknown=false}," +
		"Constraint_UNKNOWN=>{rt_unknown=true}," +
		"Constraint_UNDEF=>{throw(Error_Undefined())}," +
		"Constraint_NOP=>{EndOfInstruction()}}};" +
		"ifmemop==MemOp_LOAD&t==t2then{" +
		"letc=ConstrainUnpredictable(Unpredictable_LDPOVERLAP);" +
		"assert(c==Constraint_UNKNOWN|c==Constraint_UNDEF|c==Constraint_NOP);" +
		"matchc{" +
		"Constraint_UNKNOWN=>{rt_unknown=true}," +
		"Constraint_UNDEF=>{throw(Error_Undefined())}," +
		"Constraint_NOP=>{EndOfInstruction()}}};" +
		"ifn==31then{CheckSPAlignment();address=SP()}else{address=X(n)};" +
		"if~(postindex)then{address=address+offset};" +
		"matchmemop{"
	if got := compactSail(instruction[pathStart:pathEnd]); got != wantDecisivePath {
		t.Fatalf("official decisive offset-pair path changed:\n--- have\n%s\n--- want\n%s",
			got, wantDecisivePath)
	}

	storeHeader := regexp.MustCompile(`(?m)^[ \t]*MemOp_STORE[ \t]*=>[ \t]*\{`)
	storeHeaders := storeHeader.FindAllStringIndex(instruction, -1)
	if len(storeHeaders) != 1 {
		t.Fatalf("official pair MemOp_STORE arm count = %d, want 1", len(storeHeaders))
	}
	if got := compactSail(instruction[pathEnd:storeHeaders[0][1]]); got != "MemOp_STORE=>{" {
		t.Fatalf("official pair STORE arm is not the match's immediate first arm: %q", got)
	}
	storeArm, _, err := sailBalancedBody(instruction, storeHeaders[0][1]-1)
	if err != nil {
		t.Fatal(err)
	}
	wantStoreArm := "ifrt_unknown&t==nthen{" +
		"data1=undefined:bits('datasize)" +
		"}else{data1=X(t)};" +
		"ifrt_unknown&t2==nthen{" +
		"data2=undefined:bits('datasize)" +
		"}else{data2=X(t2)};" +
		"Mem(address+0,dbytes,acctype)=data1;" +
		"Mem(address+dbytes,dbytes,acctype)=data2"
	if got := compactSail(storeArm); got != wantStoreArm {
		t.Fatalf("official pair MemOp_STORE arm changed:\n--- have\n%s\n--- want\n%s", got, wantStoreArm)
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
	wantDecodeProjectionHeader := "valdecode64_stp64_offset_pure:" +
		"bits(32)->(bool,bits(5),bits(5),bits(5),bits(7))" +
		"functiondecode64_stp64_offset_pure(op_code)={"
	if got := declarationThroughOpen(projection, "decode64_stp64_offset_pure"); got != wantDecodeProjectionHeader {
		t.Fatalf("local STP64 decoder projection signature/binders changed:\n--- have\n%s\n--- want\n%s",
			got, wantDecodeProjectionHeader)
	}
	decodeProjection := functionBody(projection, "decode64_stp64_offset_pure")
	wantDecodeProjection := "letRt:bits(5)=slice(op_code,0,5);" +
		"letRn:bits(5)=slice(op_code,5,5);" +
		"letRt2:bits(5)=slice(op_code,10,5);" +
		"letimm7:bits(7)=slice(op_code,15,7);" +
		"if(op_code&0xFFC00000)==0xA9000000then{" +
		"(true,Rt,Rn,Rt2,imm7)" +
		"}else{(false,Rt,Rn,Rt2,imm7)}"
	if got := compactSail(decodeProjection); got != wantDecodeProjection {
		t.Fatalf("local STP64 decoder projection changed:\n--- have\n%s\n--- want\n%s",
			got, wantDecodeProjection)
	}

	wantRequestsProjectionHeader := "valstp64_offset_store_requests_pure:" +
		"(bits(5),bits(5),bits(5),bits(7),bits(64),bits(64),bits(64),bits(64))->" +
		"(bits(64),bits(64),bits(64),bits(64))" +
		"functionstp64_offset_store_requests_pure" +
		"(Rt,Rn,Rt2,imm7,rn_value,rt_value,rt2_value,sp_value)={"
	if got := declarationThroughOpen(projection, "stp64_offset_store_requests_pure"); got != wantRequestsProjectionHeader {
		t.Fatalf("local STP64 request projection signature/binders changed:\n--- have\n%s\n--- want\n%s",
			got, wantRequestsProjectionHeader)
	}
	requestsProjection := functionBody(projection, "stp64_offset_store_requests_pure")
	wantRequestsProjection := "letbase:bits(64)=ifRn==0b11111thensp_valueelsern_value;" +
		"letdata1:bits(64)=ifRt==0b11111thenZeros(64)elsert_value;" +
		"letdata2:bits(64)=ifRt2==0b11111thenZeros(64)elsert2_value;" +
		"letoffset:bits(64)=sail_shiftleft(sail_sign_extend(imm7,64),3);" +
		"letaddress1:bits(64)=base+offset;" +
		"letaddress2:bits(64)=address1+0x0000000000000008;" +
		"(address1,data1,address2,data2)"
	if got := compactSail(requestsProjection); got != wantRequestsProjection {
		t.Fatalf("local STP64 request projection changed:\n--- have\n%s\n--- want\n%s",
			got, wantRequestsProjection)
	}
}
