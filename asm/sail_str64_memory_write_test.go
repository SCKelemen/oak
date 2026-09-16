package asm

import (
	"crypto/sha256"
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

type pinnedSailFunction struct {
	name       string
	source     string
	header     string
	bodySHA256 string
}

func exactSailFunctionStart(source, name string) (int, error) {
	pattern := regexp.MustCompile(`(?m)^function[ \t]+` + regexp.QuoteMeta(name) + `(?:[ \t\r\n]|\()`)
	starts := pattern.FindAllStringIndex(source, -1)
	if len(starts) != 1 {
		return -1, fmt.Errorf("official %s function header count = %d, want 1", name, len(starts))
	}
	return starts[0][0], nil
}

func sailDeclarationThroughOpen(source, name string) (string, error) {
	valMarker := "val " + name + " :"
	if count := strings.Count(source, valMarker); count != 1 {
		return "", fmt.Errorf("official %s val declaration count = %d, want 1", name, count)
	}
	start := strings.Index(source, valMarker)
	functionStart, err := exactSailFunctionStart(source, name)
	if err != nil {
		return "", err
	}
	if functionStart < start {
		return "", fmt.Errorf("official %s function header precedes its val declaration", name)
	}
	open := strings.IndexByte(source[functionStart:], '{')
	if open < 0 {
		return "", fmt.Errorf("official %s function header has no opening brace", name)
	}
	return compactSail(source[start : functionStart+open+1]), nil
}

func exactSailFunctionBodyAndClose(source, name string) (string, int, error) {
	functionStart, err := exactSailFunctionStart(source, name)
	if err != nil {
		return "", 0, err
	}
	open := strings.IndexByte(source[functionStart:], '{')
	if open < 0 {
		return "", 0, fmt.Errorf("official %s function header has no opening brace", name)
	}
	return sailBalancedBody(source, functionStart+open)
}

func exactSailFunctionBody(source, name string) (string, error) {
	body, _, err := exactSailFunctionBodyAndClose(source, name)
	return body, err
}

func compactSailHash(source string) string {
	sum := sha256.Sum256([]byte(compactSail(source)))
	return fmt.Sprintf("%x", sum)
}

func requirePinnedSailFunction(t *testing.T, function pinnedSailFunction) {
	t.Helper()
	header, err := sailDeclarationThroughOpen(function.source, function.name)
	if err != nil {
		t.Error(err)
	} else if header != function.header {
		t.Errorf("official %s signature/binders changed:\n--- have\n%s\n--- want\n%s",
			function.name, header, function.header)
	}
	body, err := exactSailFunctionBody(function.source, function.name)
	if err != nil {
		t.Error(err)
		return
	}
	if got := compactSailHash(body); got != function.bodySHA256 {
		t.Errorf("official %s normalized body hash = %s, want %s",
			function.name, got, function.bodySHA256)
	}
}

func requireCompactSailSlice(t *testing.T, source, description, want string) {
	t.Helper()
	if count := strings.Count(compactSail(source), want); count != 1 {
		t.Fatalf("official %s normalized count = %d, want 1", description, count)
	}
}

func requireExactSailStruct(t *testing.T, source, name, wantBody string) {
	t.Helper()
	pattern := regexp.MustCompile(`(?m)^struct[ \t]+` + regexp.QuoteMeta(name) + `[ \t]*=[ \t]*\{`)
	starts := pattern.FindAllStringIndex(source, -1)
	if len(starts) != 1 {
		t.Fatalf("official %s struct declaration count = %d, want 1", name, len(starts))
	}
	open := strings.IndexByte(source[starts[0][0]:starts[0][1]], '{')
	body, _, err := sailBalancedBody(source, starts[0][0]+open)
	if err != nil {
		t.Fatal(err)
	}
	if got := compactSail(body); got != wantBody {
		t.Fatalf("official %s struct changed:\n--- have\n%s\n--- want\n%s",
			name, got, wantBody)
	}
}

func requireImmediateSailOverload(t *testing.T, source, setter, overload, function string) {
	t.Helper()
	_, close, err := exactSailFunctionBodyAndClose(source, setter)
	if err != nil {
		t.Fatal(err)
	}
	tail := strings.TrimLeft(source[close+1:], " \t\r\n")
	lineEnd := strings.IndexAny(tail, "\r\n")
	if lineEnd < 0 {
		lineEnd = len(tail)
	}
	want := "overload" + overload + "={" + function + "}"
	if got := compactSail(tail[:lineEnd]); got != want {
		t.Fatalf("official overload %s = {%s} is not immediately after %s:\n--- have\n%s\n--- want\n%s",
			overload, function, setter, got, want)
	}
}

func requireExactSailValParagraph(t *testing.T, source, name, want string) {
	t.Helper()
	pattern := regexp.MustCompile(`(?m)^val[ \t]+` + regexp.QuoteMeta(name) + `[ \t]*(?::|=)`)
	starts := pattern.FindAllStringIndex(source, -1)
	if len(starts) != 1 {
		t.Fatalf("official %s val declaration count = %d, want 1", name, len(starts))
	}
	start := starts[0][0]
	end := strings.Index(source[start:], "\n\n")
	if end < 0 {
		t.Fatalf("official %s val declaration has no paragraph terminator", name)
	}
	if got := compactSail(source[start : start+end]); got != want {
		t.Fatalf("official %s val declaration changed:\n--- have\n%s\n--- want\n%s",
			name, got, want)
	}
}

func requireExactSailExpressionFunction(t *testing.T, source, name, want string) {
	t.Helper()
	pattern := regexp.MustCompile(`(?m)^function[ \t]+` + regexp.QuoteMeta(name) + `[^\r\n]*$`)
	lines := pattern.FindAllString(source, -1)
	if len(lines) != 1 {
		t.Fatalf("official %s expression-function count = %d, want 1", name, len(lines))
	}
	if got := compactSail(lines[0]); got != want {
		t.Fatalf("official %s expression-function changed:\n--- have\n%s\n--- want\n%s",
			name, got, want)
	}
}

// TestSailArmSTR64WriteMemoryArgumentsSource pins the conditional route from
// the already-audited STR64 Mem request to the arguments of the ordinary
// aligned size-eight __WriteMemory call. It does not assert that the route is
// reached, that __WriteMemory returns, that RAM changes, or that a CAT event is
// created.
func TestSailArmSTR64WriteMemoryArgumentsSource(t *testing.T) {
	modelDir := filepath.Dir(sailArmModel)
	readModel := func(name string) string {
		t.Helper()
		data, err := os.ReadFile(filepath.Join(modelDir, name))
		if err != nil {
			requireOracle(t, "sail-arm "+name+" not present: "+err.Error())
		}
		return string(data)
	}
	aarch64 := readModel("aarch64.sail")
	aarchMem := readModel("aarch_mem.sail")
	aarchTypes := readModel("aarch_types.sail")
	noDevices := readModel("no_devices.sail")
	sailJSON := readModel("sail.json")

	functions := []pinnedSailFunction{
		{name: "BigEndianReverse", source: aarchMem,
			header:     "valBigEndianReverse:forall('width:Int),'width>=0.bits('width)->bits('width)effect{escape}functionBigEndianReversevalue_name={",
			bodySHA256: "8a002622486be6c5b90c6bb7c2c1006323f2502b96d1c10f187d380b64f30301"},
		{name: "aset_Mem", source: aarch64,
			header:     "valaset_Mem:forall'size,8*'size>=0&'sizein{1,2,4,8,16}.(bits(64),int('size),AccType,bits(8*'size))->uniteffect{escape,rmem,rreg,undef,wmem,wreg}functionaset_Mem(address,size,acctype,value_name__arg)={",
			bodySHA256: "a4eb17ddec75f15fad56f8802ab7d5dba226ab37df2426b8f708fe713cfecf7c"},
		{name: "AArch64_aset_MemSingle", source: aarch64,
			header:     "valAArch64_aset_MemSingle:forall'size('wasaligned:Bool),'sizein{1,2,4,8,16}.(bits(64),int('size),AccType,bool('wasaligned),bits(8*'size))->uniteffect{escape,rmem,rreg,undef,wmem,wreg}functionAArch64_aset_MemSingle(address,size,acctype,wasaligned,value_name)={",
			bodySHA256: "a708491b7212b77b9ccd338ebb3d75a5b28b2d29a0d49d89f709a749dc240f52"},
		{name: "IsFault", source: aarchMem,
			header:     "valIsFault:AddressDescriptor->boolfunctionIsFaultaddrdesc={",
			bodySHA256: "341d15e8ab6497005b66222e8b381d7f8cf8e9da9889bf190c15f79f5174c7f4"},
		{name: "aset__Mem", source: aarchMem,
			header:     "valaset__Mem:forall('size:Int),'size>=0.(AddressDescriptor,int('size),AccessDescriptor,bits(8*'size))->uniteffect{escape,rmem,rreg,undef,wmem,wreg}functionaset__Mem(desc,size,accdesc,value_name)={",
			bodySHA256: "d76e7b010fd2860d322c34ee709737a36ff2c5f902bc8b6b6cc631b2ced581f6"},
		{name: "__WriteMemory", source: aarchMem,
			header:     "val__WriteMemory:forall('N:Int).(int('N),bits(56),bits(8*'N))->uniteffect{rreg,wmem}function__WriteMemory(N,address,val_name)={",
			bodySHA256: "33e76d698e110e33284c7a0f1ee26551cf0f4ed85bc392b6bb1994e63d29fed5"},
		{name: "__WriteRAM", source: noDevices,
			header:     "val__WriteRAM:forall'n'm.(atom('m),atom('n),bits('m),bits('m),bits(8*'n))->uniteffect{wmem}function__WriteRAM(addr_length,bytes,hex_ram,addr,data)={",
			bodySHA256: "82059e847198b4ec85ba1d05580d35e3ad894018f169a54f3ac2b9e1f3e68672"},
	}
	for _, function := range functions {
		t.Run(function.name, func(t *testing.T) {
			requirePinnedSailFunction(t, function)
		})
	}
	asetMemBody, err := exactSailFunctionBody(aarch64, "aset_Mem")
	if err != nil {
		t.Fatal(err)
	}
	memSingleBody, err := exactSailFunctionBody(aarch64, "AArch64_aset_MemSingle")
	if err != nil {
		t.Fatal(err)
	}
	asetPhysicalMemBody, err := exactSailFunctionBody(aarchMem, "aset__Mem")
	if err != nil {
		t.Fatal(err)
	}
	writeMemoryBody, err := exactSailFunctionBody(aarchMem, "__WriteMemory")
	if err != nil {
		t.Fatal(err)
	}

	requireExactSailStruct(t, aarchTypes, "FullAddress",
		"address:bits(52),NS:bits(1)")
	requireExactSailStruct(t, aarchTypes, "AddressDescriptor",
		"fault:FaultRecord,memattrs:MemoryAttributes,paddress:FullAddress,vaddress:bits(64)")
	requireImmediateSailOverload(t, aarch64, "aset_Mem", "Mem", "aset_Mem")
	requireImmediateSailOverload(t, aarch64, "AArch64_aset_MemSingle", "MemSingle",
		"AArch64_aset_MemSingle")
	requireImmediateSailOverload(t, aarchMem, "aset__Mem", "_Mem", "aset__Mem")
	requireExactSailValParagraph(t, noDevices, "___WriteRAM",
		`val___WriteRAM="write_ram":forall'n'm.(atom('m),atom('n),bits('m),bits('m),bits(8*'n))->uniteffect{wmem}`)
	requireExactSailValParagraph(t, noDevices, "__TraceMemoryWrite",
		"val__TraceMemoryWrite:forall'n'm.(atom('n),bits('m),bits(8*'n))->unit")
	requireExactSailExpressionFunction(t, noDevices, "__TraceMemoryWrite",
		"function__TraceMemoryWrite(bytes,addr,data)=()")

	wantModelFiles := compactSail(`{
    "options" : "-non_lexical_flow -no_lexp_bounds_check",
    "files" : [
        "prelude.sail",
        "no_devices.sail",
        "aarch_types.sail",
        "aarch_mem.sail",
        "aarch64.sail",
        "aarch64_float.sail",
        "aarch64_vector.sail",
        "aarch32.sail",
        "aarch_decode.sail"
    ]
}`)
	if got := compactSail(sailJSON); got != wantModelFiles {
		t.Fatalf("official Sail model file selection changed:\n--- have\n%s\n--- want\n%s",
			got, wantModelFiles)
	}

	requireCompactSailSlice(t, asetMemBody, "normal-store endian selection",
		"if(HaveNV2Ext()&acctype==AccType_NV2REGISTER)&[SCTLR_EL2[25]]==0b1|BigEndian()then{value_name=BigEndianReverse(value_name)}")
	requireCompactSailSlice(t, asetMemBody, "alignment decision",
		"aligned=AArch64_CheckAlignment(address,size,acctype,iswrite)")
	requireCompactSailSlice(t, asetMemBody, "aligned whole-value MemSingle call",
		"MemSingle(address,size,acctype,aligned)=value_name")
	requireCompactSailSlice(t, memSingleBody, "translated physical descriptor",
		"letmemaddrdesc=AArch64_TranslateAddress(address,acctype,iswrite,wasaligned,size)")
	requireCompactSailSlice(t, memSingleBody, "translation-fault abort",
		"ifIsFault(memaddrdesc)then{AArch64_Abort(address,memaddrdesc.fault)}")
	requireCompactSailSlice(t, memSingleBody, "shareable exclusive clear",
		"ifmemaddrdesc.memattrs.shareablethen{ClearExclusiveByAddress(memaddrdesc.paddress,ProcessorID(),size)}")
	requireCompactSailSlice(t, memSingleBody, "MTE tag-failure diversion",
		"if~(CheckTag(memaddrdesc,ptag,iswrite))then{TagCheckFail(ZeroExtend(address,64),iswrite)}")
	requireCompactSailSlice(t, memSingleBody, "translated _Mem assignment",
		"_Mem(memaddrdesc,size,accdesc)=value_name")
	requireCompactSailSlice(t, asetPhysicalMemBody, "physical-address projection",
		"paddress:bits(52)=desc.paddress.address")
	requireCompactSailSlice(t, asetPhysicalMemBody, "trickbox diversion",
		"if__trickbox_enabled&(paddress&__trickbox_mask_v8)==__trickbox_base_v8then{")
	requireCompactSailSlice(t, asetPhysicalMemBody, "counter-register diversion",
		"ifUInt(__CNTControlBase)!=0&(paddress&__CNTControlMask)==__CNTControlBasethen{")
	requireCompactSailSlice(t, asetPhysicalMemBody, "size-16 split first call",
		"__WriteMemory(8,ZeroExtend(paddress),slice(value_name,0,64))")
	requireCompactSailSlice(t, asetPhysicalMemBody, "ordinary direct write call",
		"__WriteMemory(size,ZeroExtend(paddress),value_name)")
	requireCompactSailSlice(t, writeMemoryBody, "RAM-width write call",
		"__WriteRAM(56,N,__defaultRAM,address,val_name)")

	projectionBytes, err := os.ReadFile(filepath.Join("..", "spec", "sail", "arm_primitives.sail"))
	if err != nil {
		t.Fatal(err)
	}
	projection := string(projectionBytes)
	reverseHeader, err := sailDeclarationThroughOpen(projection,
		"big_endian_reverse64_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantReverseHeader := "valbig_endian_reverse64_pure:bits(64)->bits(64)" +
		"functionbig_endian_reverse64_pure(value_name)={"
	if reverseHeader != wantReverseHeader {
		t.Fatalf("local 64-bit endian projection signature changed:\n--- have\n%s\n--- want\n%s",
			reverseHeader, wantReverseHeader)
	}
	reverseProjection, err := exactSailFunctionBody(projection, "big_endian_reverse64_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantReverseProjection := "slice(value_name,0,8)@slice(value_name,8,8)@" +
		"slice(value_name,16,8)@slice(value_name,24,8)@" +
		"slice(value_name,32,8)@slice(value_name,40,8)@" +
		"slice(value_name,48,8)@slice(value_name,56,8)"
	if got := compactSail(reverseProjection); got != wantReverseProjection {
		t.Fatalf("local 64-bit endian projection changed:\n--- have\n%s\n--- want\n%s",
			got, wantReverseProjection)
	}
	argumentsHeader, err := sailDeclarationThroughOpen(projection,
		"str64_aligned_normal_write_memory_arguments_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantArgumentsHeader := "valstr64_aligned_normal_write_memory_arguments_pure:" +
		"(bool,bits(52),bits(64))->(bits(56),bits(64))" +
		"functionstr64_aligned_normal_write_memory_arguments_pure" +
		"(big_endian,paddress,pre_mem_data)={"
	if argumentsHeader != wantArgumentsHeader {
		t.Fatalf("local __WriteMemory argument projection signature changed:\n--- have\n%s\n--- want\n%s",
			argumentsHeader, wantArgumentsHeader)
	}
	argumentsProjection, err := exactSailFunctionBody(projection,
		"str64_aligned_normal_write_memory_arguments_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantArgumentsProjection := "letwrite_data:bits(64)=ifbig_endianthen" +
		"big_endian_reverse64_pure(pre_mem_data)elsepre_mem_data;" +
		"(sail_zero_extend(paddress,56),write_data)"
	if got := compactSail(argumentsProjection); got != wantArgumentsProjection {
		t.Fatalf("local __WriteMemory argument projection changed:\n--- have\n%s\n--- want\n%s",
			got, wantArgumentsProjection)
	}
}
