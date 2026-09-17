package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"strings"
	"testing"
)

func TestAArch64BRKLeanEncodingMatchesTable(t *testing.T) {
	var rows []isaEncoding
	for _, row := range isaEncodings {
		if row.Name == "BRK_EX_exception" {
			rows = append(rows, row)
		}
	}
	if len(rows) != 1 {
		t.Fatalf("BRK rows = %d, want one", len(rows))
	}
	row := rows[0]
	fields := []isaField{{"opc", 23, 3}, {"imm16", 20, 16}, {"op2", 4, 3}, {"LL", 1, 2}}
	if row.Mnemonic != "brk" || row.Value != 0xd4200000 || row.Mask != 0xffe0001f || !slices.Equal(row.Fields, fields) {
		t.Fatalf("BRK generated row drift: %+v", row)
	}
	if len(row.Forms) != 1 || len(row.Forms[0].Operands) != 1 || len(row.Forms[0].Defaults) != 0 {
		t.Fatalf("BRK forms drift: %+v", row.Forms)
	}
	imm := row.Forms[0].Operands[0]
	if imm.Kind != "imm" || !slices.Equal(imm.Fields, []string{"imm16"}) ||
		!imm.HasRange || imm.Min != 0 || imm.Max != 65535 || imm.Scale != 0 {
		t.Fatalf("BRK immediate drift: %+v", imm)
	}
	contents, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "AArch64BreakpointEncoding.lean"))
	if err != nil {
		t.Fatal(err)
	}
	block := regexp.MustCompile(`(?s)-- OAK-A64-BRK-ENC-BEGIN[^\n]*\n(.*?)-- OAK-A64-BRK-ENC-END`).FindAllStringSubmatch(string(contents), -1)
	want := `def brk : Encoding := ⟨"BRK_EX_exception", "brk", 0xd4200000#32, 0xffe0001f#32, [⟨"opc", 23, 3⟩, ⟨"imm16", 20, 16⟩, ⟨"op2", 4, 3⟩, ⟨"LL", 1, 2⟩]⟩`
	if len(block) != 1 || strings.TrimSpace(block[0][1]) != want {
		t.Fatalf("BRK Lean row differs from generated table: %v", block)
	}
}

func TestAArch64BRKAllImmediates(t *testing.T) {
	for value := int64(0); value < 1<<16; value++ {
		word, relocation, err := EncodeInstruction(Instruction{
			Mnemonic: "brk", Operands: []Operand{Immediate{Value: value}},
		}, 0, nil)
		want := uint32(0xd4200000) | uint32(value)<<5
		if err != nil || relocation != nil || word != want {
			t.Fatalf("BRK #%d = %#x, %+v, %v; want %#x", value, word, relocation, err, want)
		}
	}
	for _, value := range []int64{-1, 1 << 16, -1 << 63, 1<<63 - 1} {
		word, relocation, err := EncodeInstruction(Instruction{
			Mnemonic: "brk", Operands: []Operand{Immediate{Value: value}},
		}, 0, nil)
		if err == nil || word != 0 || relocation != nil {
			t.Fatalf("BRK accepted invalid immediate %d: %#x, %+v, %v", value, word, relocation, err)
		}
	}
}

// Exact source fixtures from the pinned Arm model. These retain the erased
// BTI/PostDecode/exception calls so a pure projection cannot silently acquire
// an architectural execution claim when the source route changes.
const sailBRKDecodeSource = `
val system_exceptions_debug_breakpoint_decode : (bits(2), bits(3), bits(16), bits(3)) -> unit effect {escape, rreg, undef, wreg}
function system_exceptions_debug_breakpoint_decode (LL, op2, imm16, opc) = {
    __unconditional = true;
    let comment = imm16;
    if HaveBTIExt() then { BTypeCompatible = true };
    __PostDecode();
    system_exceptions_debug_breakpoint(comment)
}
`

const sailBRKDispatchSource = `
val system_exceptions_debug_breakpoint : bits(16) -> unit effect {escape, rreg, undef, wreg}
function system_exceptions_debug_breakpoint comment = {
    AArch64_SoftwareBreakpoint(comment)
}
`

const sailSoftwareBreakpointSource = `
val AArch64_SoftwareBreakpoint : bits(16) -> unit effect {escape, rreg, undef, wreg}
function AArch64_SoftwareBreakpoint immediate = {
    let route_to_el2 = (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ([HCR_EL2[27]] == 0b1 | [MDCR_EL2[8]] == 0b1);
    let preferred_exception_return : bits(64) = ThisInstrAddr();
    let vect_offset = 0;
    exception : ExceptionRecord = undefined : ExceptionRecord;
    exception = ExceptionSyndrome(Exception_SoftwareBreakpoint);
    __tc1 : bits(25) = exception.syndrome;
    let __tc1 = __SetSlice_bits(25, 16, __tc1, 0, immediate);
    exception.syndrome = __tc1;
    if UInt(PSTATE.EL) > UInt(EL1) then {
        AArch64_TakeException(PSTATE.EL, exception, preferred_exception_return, vect_offset)
    } else {
        if route_to_el2 then {
            AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)
        } else {
            AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
        }
    }
}
`

const sailBreakpointSyndromeSource = `
val ExceptionSyndrome : Exception -> ExceptionRecord effect {undef}
function ExceptionSyndrome typ = {
    r : ExceptionRecord = undefined : ExceptionRecord;
    r.typ = typ;
    r.syndrome = Zeros();
    r.vaddress = Zeros();
    r.ipavalid = false;
    r.NS = 0b0;
    r.ipaddress = Zeros();
    r
}
`

func checkSailBreakpointFunction(source, fixture, name string) error {
	for _, part := range []struct {
		name string
		read func(string, string) (string, error)
	}{
		{"signature", sailDeclarationThroughOpen},
		{"body", exactSailFunctionBody},
	} {
		got, err := part.read(source, name)
		if err != nil {
			return err
		}
		want, err := part.read(fixture, name)
		if err != nil {
			return fmt.Errorf("invalid expected %s fixture: %w", name, err)
		}
		if compactSail(got) != compactSail(want) {
			return fmt.Errorf("%s %s drift: %s", name, part.name, got)
		}
	}
	return nil
}

func TestSailArmBRKDispatchSource(t *testing.T) {
	read := func(path string) string {
		t.Helper()
		data, err := os.ReadFile(path)
		if err != nil {
			requireOracle(t, "official Sail source not present: "+err.Error())
		}
		return string(data)
	}
	decode := read(sailArmModel)
	dir := filepath.Dir(sailArmModel)
	aarch64, memory := read(filepath.Join(dir, "aarch64.sail")), read(filepath.Join(dir, "aarch_mem.sail"))
	header := regexp.MustCompile(`(?m)^function clause decode64 \(\(0b11010100001 @ _ : bits\(16\) @ 0b00000 as op_code\) if SEE < 1747\) = \{`)
	active, err := stripSailComments(decode)
	if err != nil {
		t.Fatal(err)
	}
	clause, _, err := sailUniqueArm(active, header)
	if err != nil {
		t.Fatal(err)
	}
	wantClause := "SEE=1747;LL:bits(2)=op_code[1..0];op2:bits(3)=op_code[4..2];imm16:bits(16)=op_code[20..5];opc:bits(3)=op_code[23..21];system_exceptions_debug_breakpoint_decode(LL,op2,imm16,opc)"
	if compactSail(clause) != wantClause {
		t.Fatalf("official BRK decoder drift: %s", clause)
	}
	for _, test := range []struct{ source, fixture, name string }{
		{aarch64, sailBRKDecodeSource, "system_exceptions_debug_breakpoint_decode"},
		{aarch64, sailBRKDispatchSource, "system_exceptions_debug_breakpoint"},
		{aarch64, sailSoftwareBreakpointSource, "AArch64_SoftwareBreakpoint"},
		{memory, sailBreakpointSyndromeSource, "ExceptionSyndrome"},
	} {
		if err := checkSailBreakpointFunction(test.source, test.fixture, test.name); err != nil {
			t.Fatal(err)
		}
	}
	requireExactSailStruct(t, read(filepath.Join(dir, "aarch_types.sail")), "ExceptionRecord",
		"typ:Exception,syndrome:bits(25),vaddress:bits(64),ipavalid:bool,NS:bits(1),ipaddress:bits(52)")
	active, err = stripSailComments(memory)
	if err != nil {
		t.Fatal(err)
	}
	for _, constant := range []string{"letEL0:bits(2)=0b00", "letEL1:bits(2)=0b01", "letEL2:bits(2)=0b10"} {
		requireCompactSailSlice(t, active, "exception level", constant)
	}
	projection, err := os.ReadFile(filepath.Join("..", "spec", "sail", "arm_primitives.sail"))
	if err != nil {
		t.Fatal(err)
	}
	for _, test := range []struct{ name, want string }{
		{"decode64_brk_pure", "letimmediate:bits(16)=slice(op_code,5,16);letencoding_valid:bool=(op_code&0xFFE0001F)==0xD4200000;struct{encoding_valid=encoding_valid,immediate=immediate}"},
		{"software_breakpoint_arguments_pure", "letroute_to_el2=(el2_enabled&(current_el==0b00|current_el==0b01))&(slice(hcr_el2,27,1)==0b1|slice(mdcr_el2,8,1)==0b1);lettarget_el=ifUInt(current_el)>UInt(0b01)thencurrent_elelseifroute_to_el2then0b10else0b01;letsyndrome:bits(25)=Zeros(9)@immediate;struct{target_el=target_el,syndrome=syndrome,preferred_exception_return=this_instr_addr,vect_offset=0}"},
	} {
		body, err := exactSailFunctionBody(string(projection), test.name)
		if err != nil {
			t.Fatal(err)
		}
		if compactSail(body) != test.want {
			t.Fatalf("local %s projection drift: %s", test.name, body)
		}
	}
}

func TestSailBRKSourceGateRejectsMutations(t *testing.T) {
	for _, test := range []struct{ fixture, function, from, to string }{
		{sailSoftwareBreakpointSource, "AArch64_SoftwareBreakpoint", "EL2Enabled() &", "EL2Enabled() |"},
		{sailSoftwareBreakpointSource, "AArch64_SoftwareBreakpoint", "HCR_EL2[27]", "HCR_EL2[26]"},
		{sailSoftwareBreakpointSource, "AArch64_SoftwareBreakpoint", "MDCR_EL2[8]", "MDCR_EL2[9]"},
		{sailSoftwareBreakpointSource, "AArch64_SoftwareBreakpoint", "ThisInstrAddr()", "ThisInstrAddr() + 4"},
		{sailSoftwareBreakpointSource, "AArch64_SoftwareBreakpoint", "vect_offset = 0", "vect_offset = 4"},
		{sailSoftwareBreakpointSource, "AArch64_SoftwareBreakpoint", "Exception_SoftwareBreakpoint", "Exception_Breakpoint"},
		{sailSoftwareBreakpointSource, "AArch64_SoftwareBreakpoint", "__tc1, 0, immediate", "__tc1, 1, immediate"},
		{sailSoftwareBreakpointSource, "AArch64_SoftwareBreakpoint", "AArch64_TakeException(PSTATE.EL", "AArch64_TakeException(EL1"},
		{sailBRKDecodeSource, "system_exceptions_debug_breakpoint_decode", "__PostDecode();", ""},
		{sailBRKDecodeSource, "system_exceptions_debug_breakpoint_decode", "BTypeCompatible = true", "BTypeCompatible = false"},
		{sailBRKDispatchSource, "system_exceptions_debug_breakpoint", "AArch64_SoftwareBreakpoint(comment)", "AArch64_SoftwareBreakpoint(0x0000)"},
		{sailBreakpointSyndromeSource, "ExceptionSyndrome", "r.syndrome = Zeros()", "r.syndrome = Ones()"},
	} {
		t.Run(test.function+"/"+test.from, func(t *testing.T) {
			if err := checkSailBreakpointFunction(test.fixture, test.fixture, test.function); err != nil {
				t.Fatal(err)
			}
			mutant := strings.Replace(test.fixture, test.from, test.to, 1)
			if mutant == test.fixture {
				t.Fatal("vacuous mutation")
			}
			if err := checkSailBreakpointFunction(mutant, test.fixture, test.function); err == nil {
				t.Fatal("accepted changed exception source route")
			}
		})
	}
	for name, mutant := range map[string]string{
		"duplicate": sailSoftwareBreakpointSource + sailSoftwareBreakpointSource,
		"commented": "/*" + sailSoftwareBreakpointSource + "*/",
	} {
		t.Run(name, func(t *testing.T) {
			if err := checkSailBreakpointFunction(mutant, sailSoftwareBreakpointSource, "AArch64_SoftwareBreakpoint"); err == nil {
				t.Fatal("accepted ambiguous or inactive exception source")
			}
		})
	}
}
