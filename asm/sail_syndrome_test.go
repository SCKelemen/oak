package asm

import (
	"fmt"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

// Complete declarations, including fields unused by the syndrome setter.
const sailSyndromeProcState = `struct ProcState = {
N : bits(1), Z : bits(1), C : bits(1), V : bits(1),
D : bits(1), A : bits(1), I : bits(1), F : bits(1),
PAN : bits(1), UAO : bits(1), DIT : bits(1), TCO : bits(1),
BTYPE : bits(2), SS : bits(1), IL : bits(1), EL : bits(2),
nRW : bits(1), SP : bits(1), Q : bits(1), GE : bits(4),
SSBS : bits(1), IT : bits(8), J : bits(1), T : bits(1), E : bits(1), M : bits(5)
}`

const sailSyndromeMakeVal = `val MakeLSInstructionSyndrome : forall 'size ('sign_extend : Bool) 'Rt ('sixty_four : Bool) ('acq_rel : Bool),
  ('size in {1, 2, 4, 8} & 0 <= 'Rt & 'Rt <= 31).
  (int('size), bool('sign_extend), int('Rt), bool('sixty_four), bool('acq_rel)) -> bits(11) effect {escape, undef}`
const sailSyndromeMake = `function MakeLSInstructionSyndrome (size, sign_extend, Rt, sixty_four, acq_rel) = {
assert(size == 1 | size == 2 | size == 4 | size == 8);
assert(0 <= Rt & Rt <= 31);
sz : bits(2) = undefined : bits(2);
match size {
1 => { sz = 0b00 },
2 => { sz = 0b01 },
4 => { sz = 0b10 },
8 => { sz = 0b11 }
};
let sz = sz;
let ext = if sign_extend then 0b1 else 0b0;
let sf = if sixty_four then 0b1 else 0b0;
let ar = if acq_rel then 0b1 else 0b0;
((((0b1 @ sz) @ ext) @ __GetSlice_int(5, Rt, 0)) @ sf) @ ar
}`
const sailSyndromeSetVal = `val AArch64_SetLSInstructionSyndrome : forall 'size 'Rt,
  ('size in {1, 2, 4, 8} & 0 <= 'Rt & 'Rt <= 31).
  (int('size), bool, int('Rt), bool, bool) -> unit effect {escape, rreg, undef, wreg}`
const sailSyndromeSet = `function AArch64_SetLSInstructionSyndrome (size, sign_extend, Rt, sixty_four, acq_rel) = {
if PSTATE.EL == EL0 | PSTATE.EL == EL1 then {
__LSISyndrome = MakeLSInstructionSyndrome(size, sign_extend, Rt, sixty_four, acq_rel)
}
}`

// Whitespace/comments may differ, but a declaration must be unique and match
// completely through the next top-level declaration. Checking only balanced
// braces would miss an appended expression/effect after the closing brace.
func auditSailSyndromeDeclaration(source, kind, name, want string) error {
	active, err := stripSailComments(source)
	if err != nil {
		return err
	}
	startPattern := regexp.MustCompile(`(?m)^` + regexp.QuoteMeta(kind) + `[ \t]+` + regexp.QuoteMeta(name) + `(?:[ \t\r\n]|\()`)
	starts := startPattern.FindAllStringIndex(active, -1)
	if len(starts) != 1 {
		return fmt.Errorf("%s %s declaration count = %d, want 1", kind, name, len(starts))
	}
	start := starts[0][0]
	tailStart := starts[0][1]
	next := regexp.MustCompile(`(?m)^(?:val|function|register|type|enum|struct|overload|let)[ \t]`).FindStringIndex(active[tailStart:])
	end := len(active)
	if next != nil {
		end = tailStart + next[0]
	}
	if got := compactSail(active[start:end]); got != compactSail(want) {
		return fmt.Errorf("%s %s changed: %s", kind, name, got)
	}
	return nil
}

func TestSailSyndromeProcStateExactAndMutated(t *testing.T) {
	audit := func(source string) error {
		return auditSailSyndromeDeclaration(source, "struct", "ProcState", sailSyndromeProcState)
	}
	checkSailMemorySourceGate(t, filepath.Join(filepath.Dir(sailArmModel), "aarch_types.sail"), audit,
		[]sailMemoryMutation{
			{"el_width", "EL : bits(2)", "EL : bits(1)"},
			{"unread_field_removed", "  TCO : bits(1),", ""},
			{"unread_field_width", "GE : bits(4)", "GE : bits(8)"},
			{"duplicate", "struct ProcState = {", "struct ProcState = {}\nstruct ProcState = {"},
		})
}

func TestSailSyndromeRegistersExactAndMutated(t *testing.T) {
	declarations := []struct{ kind, name, text string }{
		{"register", "PSTATE", "register PSTATE : ProcState"},
		{"register", "__LSISyndrome", "register __LSISyndrome : bits(11)"},
		{"let", "EL0", "let EL0 : bits(2) = 0b00"},
		{"let", "EL1", "let EL1 : bits(2) = 0b01"},
	}
	audit := func(source string) error {
		for _, d := range declarations {
			if err := auditSailSyndromeDeclaration(source, d.kind, d.name, d.text); err != nil {
				return err
			}
		}
		return nil
	}
	mutations := []sailMemoryMutation{
		{"wrong_state_type", "register PSTATE : ProcState", "register PSTATE : bits(2)"},
		{"wrong_syndrome_width", "register __LSISyndrome : bits(11)", "register __LSISyndrome : bits(12)"},
		{"wrong_el0", "let EL0 : bits(2) = 0b00", "let EL0 : bits(2) = 0b10"},
		{"wrong_el1", "let EL1 : bits(2) = 0b01", "let EL1 : bits(2) = 0b11"},
	}
	for _, d := range declarations {
		mutations = append(mutations,
			sailMemoryMutation{"duplicate_" + d.name, d.text, d.text + "\n" + d.text},
			sailMemoryMutation{"commented_" + d.name, d.text, "/* " + d.text + " */"})
	}
	checkSailMemorySourceGate(t, filepath.Join(filepath.Dir(sailArmModel), "aarch_mem.sail"), audit, mutations)
}

func checkSailSyndromeFunction(t *testing.T, name, signature, body string, mutations []sailMemoryMutation) {
	t.Helper()
	audit := func(source string) error {
		if err := auditSailSyndromeDeclaration(source, "val", name, signature); err != nil {
			return err
		}
		return auditSailSyndromeDeclaration(source, "function", name, body)
	}
	header := "function " + name + " (size, sign_extend, Rt, sixty_four, acq_rel) = {"
	mutations = append(mutations,
		sailMemoryMutation{"duplicate", header, header + "}\n" + header},
		sailMemoryMutation{"wrong_binders", header, strings.Replace(header, "size, sign_extend", "sign_extend, size", 1)},
		sailMemoryMutation{"commented_header", header, "/* " + header + " */"})
	checkSailMemorySourceGate(t, filepath.Join(filepath.Dir(sailArmModel), "aarch64.sail"), audit, mutations)
}

func TestSailSyndromeMakeExactAndMutated(t *testing.T) {
	checkSailSyndromeFunction(t, "MakeLSInstructionSyndrome", sailSyndromeMakeVal, sailSyndromeMake,
		[]sailMemoryMutation{
			{"size_domain", sailSyndromeMakeVal, strings.Replace(sailSyndromeMakeVal, "1, 2, 4, 8", "1, 2, 4, 8, 16", 1)},
			{"size_assert", "assert(size == 1 | size == 2 | size == 4 | size == 8);", "assert(true);"},
			{"rt_assert", "assert(0 <= Rt & Rt <= 31);", "assert(0 <= Rt & Rt <= 32);"},
			{"size_code", "sz = 0b11", "sz = 0b10"},
			{"initializer", "sz : bits(2) = undefined : bits(2);", "sz : bits(2) = 0b00;"},
			{"sign_flag", "let ext = if sign_extend then 0b1 else 0b0;", "let ext = if sign_extend then 0b0 else 0b1;"},
			{"sf_flag", "let sf = if sixty_four then 0b1 else 0b0;", "let sf = 0b0;"},
			{"ar_flag", "let ar = if acq_rel then 0b1 else 0b0;", "let ar = 0b1;"},
			{"valid_bit", "((((0b1 @ sz) @ ext)", "((((0b0 @ sz) @ ext)"},
			{"rt_slice", "__GetSlice_int(5, Rt, 0)", "__GetSlice_int(5, Rt, 1)"},
			{"trailing_effect", "@ sf) @ ar\n}", "@ sf) @ ar\n};\nthrow()"},
		})
}

func TestSailSyndromeSetExactAndMutated(t *testing.T) {
	checkSailSyndromeFunction(t, "AArch64_SetLSInstructionSyndrome", sailSyndromeSetVal, sailSyndromeSet,
		[]sailMemoryMutation{
			{"rt_domain", sailSyndromeSetVal, strings.Replace(sailSyndromeSetVal, "'Rt <= 31", "'Rt <= 32", 1)},
			{"el2_enabled", "if PSTATE.EL == EL0 | PSTATE.EL == EL1 then {", "if PSTATE.EL == EL0 | PSTATE.EL == EL2 then {"},
			{"all_levels", "if PSTATE.EL == EL0 | PSTATE.EL == EL1 then {", "if true then {"},
			{"and_guard", "if PSTATE.EL == EL0 | PSTATE.EL == EL1 then {", "if PSTATE.EL == EL0 & PSTATE.EL == EL1 then {"},
			{"wrong_destination", "__LSISyndrome = MakeLSInstructionSyndrome", "OTHER = MakeLSInstructionSyndrome"},
			{"wrong_rt", "__LSISyndrome = MakeLSInstructionSyndrome(size, sign_extend, Rt, sixty_four, acq_rel)", "__LSISyndrome = MakeLSInstructionSyndrome(size, sign_extend, 0, sixty_four, acq_rel)"},
			{"extra_effect", "__LSISyndrome = MakeLSInstructionSyndrome", "PSTATE.EL = EL0; __LSISyndrome = MakeLSInstructionSyndrome"},
			{"trailing_effect", "acq_rel)\n    }\n}", "acq_rel)\n    }\n};\nthrow()"},
		})
}
