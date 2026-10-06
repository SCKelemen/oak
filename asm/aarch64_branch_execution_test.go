package asm

import (
	"fmt"
	"strings"
	"testing"
)

func aarch64FlagsLiteral(nzcv int) string {
	return fmt.Sprintf("⟨%t, %t, %t, %t⟩", nzcv&8 != 0, nzcv&4 != 0, nzcv&2 != 0, nzcv&1 != 0)
}

// Obtain every NZCV pattern through the real verifier's CCMP fallback, rather
// than synthesizing flags in the Lean oracle from a Go copy of the ARM table.
func aarch64ConstantFlags(nzcv int) *flagsFact {
	return &flagsFact{left: constTerm(0, 64), right: constTerm(0, 64), width: 64,
		cond: constTerm(0, 1), elseNZCV: int64(nzcv)}
}

// Use the production path executor's two distinct continuations. The label's
// item index is 3, and its byte address is 12 (labels occupy zero bytes).
func aarch64BranchContinuation(t *testing.T, instr Instruction, state *symbolicState) uint64 {
	t.Helper()
	out := Register{Class: ClassW, Num: 0, Lane: -1}
	x := pathExecutor{arch: ArchArm64, hasResult: true, resultClass: ClassW, resultReg: out,
		labels: map[string]int{"target": 3}, items: []Item{
			instr,
			Instruction{Mnemonic: "mov", Operands: []Operand{out, Immediate{Value: 17}}},
			Instruction{Mnemonic: "ret"},
			Label{Name: "target"},
			Instruction{Mnemonic: "mov", Operands: []Operand{out, Immediate{Value: 29}}},
			Instruction{Mnemonic: "ret"},
		}}
	result, _, reason, ok := x.runAll(state)
	if !ok || result == nil || result == trapPath {
		t.Fatalf("branch continuation failed: %s", reason)
	}
	return result.eval(nil)
}

func TestAArch64ConditionalExecutionMatchesLean(t *testing.T) {
	var examples []string
	// All sixteen conditions times all sixteen flags. The actual encoded
	// word, not a handwritten condition number, is checked by Lean's decoder.
	for low, code := range aarch64Cond19Conditions {
		instr := aarch64Cond19Instruction("bcond", low)
		word, rel, err := EncodeInstruction(instr, 0, map[string]int64{"target": 12})
		if err != nil || rel != nil {
			t.Fatalf("encoding %s: %v %+v", code, err, rel)
		}
		for nzcv := 0; nzcv < 16; nzcv++ {
			state := &symbolicState{arch: ArchArm64, regs: map[int]*term{}, flags: aarch64ConstantFlags(nzcv)}
			cond, reason, ok := branchCondition(instr, state)
			if !ok || cond == nil {
				t.Fatalf("%s/%d: %s", code, nzcv, reason)
			}
			decision := cond.eval(nil) != 0
			if decision != conditionFromFlags(code, nzcv&8 != 0, nzcv&4 != 0, nzcv&2 != 0, nzcv&1 != 0) {
				t.Fatalf("condition table/branch mismatch for %s/%d", code, nzcv)
			}
			result := aarch64BranchContinuation(t, instr, state)
			want := uint64(17)
			if decision {
				want = 29
			}
			if result != want {
				t.Fatalf("%s/%d: executor selected %d, want %d", code, nzcv, result, want)
			}
			examples = append(examples, fmt.Sprintf("example : (step 0x%08x#32 ⟨0, %s, fun _ => 0⟩).map (fun t => if t.isTaken then (29 : Nat) else 17) = some %d := by decide", word, aarch64FlagsLiteral(nzcv), result))
		}
	}
	// All W/X register numbers, including WZR/XZR, at width-sensitive values.
	values := []uint64{0, 1, 0x80000000, 0xffffffff, 0x100000000, 0x100000001, 0xffffffff00000000, 1 << 63, ^uint64(0)}
	for _, kind := range aarch64Cond19Kinds[1:] {
		for rt := 0; rt < 32; rt++ {
			instr := aarch64Cond19Instruction(kind, rt)
			word, rel, err := EncodeInstruction(instr, 0, map[string]int64{"target": 12})
			if err != nil || rel != nil {
				t.Fatalf("encoding %s/%d: %v %+v", kind, rt, err, rel)
			}
			for _, raw := range values {
				state := &symbolicState{arch: ArchArm64, regs: map[int]*term{rt: constTerm(raw, 64)}}
				cond, reason, ok := branchCondition(instr, state)
				if !ok || cond == nil {
					t.Fatalf("%s/%d/%x: %s", kind, rt, raw, reason)
				}
				value := raw
				if strings.HasSuffix(kind, "32") {
					value = uint64(uint32(value))
				}
				if rt == 31 {
					value = 0
				}
				wantTaken := value == 0
				if strings.HasPrefix(kind, "cbnz") {
					wantTaken = !wantTaken
				}
				if (cond.eval(nil) != 0) != wantTaken {
					t.Fatalf("wrong W/X/ZR predicate: %s/%d/%x", kind, rt, raw)
				}
				result := aarch64BranchContinuation(t, instr, state)
				examples = append(examples, fmt.Sprintf("example : (step 0x%08x#32 ⟨0, ⟨false, false, false, false⟩, fun _ => 0x%x#64⟩).map (fun t => if t.isTaken then (29 : Nat) else 17) = some %d := by decide", word, raw, result))
			}
		}
	}
	// Flag-condition aliases bind to their encoded bits and the verifier table.
	for alias, canonical := range map[string]string{"hs": "cs", "lo": "cc"} {
		for nzcv := 0; nzcv < 16; nzcv++ {
			if conditionFromFlags(alias, nzcv&8 != 0, nzcv&4 != 0, nzcv&2 != 0, nzcv&1 != 0) !=
				conditionFromFlags(canonical, nzcv&8 != 0, nzcv&4 != 0, nzcv&2 != 0, nzcv&1 != 0) {
				t.Fatalf("condition alias drift: %s", alias)
			}
		}
	}
	checkAArch64BranchLean(t, "AArch64BranchExecution", examples)
}

func TestAArch64ConditionalAlwaysWithoutFlags(t *testing.T) {
	for _, code := range []string{"al", "nv"} {
		for _, flags := range []*flagsFact{nil, {unknown: true}} {
			cond, reason, ok := branchCondition(Instruction{Mnemonic: "b.", Cond: code}, &symbolicState{flags: flags})
			if !ok || cond == nil || cond.kind != termConst || cond.value != 1 {
				t.Fatalf("b.%s requires flags: %s", code, reason)
			}
		}
		body := "  bind w0 = a\n  b." + code + " out\nout:\n  ret"
		v := verifyCase(t, "f: (a: u32) -> u32", "a", body)
		if v.Kind != VerdictProven {
			t.Fatalf("b.%s identity: %s: %s", code, v.Kind, v.Message)
		}
		wrong := verifyCase(t, "f: (a: u32) -> u32", "u32(0)", body)
		if wrong.Kind != VerdictMismatch {
			t.Fatalf("b.%s false fall-through contract: %s: %s", code, wrong.Kind, wrong.Message)
		}
		dead := "  bind w0 = a\n  b." + code + " out\n  mov w0, #0\nout:\n  ret"
		findings := checkBody(t, "f: (a: u32) -> u32", dead)
		if !strings.Contains(strings.Join(findings, "\n"), "unreachable instruction after an unconditional transfer") {
			t.Fatalf("b.%s must terminate the checker block: %v", code, findings)
		}
	}
	// Real flag predicates retain their preconditions.
	for _, code := range aarch64Cond19Conditions[:14] {
		for _, flags := range []*flagsFact{nil, {unknown: true}} {
			if _, _, ok := branchCondition(Instruction{Mnemonic: "b.", Cond: code}, &symbolicState{flags: flags}); ok {
				t.Fatalf("b.%s accepted missing/unknown flags", code)
			}
		}
	}
	if _, _, ok := branchCondition(aarch64Cond19Instruction("cbz64", 0), &symbolicState{regs: map[int]*term{}}); ok {
		t.Fatal("CBZ accepted an unbound ordinary register")
	}
}

func TestAArch64ConditionalSymbolicContinuations(t *testing.T) {
	for _, kind := range []string{"cbz32", "cbnz32", "cbz64", "cbnz64"} {
		reg, typ, cast := "x0", "u64", "a"
		if strings.HasSuffix(kind, "32") {
			reg, cast = "w0", "a & u64(0xffffffff)"
		}
		mnemonic := strings.TrimSuffix(strings.TrimSuffix(kind, "32"), "64")
		op := "=="
		if mnemonic == "cbnz" {
			op = "!="
		}
		body := fmt.Sprintf("(%s) %s u64(0) ? u64(29) | u64(17)", cast, op)
		machine := fmt.Sprintf("  bind x0 = a\n  %s %s, yes\n  mov x0, #17\n  ret\nyes:\n  mov x0, #29\n  ret", mnemonic, reg)
		v := verifyCase(t, "f: (a: "+typ+") -> u64", body, machine)
		if v.Kind != VerdictProven {
			t.Fatalf("symbolic %s: %s: %s", kind, v.Kind, v.Message)
		}
	}
}
