package asm

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

// The backend inlines wrapped but keeps its call to sum_to. Both callees
// qualify for finite applications, so merely checking whether each side
// contains an application cannot recover the common call boundary.
func partialInlineApplicationFixture(t *testing.T, machine, source string) (*Function, *ast.FunctionStatement) {
	t.Helper()
	const declaration = "caller: (n: u32) -> u32"
	unit, errs := ParseUnit("partial_inline.oakasm", declaration+" = {\n"+machine+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	fn := unit.Functions[0]
	fn.Callees = map[string]*ast.FunctionStatement{}
	for _, body := range []string{
		"sum_to: (n: u32) -> u32 { acc: u32 = u32(0)\n i: u32 = u32(0)\n while i < n { acc = acc + i\n i = i + u32(1) }\n acc }",
		"wrapped: (n: u32) -> u32 = sum_to(n)",
	} {
		callee, err := parseSignatureWithBody(body)
		if err != nil {
			t.Fatal(err)
		}
		fn.Callees[callee.Name.Value] = callee
	}
	sig, err := parseSignatureWithBody(declaration + " = " + source)
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(fn, sig, map[string]bool{"sum_to": true, "wrapped": true}); len(findings) != 0 {
		t.Fatalf("checker: %v", findings)
	}
	return fn, sig
}

// Pin actual execution separately from the opaque application model. In
// particular, a negative case must really change the source computation,
// rather than just produce an arbitrary application's countermodel.
func requirePartialInlineConcrete(t *testing.T, fn *Function, sig *ast.FunctionStatement, machineWant, sourceWant uint64) {
	t.Helper()
	env := map[string]uint64{"n": 4}
	machine, _, reason, ok := executeBodyChunk(fn, sig, env, 0, 0)
	if !ok || machine == nil || machine == trapPath {
		t.Fatalf("concrete machine execution: ok=%v reason=%s result=%v", ok, reason, machine)
	}
	lo := prepareLowering(fn, sig, env)
	source, reason, ok := lo.lower(sig.Body, 32)
	if !ok || source == nil || lo.witnessTrapped {
		t.Fatalf("concrete source execution: ok=%v reason=%s result=%v", ok, reason, source)
	}
	if theoremHasGeneralApplication(machine, []*term{source}) {
		t.Fatal("concrete execution retained an opaque call application")
	}
	if got := machine.eval(env) & mask(32); got != machineWant {
		t.Fatalf("machine at n=4: got %d, want %d", got, machineWant)
	}
	if got := source.eval(env) & mask(32); got != sourceWant {
		t.Fatalf("source at n=4: got %d, want %d", got, sourceWant)
	}
}

const partialInlineScalarMachine = `  bind w0 = n
  clobber x29, x30
  frame 16
  sub sp, sp, #16
  stp x29, x30, [sp]
  bl sum_to
  ldp x29, x30, [sp]
  add sp, sp, #16
  ret`

func TestFiniteCallApplicationPartialInlining(t *testing.T) {
	t.Setenv("OAK_VERIFY_CACHE", "0")
	fn, sig := partialInlineApplicationFixture(t, partialInlineScalarMachine, "wrapped(n)")
	requirePartialInlineConcrete(t, fn, sig, 6, 6)
	machine, exec, reason, ok := executeBodyChunk(fn, sig, nil, 0, 0)
	if !ok || exec == nil || len(exec.loops) != 0 || !theoremHasGeneralApplication(machine, nil) {
		t.Fatalf("expected a compact machine call without imported loops: ok=%v reason=%s", ok, reason)
	}
	lo := prepareLowering(fn, sig, nil)
	source, reason, ok := lo.lower(sig.Body, 32)
	if !ok || source == nil || source.kind != termApply || source.name != callApplicationName("wrapped", "") {
		t.Fatalf("unrestricted source lowering must expose the wrapper application: ok=%v reason=%s result=%v", ok, reason, source)
	}
	if verdict := Verify(fn, sig, sig.Body); verdict.Kind != VerdictProven {
		t.Errorf("inlining only the wrapper must prove: %s: %s", verdict.Kind, verdict.Message)
	}

	for _, test := range []struct {
		name, machine string
		want          uint64
	}{
		{"changed argument", strings.Replace(partialInlineScalarMachine, "  bl sum_to", "  add w0, w0, #1\n  bl sum_to", 1), 10},
		{"changed result", strings.Replace(partialInlineScalarMachine, "  bl sum_to", "  bl sum_to\n  add w0, w0, #1", 1), 7},
	} {
		t.Run(test.name, func(t *testing.T) {
			changed, source := partialInlineApplicationFixture(t, test.machine, "wrapped(n)")
			requirePartialInlineConcrete(t, changed, source, test.want, 6)
			// A scalar call abstraction may remain undecided, but cannot
			// turn this independently witnessed difference into a proof.
			if verdict := Verify(changed, source, source.Body); verdict.Kind == VerdictProven {
				t.Fatalf("changed partial inline must not prove: %s", verdict.Message)
			}
		})
	}
}

const partialInlineLoopSource = `{
  acc: u32 = u32(0)
  i: u32 = u32(0)
  while i < n {
    acc = wrapped(i)
    i = i + u32(1)
  }
  acc
}`

const partialInlineLoopMachine = `  bind w0 = n
  clobber x19, x20, x21, x29, x30
  frame 48
  sub sp, sp, #48
  stp x29, x30, [sp]
  stp x19, x20, [sp, #16]
  str x21, [sp, #32]
  mov w20, w0
  mov w19, #0
  mov w21, #0
loop:
  cmp w19, w20
  b.hs done
  mov w0, w19
  bl sum_to
  mov w21, w0
  add w19, w19, #1
  b loop
done:
  mov w0, w21
  ldr x21, [sp, #32]
  ldp x19, x20, [sp, #16]
  ldp x29, x30, [sp]
  add sp, sp, #48
  ret`

func TestFiniteCallApplicationPartialInliningInsideLoop(t *testing.T) {
	t.Setenv("OAK_VERIFY_CACHE", "0")
	fn, sig := partialInlineApplicationFixture(t, partialInlineLoopMachine, partialInlineLoopSource)
	requirePartialInlineConcrete(t, fn, sig, 3, 3)
	result, exec, reason, ok := executeBodyChunk(fn, sig, nil, 0, 0)
	if !ok || exec == nil || len(exec.loops) != 1 {
		t.Fatalf("expected one caller loop and no imported callee loops: ok=%v reason=%s", ok, reason)
	}
	if theoremHasGeneralApplication(result, exec.moreResults) {
		t.Fatal("fixture must hide its application behind the caller loop's result symbol")
	}
	hasApplication := false
	for _, next := range exec.loops[0].next {
		hasApplication = hasApplication || theoremHasGeneralApplication(next, nil)
	}
	if !hasApplication {
		t.Fatal("the machine loop's next values must contain the retained callee application")
	}
	if verdict := Verify(fn, sig, sig.Body); verdict.Kind != VerdictProven {
		t.Errorf("partial inlining inside a loop must prove: %s: %s", verdict.Kind, verdict.Message)
	}

	for _, test := range []struct {
		name, machine string
		want          uint64
	}{
		{"changed argument", strings.Replace(partialInlineLoopMachine, "  mov w0, w19", "  add w0, w19, #1", 1), 6},
		{"changed result", strings.Replace(partialInlineLoopMachine, "  mov w21, w0", "  add w21, w0, #1", 1), 4},
	} {
		t.Run(test.name, func(t *testing.T) {
			changed, source := partialInlineApplicationFixture(t, test.machine, partialInlineLoopSource)
			requirePartialInlineConcrete(t, changed, source, test.want, 3)
			// Loop verification executes the real bodies for its witnesses,
			// so these mutations must be actual mismatches, not evidence.
			if verdict := Verify(changed, source, source.Body); verdict.Kind != VerdictMismatch {
				t.Fatalf("changed partial inline must be refuted: %s: %s", verdict.Kind, verdict.Message)
			}
		})
	}
}

func TestFiniteCallApplicationPartialInliningRejectsExtraTrap(t *testing.T) {
	t.Setenv("OAK_VERIFY_CACHE", "0")
	machine := strings.Replace(partialInlineScalarMachine, "  sub sp, sp, #16", "  cmp w0, #4\n  b.eq trap\n  sub sp, sp, #16", 1) + "\ntrap:\n  brk #1"
	fn, sig := partialInlineApplicationFixture(t, machine, "wrapped(n)")
	env := map[string]uint64{"n": 4}
	result, _, reason, ok := executeBodyChunk(fn, sig, env, 0, 0)
	if !ok || result != trapPath {
		t.Fatalf("machine must trap at n=4: ok=%v reason=%s result=%v", ok, reason, result)
	}
	lo := prepareLowering(fn, sig, env)
	source, reason, ok := lo.lower(sig.Body, 32)
	if !ok || source == nil || lo.witnessTrapped || source.eval(env) != 6 {
		t.Fatalf("source must yield 6 at n=4: ok=%v reason=%s result=%v", ok, reason, source)
	}
	if verdict := Verify(fn, sig, sig.Body); verdict.Kind != VerdictMismatch {
		t.Fatalf("a machine-only trap must remain a mismatch after partial inlining: %s: %s", verdict.Kind, verdict.Message)
	}
}

func TestFiniteCallApplicationPartialInliningGlobalEffect(t *testing.T) {
	t.Setenv("OAK_VERIFY_CACHE", "0")
	template, _ := partialInlineApplicationFixture(t, partialInlineScalarMachine, "wrapped(n)")
	const declaration = "caller: (n: u32) -> ()"
	const source = "{\n  st = wrapped(n)\n}"
	machine := strings.Replace(partialInlineScalarMachine, "clobber x29, x30", "clobber x9, x29, x30", 1)
	machine = strings.Replace(machine, "  bl sum_to", "  bl sum_to\n  adrp x9, st\n  add x9, x9, :lo12:st\n  str w0, [x9]", 1)
	for _, changed := range []bool{false, true} {
		name := "matching store"
		if changed {
			name = "changed store value"
		}
		t.Run(name, func(t *testing.T) {
			body := machine
			if changed {
				body = strings.Replace(body, "  str w0, [x9]", "  add w0, w0, #1\n  str w0, [x9]", 1)
			}
			unit, errs := ParseUnit("partial_inline_effect.oakasm", declaration+" = {\n"+body+"\n}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			fn := unit.Functions[0]
			fn.Callees = template.Callees
			fn.Globals = map[string]Global{"st": {Type: "u32", Bits: 32}}
			sig, err := parseSignatureWithBody(declaration + " = " + source)
			if err != nil {
				t.Fatal(err)
			}
			if findings := Check(fn, sig, map[string]bool{"sum_to": true, "wrapped": true}); len(findings) != 0 {
				t.Fatalf("checker: %v", findings)
			}
			result, exec, reason, ok := executeBodyChunk(fn, sig, nil, 0, 0)
			if !ok || exec == nil || exec.hasResult || theoremHasGeneralApplication(result, exec.moreResults) || !theoremHasGeneralApplication(exec.cells["st"], nil) {
				t.Fatalf("unit caller must carry its application only in the global effect: ok=%v reason=%s", ok, reason)
			}
			env := map[string]uint64{"n": 4}
			_, concrete, reason, ok := executeBodyChunk(fn, sig, env, 0, 0)
			if !ok || concrete == nil {
				t.Fatalf("concrete unit caller: ok=%v reason=%s", ok, reason)
			}
			lo := prepareLowering(fn, sig, env)
			if reason, ok := lo.lowerUnitBody(sig.Body); !ok || lo.witnessTrapped {
				t.Fatalf("concrete source writer: ok=%v reason=%s", ok, reason)
			}
			stored, wanted := concrete.cells["st"], lo.writtenCells()["st"]
			machineWant := uint64(6)
			if changed {
				machineWant++
			}
			if stored == nil || wanted == nil || theoremHasGeneralApplication(stored, []*term{wanted}) || stored.eval(env) != machineWant || wanted.eval(env) != 6 {
				t.Fatalf("concrete stores at n=4 must be machine=%d and source=6: machine=%v source=%v", machineWant, stored, wanted)
			}
			verdict := Verify(fn, sig, sig.Body)
			if !changed && verdict.Kind != VerdictProven {
				t.Fatalf("matching partial-inline global effect must prove: %s: %s", verdict.Kind, verdict.Message)
			}
			if changed && verdict.Kind == VerdictProven {
				t.Fatalf("changed global store must not prove: %s", verdict.Message)
			}
		})
	}
}
