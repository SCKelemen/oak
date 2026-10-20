package compiler

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
)

// This test passes complete final production ELF objects directly to Lean.
// There is no Go ELF extraction or producer-supplied function extent. Its finite
// compiler witnesses exercise the strict named-object/flat-section-loader model;
// they neither prove original-source semantics nor change production authority.
func TestNativeBitwiseObjectLean(t *testing.T) {
	lake := findLake()
	if lake == "" {
		if os.Getenv("OAK_REQUIRE_NATIVE_OBJECT_LEAN") == "1" {
			t.Fatal("OAK_REQUIRE_NATIVE_OBJECT_LEAN=1 requires lake")
		}
		t.Skip("lake unavailable; formal CI requires complete native-object kernel checks")
	}
	root, err := filepath.Abs(filepath.Join("..", "spec", "lean"))
	if err != nil {
		t.Fatal(err)
	}
	run := func(limit time.Duration, args ...string) string {
		t.Helper()
		ctx, cancel := context.WithTimeout(t.Context(), limit)
		defer cancel()
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = root
		cmd.WaitDelay = 5 * time.Second
		started := time.Now()
		output, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("lake %v failed after %s (context: %v): %v\n%s", args, time.Since(started), ctx.Err(), err, output)
		}
		t.Logf("lake %v completed in %s", args, time.Since(started))
		return string(output)
	}
	// Build this model's closure only, never the repository-wide default target.
	run(4*time.Minute, "build", "Oak.NativeBitwiseObject")

	const preamble = `import Oak.NativeBitwiseObject
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
open Oak Oak.NativeBitwiseObject
open Oak.MinimalELF (Bytes)
namespace CurrentNativeObjects
`
	list := func(b []byte) string { return strings.Replace(wasmLeanArray(b), "#[", "[", 1) }
	families := []struct{ name, first, second string }{
		{"bitwise", "x", "y"},
		{"Mix9", "left0", "Right9"},
	}
	operations := []struct{ name, token, other string }{
		{"and", "&", "or"}, {"or", "|", "xor"}, {"xor", "^", "and"},
	}
	lanes := []struct{ arch, machine, wrongMachine string }{
		{target.ArchArm64, "arm64", "rv64"},
		{target.ArchRiscv64, "rv64", "arm64"},
	}
	directory := t.TempDir()
	objects, refusals, audited := 0, 0, 0
	for _, lane := range lanes {
		for familyIndex, family := range families {
			for _, op := range operations {
				id := lane.arch + "_" + family.name + "_" + op.name
				var proof strings.Builder
				proof.WriteString(preamble)
				expectedAudits := map[string]bool{}
				original := fmt.Sprintf("%s: (%s: u32, %s: u32): u32 = %s %s %s\n", family.name, family.first, family.second, family.first, op.token, family.second)
				object, err := New().WithSource(id+".oak", original).
					WithTarget(target.Target{OS: target.OSLinux, Arch: lane.arch}).EmitNativeObject(asm.ELF).Get()
				if err != nil {
					t.Fatalf("%s production native object: %v", id, err)
				}
				if len(object) == 0 {
					t.Fatalf("%s emitted an empty object", id)
				}
				fmt.Fprintf(&proof, "namespace %s\ndef source : List UInt8 := %s\ndef name : Bytes := fromUInt8 %s\ndef image : Bytes := fromUInt8 %s\n", id, list([]byte(original)), list([]byte(family.name)), list(object))
				body := func(operation string) string {
					if lane.machine == "arm64" {
						return fmt.Sprintf("(fromUInt8 (AArch64BitwiseFunction.functionBytes .%s))", operation)
					}
					return fmt.Sprintf("(RiscVFramedBitwise.functionBytes .%s)", operation)
				}
				fmt.Fprintf(&proof, "theorem admitted : accepts .%s name image %s = true := by decide +kernel\n", lane.machine, body(op.name))
				// Independently modify the complete emitted image or the requested
				// target/name/body. Every refusal retains the original other inputs.
				wrongName := list([]byte(families[1-familyIndex].name))
				changedFlags := 1
				if lane.machine == "rv64" {
					changedFlags = 5 // LP64D flags=4 plus forbidden RVC.
				}
				controls := []struct{ name, machine, nameBytes, image, body string }{
					{"wrong_name", lane.machine, "(fromUInt8 " + wrongName + ")", "image", body(op.name)},
					{"nul_name", lane.machine, "(name ++ [0,120])", "image", body(op.name)},
					{"wrong_op", lane.machine, "name", "image", body(op.other)},
					{"wrong_target", lane.wrongMachine, "name", "image", body(op.name)},
					{"append_zero", lane.machine, "name", "(image ++ [0])", body(op.name)},
					{"truncate", lane.machine, "name", "(image.take (image.length - 1))", body(op.name)},
					{"body_byte", lane.machine, "name", "(image.set 64 ((image.getD 64 0) ^^^ 1))", body(op.name)},
					{"flags", lane.machine, "name", fmt.Sprintf("(image.set 48 %d)", changedFlags), body(op.name)},
				}
				for _, control := range controls {
					fmt.Fprintf(&proof, "theorem refuse_%s : accepts .%s %s %s %s = false := by decide +kernel\n", control.name, control.machine, control.nameBytes, control.image, control.body)
					refusals++
				}
				// Instantiate the universal existing execution theorem using this
				// actual object's admission fact, retaining every model assumption.
				if lane.machine == "arm64" {
					fmt.Fprintf(&proof, `theorem named_execution
    (base : Nat) (aligned : base %% 4 = 0) (bounded : base + 8 < 2^64)
    (s : AArch64BitwiseFunction.State) :
    ∃ loaded, extract .arm64 name image = some loaded ∧
      NamedFunction image (oakPrefix ++ name) loaded ∧ resolvedEntry loaded base = base ∧
      (loadBytes image loaded base (resolvedEntry loaded base) loaded.size).bind
        (fun bytes => AArch64BitwiseFunction.invoke (toUInt8 bytes)
          { s with pc := BitVec.ofNat 64 base }) =
      some (AArch64BitwiseFunction.returned .%s { s with pc := BitVec.ofNat 64 base }) :=
  accepted_arm_execution .%s admitted base aligned bounded s
`, op.name, op.name)
				} else {
					fmt.Fprintf(&proof, `theorem named_execution
    (base : Nat) (aligned : base %% 4 = 0) (bounded : base + 36 < 2^64)
    (s : RiscVFramedBitwise.State) (mappedRW : Nat → Nat → Bool)
    (safe : RiscVFramedBitwise.frameSafe mappedRW s = true) :
    ∃ loaded, extract .rv64 name image = some loaded ∧
      NamedFunction image (oakPrefix ++ name) loaded ∧ resolvedEntry loaded base = base ∧
      (loadBytes image loaded base (resolvedEntry loaded base) loaded.size).bind
        (fun bytes => RiscVFramedBitwise.invoke mappedRW bytes
          { s with core := { s.core with pc := BitVec.ofNat 64 base } }) =
      some (RiscVFramedBitwise.finalState .%s
        { s with core := { s.core with pc := BitVec.ofNat 64 base } }) :=
  accepted_rv_execution .%s admitted base aligned bounded s mappedRW safe
`, op.name, op.name)
				}
				fmt.Fprintf(&proof, "end %s\n", id)
				for _, theorem := range []string{"admitted", "named_execution"} {
					qualified := "CurrentNativeObjects." + id + "." + theorem
					expectedAudits[qualified] = false
					fmt.Fprintf(&proof, "#print axioms %s\n", qualified)
				}
				proof.WriteString("end CurrentNativeObjects\n")
				path := filepath.Join(directory, id+".lean")
				if err := os.WriteFile(path, []byte(proof.String()), 0600); err != nil {
					t.Fatal(err)
				}
				// Fresh bounded Lean processes prevent proof-term accumulation
				// across complete objects. Never batch all twelve into one process.
				output := run(4*time.Minute, "env", "lean", "-j1", path)
				// This is a test-only closure regression gate, not a production
				// receipt. Require exactly this case's two named reports.
				audits := regexp.MustCompile(`'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)`).FindAllStringSubmatch(output, -1)
				for _, audit := range audits {
					seen, expected := expectedAudits[audit[1]]
					if !expected || seen {
						t.Fatalf("unexpected or duplicate native-object theorem audit %q\n%s", audit[1], output)
					}
					expectedAudits[audit[1]] = true
					for _, axiom := range strings.Split(audit[2], ",") {
						switch strings.TrimSpace(axiom) {
						case "", "propext", "Classical.choice", "Quot.sound":
						default:
							t.Fatalf("unexpected native-object proof authority %q in %s", axiom, audit[1])
						}
					}
				}
				for theorem, seen := range expectedAudits {
					if !seen {
						t.Fatalf("missing native-object theorem audit %s\n%s", theorem, output)
					}
				}
				objects++
				audited += len(expectedAudits)
				t.Logf("%s: kernel checked complete %d-byte object, eight refusals, named execution, and two axiom closures; original source %q", id, len(object), original)
			}
		}
	}
	if objects != 12 || refusals != 96 || audited != 24 {
		t.Fatalf("incomplete native-object coverage: objects=%d refusals=%d audits=%d", objects, refusals, audited)
	}
	t.Logf("kernel checked %d current complete objects, %d refusal controls, %d universal named execution instantiations, and %d axiom closures", objects, refusals, objects, audited)
}
