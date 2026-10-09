package compiler

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// Extend the original complete-image entry certificate by exactly one actual
// callback: ADDI a7,x0,93 at e_entry+8. The final state is ready to fetch/decode
// the exact ECALL at e_entry+12 after six ticks, with phase zero and mcycle
// wrapped to four. ECALL is not executed: this is explicit Machine/Bare/ABI
// initialization, not Linux delivery/exit, reset reachability, or a full loop.
func TestRV64ExitReadyCompilerMatchesLean(t *testing.T) {
	var declarations, assertions []string
	for _, tc := range []struct {
		name, operator      string
		left, right, result uint32
	}{
		{"and", "&", 0x80000000, 0xffffffff, 0x80000000},
		{"or", "|", 0x80000000, 1, 0x80000001},
		{"xor", "^", 0xffffffff, 0x7fffffff, 0x80000000},
	} {
		// Compile the unchanged restricted declaration through the same ET_REL
		// and production ET_EXEC pipeline. Keep every byte of the original ELF.
		a := compileRV64BitwiseImage(t, tc.operator)
		entry := binary.LittleEndian.Uint64(a.image[24:32])
		if len(a.image) != 4680 || entry != a.segment.Vaddr || a.address != entry+16 || a.fileBody != a.segment.Off+16 {
			t.Fatalf("complete image/startup/body profile changed: length=%d, e_entry=%#x, segment=%#x, body=%#x, file body=%#x", len(a.image), entry, a.segment.Vaddr, a.address, a.fileBody)
		}
		if a.segment.Filesz < 16 || a.segment.Off+16 > uint64(len(a.image)) {
			t.Fatal("production startup/exit pair is not wholly file-backed by PT_LOAD")
		}
		fileEntry := a.segment.Off
		if !bytes.Equal(a.image[fileEntry:fileEntry+8], []byte{0x97, 0, 0, 0, 0xe7, 0x80, 0, 1}) {
			t.Fatalf("unexpected production entry call: %x", a.image[fileEntry:fileEntry+8])
		}
		if !bytes.Equal(a.image[fileEntry+8:fileEntry+16], []byte{0x93, 0x08, 0xd0, 0x05, 0x73, 0, 0, 0}) {
			t.Fatalf("expected actual ADDI a7,x0,93; ECALL, got %x", a.image[fileEntry+8:fileEntry+16])
		}
		t.Logf("%s complete %d-byte ELF: ADDI a7,x0,93 at %#x, exact ECALL at %#x; callback 12 stops before ECALL execution", tc.name, len(a.image), entry+8, entry+12)

		image, source, claim := "exit_image_"+tc.name, "exit_source_"+tc.name, "exit_claim_"+tc.name
		declarations = append(declarations,
			fmt.Sprintf("def %s : List UInt8 := %s", source, rv64ImageLeanBytes([]byte(a.source))),
			fmt.Sprintf("def %s : Oak.BitwiseSource.Decl := ⟨[109,105,120], [97], [98], .%s⟩", claim, tc.name),
			fmt.Sprintf("def %s : Oak.MinimalELF.Bytes := %s", image, rv64ImageLeanBytes(a.image)))
		assertions = append(assertions,
			fmt.Sprintf("example : %s.length = 4680 ∧ (Oak.MinimalELF.segment %s).entry + 8 = %d ∧ (Oak.MinimalELF.segment %s).entry + 12 = %d ∧ (%s.drop %d).take 8 = [147,8,208,5,115,0,0,0] := by decide +kernel", image, image, entry+8, image, entry+12, image, fileEntry+8),
			fmt.Sprintf("theorem accepted_exit_%s : acceptsExit %s %s %s 69632 = true := by decide +kernel", tc.name, source, claim, image),
			fmt.Sprintf("noncomputable def compiler_exit_%s := OakSailExitChecks.initialized_exit_ready accepted_exit_%s", tc.name, tc.name),
			// Even for u32, the RV64 psABI sign-extends the final 32-bit
			// result to XLEN. This is the a0 value in the generic theorem.
			fmt.Sprintf("example : Oak.RiscV.widen 32 false (Oak.BitwiseFunction.eval .%s (0x%x#32) (0x%x#32)) = (0x%x#64) ∧ Oak.RiscV.widen 32 false (Oak.BitwiseFunction.eval .%s (0x%x#32) (0x%x#32)) ≠ (0x%x#64) := by decide +kernel", tc.name, tc.left, tc.right, uint64(int64(int32(tc.result))), tc.name, tc.left, tc.right, tc.result))
		if tc.name != "and" {
			continue
		}
		assertions = append(assertions,
			fmt.Sprintf("noncomputable def compiler_exit_load (s : %s) := OakSailExitSource.accepted_load s accepted_exit_and", rv64ImageLeanState))
		// Keep the controls local to this strengthened acceptance predicate.
		// The complete-image and entry gates already test general ELF/stack
		// admission, startup, and the nine-instruction function separately.
		reject := func(label, src, decl, file string) {
			assertions = append(assertions, "-- Reject "+label,
				fmt.Sprintf("example : acceptsExit %s %s %s 69632 = false := by decide +kernel", src, decl, file))
		}
		mutatedImage := func(label string, change func([]byte)) string {
			bad := append([]byte(nil), a.image...)
			change(bad)
			expression := image
			changed := false
			for i, b := range bad {
				if b != a.image[i] {
					expression = fmt.Sprintf("(%s.set %d %d)", expression, i, b)
					changed = true
				}
			}
			if !changed {
				t.Fatalf("vacuous exit adversary: %s", label)
			}
			return expression
		}
		mutate := func(label string, change func([]byte)) {
			reject(label, source, claim, mutatedImage(label, change))
		}
		for _, mutation := range []struct {
			name   string
			offset uint64
			word   uint32
		}{
			{"ADDI exit number changed to 94", 8, 0x05e00893},
			{"ADDI rd=x0 discards exit number", 8, 0x05d00013},
			{"ADDI rd=a0 overwrites the returned value", 8, 0x05d00513},
			{"ADDI rs1=x1 adds the return address", 8, 0x05d08893},
			{"ECALL changed to EBREAK", 12, 0x00100073},
			{"ECALL changed to non-SYSTEM NOP", 12, 0x00000013},
			{"ECALL word changed with nonzero rs1", 12, 0x00008073},
		} {
			mutate(mutation.name, func(b []byte) {
				at := fileEntry + mutation.offset
				binary.LittleEndian.PutUint32(b[at:at+4], mutation.word)
			})
		}
		mutate("exit instructions shifted to each other's locations", func(b []byte) {
			binary.LittleEndian.PutUint32(b[fileEntry+8:fileEntry+12], 0x00000073)
			binary.LittleEndian.PutUint32(b[fileEntry+12:fileEntry+16], 0x05d00893)
		})
		mutate("ELF e_entry shifted to the exit setup", func(b []byte) {
			binary.LittleEndian.PutUint64(b[24:32], entry+8)
		})
		mutate("unchanged exit pair with changed source-bound function", func(b []byte) {
			b[a.fileBody+16] ^= 0x10
		})
		reject("changed source operator", rv64ImageLeanBytes([]byte(strings.Replace(a.source, " & ", " | ", 1))), claim, image)
		reject("changed source claim", source, "exit_claim_or", image)
		changedExit := mutatedImage("previously excluded post-return instructions", func(b []byte) {
			clear(b[fileEntry+8 : fileEntry+16])
		})
		assertions = append(assertions,
			"-- The previous entry prefix admitted this mutation; exit readiness must reject it.",
			fmt.Sprintf("example : OakSailEntrySource.acceptsEntry %s %s %s 69632 = true ∧ acceptsExit %s %s %s 69632 = false := by decide +kernel", source, claim, changedExit, source, claim, changedExit))
	}
	claimCount := 0
	for _, line := range assertions {
		if !strings.HasPrefix(line, "--") {
			claimCount++
		}
	}
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_RV64_LEAN") != "" {
			t.Fatal("lake required for RV64 exit-readiness compiler correspondence")
		}
		t.Skip("lake unavailable; complete production ELF exit-placement structural checks passed")
	}
	export := filepath.Join("..", "external", "sail-riscv", "build", "model", "Lean_RV64D", "LeanRV64D", "Fetch.lean")
	if _, err := os.Stat(export); err != nil {
		if !os.IsNotExist(err) || os.Getenv("OAK_REQUIRE_RV64_LEAN") != "" {
			t.Fatalf("pinned RV64 fetch export required: %v", err)
		}
		t.Skip("optional pinned RV64 Sail export unavailable; complete production ELF exit-placement structural checks passed")
	}
	root := filepath.Join("..", "spec", "lean-sail429")
	build := exec.Command(lake, "build", "OakSailExitChecks")
	build.Dir = root
	if output, err := build.CombinedOutput(); err != nil {
		t.Fatalf("exit-readiness model build: %v\n%s", err, output)
	}
	pins := "import OakSailExitChecks\nopen OakSailExitSource\nset_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n" +
		strings.Join(declarations, "\n") + "\n" + strings.Join(assertions, "\n") + "\n"
	t.Logf("%d-claim exit-readiness certificate SHA-256: %x", claimCount, sha256.Sum256([]byte(pins)))
	if path := os.Getenv("OAK_RV64_EXIT_PINS_OUTPUT"); path != "" {
		if err := os.WriteFile(path, []byte(pins), 0600); err != nil {
			t.Fatal(err)
		}
	}
	// Check both theorem applications before reducing complete artifacts.
	// The interfaces-only filter does not replay earlier image/entry pins.
	if !t.Run("interfaces", func(t *testing.T) {
		preflight := fmt.Sprintf(`import OakSailExitChecks
open OakSailExitSource
namespace ExitPinPreflight
variable {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
  {image : Oak.MinimalELF.Bytes} {sp : Nat}
noncomputable def execution
    (accepted : acceptsExit source claim image sp = true)
    (left right : BitVec 32) (fuel : Nat) (s : %s)
    (saved1 saved2 : BitVec 64) (step : Nat) :=
  OakSailExitChecks.initialized_exit_ready accepted left right fuel s saved1 saved2 step
noncomputable def loading (s : %s)
    (accepted : acceptsExit source claim image sp = true) :=
  OakSailExitSource.accepted_load s accepted
end ExitPinPreflight
`, rv64ImageLeanState, rv64ImageLeanState)
		path := filepath.Join(t.TempDir(), "RV64ExitInterfaces.lean")
		if err := os.WriteFile(path, []byte(preflight), 0600); err != nil {
			t.Fatal(err)
		}
		cmd := exec.Command(lake, "env", "lean", path)
		cmd.Dir = root
		if output, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("exit-readiness theorem interface preflight: %v\n%s", err, output)
		}
	}) {
		return
	}
	t.Run("pins", func(t *testing.T) {
		path := filepath.Join(t.TempDir(), "RV64ExitReadyPins.lean")
		if err := os.WriteFile(path, []byte(pins), 0600); err != nil {
			t.Fatal(err)
		}
		cmd := exec.Command(lake, "env", "lean", "--tstack=400000", path)
		cmd.Dir = root
		if output, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("complete ELF exit-readiness/source Lean pins: %v\n%s", err, output)
		}
		t.Logf("checked %d exact exit-readiness/source and adversarial claims", claimCount)
	})
}
