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

// Bind the original restricted source and complete production ET_EXEC to the
// two actual startup instructions at its ELF e_entry, then the already-bound
// nine-instruction framed function. The theorem covers every pair of u32
// operands under its explicit initial platform/ABI state: eleven generated
// callbacks and five clock ticks, returning to e_entry+8. It does not execute
// the following exit setup/ECALL or claim reset, Linux syscalls, a host loader,
// or termination of the unrestricted platform loop.
func TestRV64EntryBitwiseCompilerMatchesLean(t *testing.T) {
	var declarations, assertions []string
	assertions = append(assertions,
		"example : OakSailEntryInstructions.startupBytes = [151,0,0,0,231,128,0,1] := by rfl")
	for _, tc := range []struct{ name, operator string }{{"and", "&"}, {"or", "|"}, {"xor", "^"}} {
		// Reuse the complete-image fixture's production pipeline. In particular,
		// do not compile a different main declaration or synthesize an ELF here.
		a := compileRV64BitwiseImage(t, tc.operator)
		entry := binary.LittleEndian.Uint64(a.image[24:32])
		if entry != a.segment.Vaddr || a.address != entry+16 || a.fileBody != a.segment.Off+16 {
			t.Fatalf("startup/body placement changed: e_entry=%#x, segment=%#x, body=%#x, file body=%#x", entry, a.segment.Vaddr, a.address, a.fileBody)
		}
		if a.segment.Filesz < 16 || a.segment.Off+16 > uint64(len(a.image)) {
			t.Fatal("production startup is not wholly file-backed by PT_LOAD")
		}
		fileEntry := a.segment.Off
		startup := a.image[fileEntry : fileEntry+8]
		if !bytes.Equal(startup, []byte{0x97, 0, 0, 0, 0xe7, 0x80, 0, 1}) {
			t.Fatalf("expected actual AUIPC x1,0; JALR x1,x1,16 startup, got %x", startup)
		}
		// The excluded post-return instructions still remain in the exact ELF
		// literal. Their bytes are not silently removed from the artifact.
		if !bytes.Equal(a.image[fileEntry+8:fileEntry+16], []byte{0x93, 0x08, 0xd0, 0x05, 0x73, 0, 0, 0}) {
			t.Fatalf("unexpected production post-return exit sequence: %x", a.image[fileEntry+8:fileEntry+16])
		}
		returnAddress := entry + 8
		t.Logf("%s actual e_entry=%#x, startup=%x, body=%#x, derived JALR return=%#x; exit setup/ECALL excluded", tc.name, entry, startup, a.address, returnAddress)

		image, source, claim := "entry_image_"+tc.name, "entry_source_"+tc.name, "entry_claim_"+tc.name
		declarations = append(declarations,
			fmt.Sprintf("def %s : List UInt8 := %s", source, rv64ImageLeanBytes([]byte(a.source))),
			fmt.Sprintf("def %s : Oak.BitwiseSource.Decl := ⟨[109,105,120], [97], [98], .%s⟩", claim, tc.name),
			fmt.Sprintf("def %s : Oak.MinimalELF.Bytes := %s", image, rv64ImageLeanBytes(a.image)))
		assertions = append(assertions,
			fmt.Sprintf("example : %s.length = %d ∧ (Oak.MinimalELF.segment %s).entry = %d ∧ (Oak.MinimalELF.segment %s).entry + 16 = %d ∧ (Oak.MinimalELF.segment %s).fileOffset + 16 = %d := by decide +kernel", image, len(a.image), image, entry, image, a.address, image, a.fileBody),
			fmt.Sprintf("theorem accepted_entry_%s : acceptsEntry %s %s %s 69632 = true := by decide +kernel", tc.name, source, claim, image),
			fmt.Sprintf("noncomputable def compiler_entry_%s := OakSailEntryChecks.initialized_entry_clocked_prefix accepted_entry_%s", tc.name, tc.name))
		if tc.name != "and" {
			continue
		}
		assertions = append(assertions,
			fmt.Sprintf("noncomputable def compiler_entry_load_%s (s : %s) := OakSailEntrySource.accepted_load s accepted_entry_%s", tc.name, rv64ImageLeanState, tc.name))
		// Keep this seam narrow: the preceding complete-image gate already
		// covers the general ELF/stack profile. These controls isolate startup,
		// derived return PC, and source/body binding rather than replaying it.
		reject := func(label, src, decl, file string) {
			assertions = append(assertions, "-- Reject "+label,
				fmt.Sprintf("example : acceptsEntry %s %s %s 69632 = false := by decide +kernel", src, decl, file))
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
				t.Fatalf("vacuous startup adversary: %s", label)
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
			{"AUIPC opcode changed to LUI", 0, 0x000000b7},
			{"AUIPC destination changed to x2", 0, 0x00000117},
			{"AUIPC nonzero upper immediate", 0, 0x00001097},
			{"JALR opcode changed to JAL", 4, 0x010080ef},
			{"JALR base changed to x2", 4, 0x010100e7},
			{"JALR offset changed to 12", 4, 0x00c080e7},
			{"JALR rd=x0 discards derived return address", 4, 0x01008067},
		} {
			mutate(mutation.name, func(b []byte) {
				at := fileEntry + mutation.offset
				binary.LittleEndian.PutUint32(b[at:at+4], mutation.word)
			})
		}
		mutate("ELF e_entry changed to the JALR address", func(b []byte) {
			binary.LittleEndian.PutUint64(b[24:32], entry+4)
		})
		mutate("unchanged startup with changed source-bound function", func(b []byte) {
			b[a.fileBody+16] ^= 0x10
		})
		reject("changed source operator", rv64ImageLeanBytes([]byte(strings.Replace(a.source, " & ", " | ", 1))), claim, image)
		reject("changed source claim", source, "entry_claim_or", image)
		assertions = append(assertions,
			"-- The startup theorem returns to entry+8, not the address of JALR.",
			fmt.Sprintf("example : returnAddress %s = BitVec.ofNat 64 %d ∧ returnAddress %s ≠ BitVec.ofNat 64 %d := by decide +kernel", image, returnAddress, image, entry+4))
		excludedExit := mutatedImage("excluded post-return ADDI/ECALL bytes", func(b []byte) {
			clear(b[fileEntry+8 : fileEntry+16])
		})
		assertions = append(assertions,
			"-- Changing only the excluded post-return instructions preserves this prefix theorem.",
			fmt.Sprintf("theorem accepted_entry_changed_exit : acceptsEntry %s %s %s 69632 = true := by decide +kernel", source, claim, excludedExit),
			"noncomputable def compiler_entry_changed_exit := OakSailEntryChecks.initialized_entry_clocked_prefix accepted_entry_changed_exit")
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
			t.Fatal("lake required for RV64 entry compiler correspondence")
		}
		t.Skip("lake unavailable; complete production ELF startup structural checks passed")
	}
	export := filepath.Join("..", "external", "sail-riscv", "build", "model", "Lean_RV64D", "LeanRV64D", "Fetch.lean")
	if _, err := os.Stat(export); err != nil {
		if !os.IsNotExist(err) || os.Getenv("OAK_REQUIRE_RV64_LEAN") != "" {
			t.Fatalf("pinned RV64 fetch export required: %v", err)
		}
		t.Skip("optional pinned RV64 Sail export unavailable; complete production ELF startup structural checks passed")
	}
	root := filepath.Join("..", "spec", "lean-sail429")
	build := exec.Command(lake, "build", "OakSailEntryChecks")
	build.Dir = root
	if output, err := build.CombinedOutput(); err != nil {
		t.Fatalf("entry model build: %v\n%s", err, output)
	}
	pins := "import OakSailEntryChecks\nopen OakSailEntrySource\nset_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n" +
		strings.Join(declarations, "\n") + "\n" + strings.Join(assertions, "\n") + "\n"
	t.Logf("%d-claim entry certificate SHA-256: %x", claimCount, sha256.Sum256([]byte(pins)))
	if path := os.Getenv("OAK_RV64_ENTRY_PINS_OUTPUT"); path != "" {
		if err := os.WriteFile(path, []byte(pins), 0600); err != nil {
			t.Fatal(err)
		}
	}
	// The interfaces-only filter checks both exact theorem applications
	// without reducing any complete-image admission or rerunning #729's pins.
	if !t.Run("interfaces", func(t *testing.T) {
		preflight := fmt.Sprintf(`import OakSailEntryChecks
open OakSailEntrySource
namespace EntryPinPreflight
variable {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
  {image : Oak.MinimalELF.Bytes} {sp : Nat}
noncomputable def execution
    (accepted : acceptsEntry source claim image sp = true) :=
  OakSailEntryChecks.initialized_entry_clocked_prefix accepted
noncomputable def loading (s : %s)
    (accepted : acceptsEntry source claim image sp = true) :=
  OakSailEntrySource.accepted_load s accepted
end EntryPinPreflight
`, rv64ImageLeanState)
		path := filepath.Join(t.TempDir(), "RV64EntryInterfaces.lean")
		if err := os.WriteFile(path, []byte(preflight), 0600); err != nil {
			t.Fatal(err)
		}
		cmd := exec.Command(lake, "env", "lean", path)
		cmd.Dir = root
		if output, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("entry theorem interface preflight: %v\n%s", err, output)
		}
	}) {
		return
	}
	t.Run("pins", func(t *testing.T) {
		path := filepath.Join(t.TempDir(), "RV64EntryBitwisePins.lean")
		if err := os.WriteFile(path, []byte(pins), 0600); err != nil {
			t.Fatal(err)
		}
		cmd := exec.Command(lake, "env", "lean", "--tstack=400000", path)
		cmd.Dir = root
		if output, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("complete ELF entry/source Lean pins: %v\n%s", err, output)
		}
		t.Logf("checked %d exact entry/source and adversarial claims", claimCount)
	})
}
