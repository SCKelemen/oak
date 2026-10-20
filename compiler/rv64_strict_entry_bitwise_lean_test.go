package compiler

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/binary"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
)

// This is a fresh, complete-artifact consumer fixture, not a conversion of the
// separately pinned 4.33 checked-image capability or one of its receipts. Every
// original source and its complete Wasm/ARM64/RV64 output is checked again by the
// original checker in the actual 4.29 Sail consumer's kernel. Execution retains
// explicit initialization and ends after eleven callbacks at ELF e_entry+8;
// neither reset reachability nor the following Linux exit/ECALL is claimed.
func TestRV64StrictEntryBitwiseCompilerMatchesLean(t *testing.T) {
	var declarations, proofs []string
	var andImage rv64BitwiseImage
	var andARM []byte
	inputs := t.TempDir()
	if destination := os.Getenv("OAK_RV64_STRICT_ENTRY_INPUTS_OUTPUT"); destination != "" {
		var err error
		inputs, err = filepath.Abs(destination)
		if err != nil {
			t.Fatal(err)
		}
		if err := os.MkdirAll(inputs, 0700); err != nil {
			t.Fatal(err)
		}
	}
	for _, tc := range []struct{ name, operator string }{{"and", "&"}, {"or", "|"}, {"xor", "^"}} {
		// The existing complete-image helper emits the unchanged original
		// declaration, ET_REL body, and complete production ET_EXEC. Independently
		// require the checked-image producer's proposal route to emit identical RV64.
		rv := compileRV64BitwiseImage(t, tc.operator)
		wasm, err := New().WithSource("image_bitwise.oak", rv.source).
			WithTarget(target.Target{OS: target.OSCore, Arch: target.ArchWasm32}).EmitWasm().Get()
		if err != nil {
			t.Fatal(err)
		}
		symbol, err := checkedImageProposedSymbol(rv.source)
		if err != nil {
			t.Fatal(err)
		}
		var native [2][]byte
		for i, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
			object := checkedImageTestObject(t, rv.source, arch)
			body, err := checkedImageProposeBody(object, symbol, arch)
			if err != nil {
				t.Fatal(err)
			}
			native[i], err = asm.WriteExecutable([]asm.EncodedFunction{body}, asm.ExecutableOptions{
				OS: asm.OSLinux, Arch: body.Arch, Entry: symbol, Base: 0, RV64FloatABI: "double",
			})
			if err != nil {
				t.Fatal(err)
			}
		}
		if !bytes.Equal(native[1], rv.image) {
			t.Fatal("fresh checked-image producer and complete RV64 fixture emitted different files")
		}
		if tc.name == "and" {
			andImage, andARM = rv, native[0]
		}
		for _, artifact := range []struct {
			name string
			data []byte
		}{{"source.oak", []byte(rv.source)}, {"module.wasm", wasm.Bytes}, {"arm64.elf", native[0]}, {"rv64.elf", native[1]}} {
			if err := os.WriteFile(filepath.Join(inputs, tc.name+"_"+artifact.name), artifact.data, 0600); err != nil {
				t.Fatal(err)
			}
			t.Logf("fresh %s %s: %d bytes SHA-256 %x", tc.name, artifact.name, len(artifact.data), sha256.Sum256(artifact.data))
		}
		declarations = append(declarations,
			fmt.Sprintf("def source_%s : List UInt8 := %s", tc.name, rv64ImageLeanBytes([]byte(rv.source))),
			fmt.Sprintf("def wasm_%s : List UInt8 := %s", tc.name, rv64ImageLeanBytes(wasm.Bytes)),
			fmt.Sprintf("def claim_%s : Oak.BitwiseSource.Decl := ⟨[109,105,120], [97], [98], .%s⟩", tc.name, tc.name))
		for i, lane := range []string{"arm", "rv"} {
			data := native[i]
			// Split only the actual zero padding, preserving all complete bytes.
			// The checked list identities below avoid expanding that long gap in
			// every section/symbol field proof. They do not replace any checker.
			if len(data) < 4096 || !bytes.Equal(data[120:4096], make([]byte, 3976)) {
				t.Fatal("production image no longer has the strict header/text padding")
			}
			prefix := lane + "_" + tc.name
			declarations = append(declarations,
				fmt.Sprintf("def %s_header : Bytes := %s", prefix, rv64ImageLeanBytes(data[:120])),
				fmt.Sprintf("def %s_suffix : Bytes := %s", prefix, rv64ImageLeanBytes(data[4096:])),
				fmt.Sprintf("def %s : Bytes := %s_header ++ (List.replicate 3976 0 ++ %s_suffix)", prefix, prefix, prefix))
			proofs = append(proofs, strictEntryImageAdmission(lane, tc.name, data))
		}
		proofs = append(proofs,
			fmt.Sprintf("theorem parsed_%[1]s : Oak.BitwiseSource.parse source_%[1]s = some claim_%[1]s := by decide +kernel", tc.name),
			fmt.Sprintf("theorem wasm_checked_%[1]s : Oak.BitwiseModule.acceptsModule .wasm .wasmLocals [32,32] 32 claim_%[1]s.op claim_%[1]s.name wasm_%[1]s = true := by decide +kernel", tc.name),
			fmt.Sprintf("theorem checked_%[1]s : Oak.BitwiseSourceImageParity.check source_%[1]s wasm_%[1]s arm_%[1]s rv_%[1]s = some claim_%[1]s :=\n  Oak.BitwiseSourceImageParity.check_of_artifacts parsed_%[1]s wasm_checked_%[1]s arm_checked_%[1]s rv_checked_%[1]s", tc.name),
			fmt.Sprintf("theorem layout_%[1]s : OakSailImageLoad.ImageLayout rv_%[1]s 69632 := by decide +kernel", tc.name),
			fmt.Sprintf("theorem admitted_%[1]s : OakSailEntrySource.acceptsEntry source_%[1]s claim_%[1]s rv_%[1]s 69632 = true :=\n  OakSailStrictImageEntry.strict_source_entry_admitted_of_layout checked_%[1]s layout_%[1]s", tc.name),
			fmt.Sprintf("noncomputable def execution_%[1]s :=\n  OakSailStrictImageEntryChecks.initialized_strict_entry_clocked_prefix checked_%[1]s layout_%[1]s", tc.name))
	}

	// Mutate actual emitted bytes, keeping the rest of each full tuple intact.
	// Each negative proof uses the original checker/consumer, not a Go verdict.
	changed := func(name, original string, data []byte, mutate func([]byte)) {
		bad := append([]byte(nil), data...)
		mutate(bad)
		expression, different := original, false
		for i, value := range bad {
			if value != data[i] {
				expression = fmt.Sprintf("(%s.set %d %d)", expression, i, value)
				different = true
			}
		}
		if !different {
			t.Fatalf("vacuous strict-entry mutation %s", name)
		}
		declarations = append(declarations, fmt.Sprintf("def %s : Bytes := %s", name, expression))
	}
	changed("arm_changed_body", "arm_and", andARM, func(b []byte) { b[4108] ^= 1 })
	changed("rv_changed_body", "rv_and", andImage.image, func(b []byte) { b[andImage.fileBody+16] ^= 0x10 })
	changed("rv_changed_startup", "rv_and", andImage.image, func(b []byte) { b[andImage.segment.Off] ^= 0x20 })
	changed("rv_changed_entry", "rv_and", andImage.image, func(b []byte) {
		binary.LittleEndian.PutUint64(b[24:32], andImage.segment.Vaddr+4)
	})
	changed("rv_changed_suffix", "rv_and", andImage.image, func(b []byte) { b[andImage.segment.Off+8] ^= 1 })
	declarations = append(declarations, fmt.Sprintf("def source_changed_type : List UInt8 := %s",
		rv64ImageLeanBytes([]byte(strings.ReplaceAll(andImage.source, "u32", "u64")))))
	proofs = append(proofs, strictEntryControls)
	pins := "import OakSailStrictImageEntryChecks\nset_option autoImplicit false\nset_option debug.skipKernelTC false\nset_option linter.unusedSimpArgs false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\nnamespace StrictEntryCompilerPins\nopen Oak.MinimalELF (Bytes readLE slice)\nopen Oak.NativeBitwiseImage\nopen Oak.NativeBitwiseObject (fromUInt8)\n" +
		strictEntryImageSupport + "\n" + strings.Join(declarations, "\n") + "\n" + strings.Join(proofs, "\n") + "\nend StrictEntryCompilerPins\n"
	path := filepath.Join(inputs, "RV64StrictEntryBitwisePins.lean")
	if err := os.WriteFile(path, []byte(pins), 0600); err != nil {
		t.Fatal(err)
	}
	if output := os.Getenv("OAK_RV64_STRICT_ENTRY_PINS_OUTPUT"); output != "" {
		if err := os.WriteFile(output, []byte(pins), 0600); err != nil {
			t.Fatal(err)
		}
	}
	t.Logf("fresh strict-entry fixture source SHA-256: %x; generated bytes are not kernel-check receipts", sha256.Sum256([]byte(pins)))

	root, err := filepath.Abs(filepath.Join("..", "spec", "lean-sail429"))
	if err != nil {
		t.Fatal(err)
	}
	if _, err := strictEntryProjectEnvironment(root, nil); err != nil {
		t.Fatal(err)
	}
	missing := func(reason string) {
		t.Helper()
		if os.Getenv("OAK_REQUIRE_RV64_LEAN") != "" {
			t.Fatal("required strict-entry kernel gate: " + reason)
		}
		t.Skip(reason + "; fresh complete production tuple generation passed, no Sail admission/execution checked")
	}
	lake, err := exec.LookPath("lake")
	if err != nil {
		missing("lake unavailable")
	}
	python, err := exec.LookPath("python3")
	if err != nil {
		missing("python3 unavailable for the strict-entry axiom audit")
	}
	export := filepath.Join(root, "..", "..", "external", "sail-riscv", "build", "model", "Lean_RV64D", "LeanRV64D", "Fetch.lean")
	if _, err := os.Stat(export); err != nil {
		if !os.IsNotExist(err) {
			t.Fatal(err)
		}
		missing("pinned RV64 Sail fetch export unavailable")
	}
	run := func(t *testing.T, program string, args ...string) string {
		t.Helper()
		ctx, cancel := context.WithTimeout(t.Context(), 25*time.Minute)
		defer cancel()
		cmd, err := strictEntryProjectCommand(ctx, root, os.Environ(), program, args...)
		if err != nil {
			t.Fatal(err)
		}
		output, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("strict-entry %s %v: %v (context %v)\n%s", program, args, err, ctx.Err(), output)
		}
		return string(output)
	}
	version := strings.TrimSpace(run(t, lake, "env", "lean", "--version"))
	if err := strictEntryCheckVersion(version); err != nil {
		t.Fatal(err)
	}
	t.Log(version)
	// Lake uses the tracked ../lean source in this project's 4.29 cache. No
	// separate 4.33 checker invocation, receipt or copied proof object is used.
	t.Log(run(t, lake, "build", "OakSailStrictImageEntryChecks"))
	if !t.Run("interfaces", func(t *testing.T) {
		preflight := `import OakSailStrictImageEntryChecks
set_option autoImplicit false
set_option debug.skipKernelTC false
namespace StrictEntryCompilerInterfaces
variable {source wasm : List UInt8} {arm image : Oak.MinimalELF.Bytes}
  {claim : Oak.BitwiseSource.Decl} {sp : Nat}
noncomputable def admission
    (checked : Oak.BitwiseSourceImageParity.check source wasm arm image = some claim)
    (layout : OakSailImageLoad.ImageLayout image sp) :=
  OakSailStrictImageEntry.strict_source_entry_admitted_of_layout checked layout
noncomputable def execution
    (checked : Oak.BitwiseSourceImageParity.check source wasm arm image = some claim)
    (layout : OakSailImageLoad.ImageLayout image sp) :=
  OakSailStrictImageEntryExecution.strict_typed_entry_clocked_prefix checked layout
noncomputable def initialized_execution
    (checked : Oak.BitwiseSourceImageParity.check source wasm arm image = some claim)
    (layout : OakSailImageLoad.ImageLayout image sp) :=
  OakSailStrictImageEntryChecks.initialized_strict_entry_clocked_prefix checked layout
end StrictEntryCompilerInterfaces
`
		preflightPath := filepath.Join(t.TempDir(), "RV64StrictEntryInterfaces.lean")
		if err := os.WriteFile(preflightPath, []byte(preflight), 0600); err != nil {
			t.Fatal(err)
		}
		t.Log(run(t, lake, "env", "lean", "-t", "0", preflightPath))
	}) {
		return
	}
	if !t.Run("pins", func(t *testing.T) {
		t.Log(run(t, lake, "env", "lean", "-j1", "-M6000", "-t", "0", "--tstack=400000", path))
		t.Log("checked three fresh source/full-artifact tuples, actual entry admission and initialized execution, touching stacks, and mutation/refusal controls")
	}) {
		return
	}
	t.Run("audit", func(t *testing.T) {
		// The auditor owns a fixed inventory and exact execution baseline. It
		// never trusts a list of roots or an allowlist supplied by this fixture.
		t.Log(run(t, python, "strict-entry-audit.py", "--fixture", path))
	})
}

const strictEntryLeanToolchain = "leanprover/lean4:v4.29.0"

// Pin toolchain selection as well as the observed version. Elan can otherwise
// honor an inherited override, or select from a temporary proof file's path.
// Every child receives its own environment; the parent environment is untouched.
func strictEntryProjectEnvironment(root string, inherited []string) ([]string, error) {
	pin, err := os.ReadFile(filepath.Join(root, "lean-toolchain"))
	if err != nil {
		return nil, fmt.Errorf("strict-entry project toolchain pin: %w", err)
	}
	if strings.TrimSpace(string(pin)) != strictEntryLeanToolchain {
		return nil, fmt.Errorf("strict-entry requires project toolchain %s, got %q", strictEntryLeanToolchain, strings.TrimSpace(string(pin)))
	}
	environment := make([]string, 0, len(inherited)+1)
	for _, entry := range inherited {
		if !strings.HasPrefix(entry, "ELAN_TOOLCHAIN=") {
			environment = append(environment, entry)
		}
	}
	return append(environment, "ELAN_TOOLCHAIN="+strictEntryLeanToolchain), nil
}

func strictEntryProjectCommand(ctx context.Context, root string, inherited []string, program string, args ...string) (*exec.Cmd, error) {
	environment, err := strictEntryProjectEnvironment(root, inherited)
	if err != nil {
		return nil, err
	}
	cmd := exec.CommandContext(ctx, program, args...)
	cmd.Dir, cmd.Env, cmd.WaitDelay = root, environment, 5*time.Second
	return cmd, nil
}

func strictEntryCheckVersion(version string) error {
	if !strings.HasPrefix(strings.TrimSpace(version), "Lean (version 4.29.0,") {
		return fmt.Errorf("strict-entry requires exact Lean 4.29.0, got %q", strings.TrimSpace(version))
	}
	return nil
}

// This subprocess probe tests selection and path custody only. It neither
// impersonates Lean nor supplies a successful proof/model/version result.
func TestRV64StrictEntryToolchainSelection(t *testing.T) {
	const probe = "OAK_STRICT_ENTRY_COMMAND_PROBE"
	if os.Getenv(probe) == "1" {
		cwd, err := os.Getwd()
		if err != nil {
			t.Fatal(err)
		}
		data, err := os.ReadFile(os.Args[len(os.Args)-1])
		if err != nil {
			t.Fatal(err)
		}
		fmt.Printf("%s\n%s\n%s", cwd, os.Getenv("ELAN_TOOLCHAIN"), data)
		os.Exit(0)
	}
	root, outside := t.TempDir(), t.TempDir()
	root, err := filepath.EvalSymlinks(root)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(root, "lean-toolchain"), []byte(strictEntryLeanToolchain+"\n"), 0600); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(outside, "lean-toolchain"), []byte("leanprover/lean4:v4.33.1\n"), 0600); err != nil {
		t.Fatal(err)
	}
	proof := filepath.Join(outside, "TemporaryProof.lean")
	const proofBytes = "-- This is a subprocess path probe, not an elaborated proof.\n"
	if err := os.WriteFile(proof, []byte(proofBytes), 0600); err != nil {
		t.Fatal(err)
	}
	program, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	before := os.Getenv("ELAN_TOOLCHAIN")
	inherited := append(os.Environ(), "ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1", "ELAN_TOOLCHAIN=conflicting-duplicate", probe+"=1")
	inheritedBefore := strings.Join(inherited, "\n")
	cmd, err := strictEntryProjectCommand(t.Context(), root, inherited, program,
		"-test.run=^TestRV64StrictEntryToolchainSelection$", "--", proof)
	if err != nil {
		t.Fatal(err)
	}
	if cmd.Dir != root || strings.Join(inherited, "\n") != inheritedBefore {
		t.Fatal("project command changed cwd selection or mutated its inherited environment")
	}
	selected := 0
	for _, entry := range cmd.Env {
		if strings.HasPrefix(entry, "ELAN_TOOLCHAIN=") {
			selected++
			if entry != "ELAN_TOOLCHAIN="+strictEntryLeanToolchain {
				t.Fatal("project command retained a conflicting toolchain override")
			}
		}
	}
	if selected != 1 {
		t.Fatalf("expected one pinned ELAN_TOOLCHAIN entry, got %d", selected)
	}
	output, err := cmd.CombinedOutput()
	if err != nil || string(output) != root+"\n"+strictEntryLeanToolchain+"\n"+proofBytes {
		t.Fatalf("project cwd/toolchain/temporary-proof probe: %v\n%s", err, output)
	}
	if os.Getenv("ELAN_TOOLCHAIN") != before {
		t.Fatal("project command mutated the process environment")
	}
	for _, wrong := range []string{"leanprover/lean4:v4.33.1\n", "leanprover/lean4:v4.29.1\n", ""} {
		if err := os.WriteFile(filepath.Join(root, "lean-toolchain"), []byte(wrong), 0600); err != nil {
			t.Fatal(err)
		}
		if _, err := strictEntryProjectCommand(t.Context(), root, inherited, program); err == nil {
			t.Fatalf("accepted wrong project toolchain %q", wrong)
		}
	}
	if err := os.Remove(filepath.Join(root, "lean-toolchain")); err != nil {
		t.Fatal(err)
	}
	if _, err := strictEntryProjectCommand(t.Context(), root, inherited, program); err == nil {
		t.Fatal("accepted missing project toolchain pin")
	}
	if err := strictEntryCheckVersion("Lean (version 4.29.0, x86_64-unknown-linux-gnu, commit TEST, Release)\n"); err != nil {
		t.Fatal(err)
	}
	for _, wrong := range []string{"", "Lean (version 4.33.1, Release)", "Lean (version 4.29.1, Release)", "Lean (version 4.29.0-rc1, Release)"} {
		if err := strictEntryCheckVersion(wrong); err == nil {
			t.Fatalf("accepted wrong actual Lean version %q", wrong)
		}
	}
}

// This is the existing complete-image fixture's atomized kernel proof pattern,
// applied to this invocation's freshly compiled bytes. The original recognizer
// and its entire profile are retained; only checked list identities are shared.
func strictEntryImageAdmission(lane, op string, image []byte) string {
	prefix := lane + "_" + op
	machine := ".rv64"
	body := "(Oak.RiscVFramedBitwise.functionBytes ." + op + ")"
	if lane == "arm" {
		machine = ".arm64"
		body = "(fromUInt8 (Oak.AArch64BitwiseFunction.functionBytes ." + op + "))"
	}
	atom := "(by (try simp only [Oak.NativeBitwiseObject.readSection, Oak.NativeBitwiseObject.readSymbol, Oak.NativeBitwiseObject.symbolName, Oak.MinimalELF.segment, textSection, dataSection, symSection, strSection, shstrSection, functionSymbol, startSymbol, nullSection, nullSymbol, image_length, h40, h58, h60]); (try simp (disch := decide) only [read_tail, slice_tail]); all_goals decide +kernel)"
	pair := func(parts ...string) string { return "⟨" + strings.Join(parts, ",") + "⟩" }
	atoms := func(count int) []string {
		out := make([]string, count)
		for i := range out {
			out[i] = atom
		}
		return out
	}
	layout := atoms(12)
	layout[5] = "(zero_gap " + prefix + "_header " + prefix + "_suffix header_length)"
	profile := pair(pair(append([]string{pair(atoms(11)...)}, atoms(5)...)...), pair(atoms(2)...), pair(atoms(6)...), pair(atoms(6)...), pair(layout...))
	return fmt.Sprintf(`theorem %[1]s_checked_%[2]s : accepts %[3]s (fromUInt8 claim_%[2]s.name) %[4]s %[5]s = true := by
  have header_length : %[4]s_header.length = 120 := by decide +kernel
  have image_length : %[4]s.length = %[6]d := by
    change (%[4]s_header ++ (List.replicate 3976 0 ++ %[4]s_suffix)).length = %[6]d
    rw [List.length_append, List.length_append, List.length_replicate, header_length]
    decide +kernel
  have h40 : readLE %[4]s 40 8 = %[7]d := by decide +kernel
  have h58 : readLE %[4]s 58 2 = 64 := by decide +kernel
  have h60 : readLE %[4]s 60 2 = 6 := by decide +kernel
  have read_tail (offset count : Nat) (bound : 4096 ≤ offset) :
      readLE %[4]s offset count = readLE %[4]s_suffix (offset-4096) count :=
    padded_tail_read %[4]s_header %[4]s_suffix header_length offset count bound
  have slice_tail (offset count : Nat) (bound : 4096 ≤ offset) :
      slice %[4]s offset count = slice %[4]s_suffix (offset-4096) count :=
    padded_tail_slice %[4]s_header %[4]s_suffix header_length offset count bound
  exact accepts_of_profile %[8]s %[9]s
`, lane, op, machine, prefix, body, len(image), binary.LittleEndian.Uint64(image[40:48]), profile, atom)
}

const strictEntryImageSupport = `
theorem slice_after (pre suffix : Bytes) (offset count : Nat)
    (bound : pre.length ≤ offset) :
    slice (pre ++ suffix) offset count = slice suffix (offset-pre.length) count := by
  unfold slice
  rw [List.drop_append, List.drop_eq_nil_of_le bound, List.nil_append]

theorem padded_tail_slice (header suffix : Bytes) (hlen : header.length = 120)
    (offset count : Nat) (bound : 4096 ≤ offset) :
    slice (header ++ (List.replicate 3976 0 ++ suffix)) offset count =
      slice suffix (offset-4096) count := by
  have plen : (header ++ List.replicate 3976 (0 : BitVec 8)).length = 4096 := by
    rw [List.length_append, hlen, List.length_replicate]
  rw [← List.append_assoc]
  have hbound : (header ++ List.replicate 3976 (0 : BitVec 8)).length ≤ offset := by
    rw [plen]
    exact bound
  simpa only [plen] using slice_after (header ++ List.replicate 3976 0) suffix offset count hbound

theorem padded_tail_read (header suffix : Bytes) (hlen : header.length = 120)
    (offset count : Nat) (bound : 4096 ≤ offset) :
    readLE (header ++ (List.replicate 3976 0 ++ suffix)) offset count =
      readLE suffix (offset-4096) count := by
  unfold readLE
  rw [padded_tail_slice header suffix hlen offset count bound]

theorem zero_gap (header tail : Bytes) (length : header.length = 120) :
    slice (header ++ (List.replicate 3976 0 ++ tail)) 120 3976 = List.replicate 3976 0 := by
  unfold slice
  rw [List.drop_left' length]
  exact List.take_left' List.length_replicate

theorem accepts_of_profile {m : Oak.MinimalELF.Machine} {name image expectedBody : Bytes}
    (profile : StrictProfile m name image)
    (body : slice image (bodyOffset m) (bodySize m) = expectedBody) :
    accepts m name image expectedBody = true := by
  simp only [accepts, extract, if_pos profile, profile_decodes profile, candidate, decide_eq_true_eq]
  exact body

theorem refuses_profile {m : Oak.MinimalELF.Machine} {name image expectedBody : Bytes}
    {condition : Prop} (necessary : StrictProfile m name image → condition)
    (bad : ¬ condition) : accepts m name image expectedBody = false := by
  have absent : ¬ StrictProfile m name image := fun h => bad (necessary h)
  simp only [accepts, extract, if_neg absent]

theorem refuses_body {m : Oak.MinimalELF.Machine} {name image expectedBody : Bytes}
    (bad : slice image (bodyOffset m) (bodySize m) ≠ expectedBody) :
    accepts m name image expectedBody = false := by
  cases h : accepts m name image expectedBody with
  | false => rfl
  | true =>
    obtain ⟨l, _, _, _, _, _, _, offset, size, _, body, _, _, _, _⟩ := accepted_named_load h
    rw [offset, size] at body
    exact False.elim (bad body.symm)
`

const strictEntryControls = `
theorem layout_touch_below : OakSailImageLoad.ImageLayout rv_and 65536 := by decide +kernel
theorem admitted_touch_below : OakSailEntrySource.acceptsEntry source_and claim_and rv_and 65536 = true :=
  OakSailStrictImageEntry.strict_source_entry_admitted_of_layout checked_and layout_touch_below
theorem layout_touch_above : OakSailImageLoad.ImageLayout rv_and 65696 := by decide +kernel
theorem admitted_touch_above : OakSailEntrySource.acceptsEntry source_and claim_and rv_and 65696 = true :=
  OakSailStrictImageEntry.strict_source_entry_admitted_of_layout checked_and layout_touch_above

theorem reject_source : Oak.BitwiseSourceImageParity.check source_or wasm_and arm_and rv_and = none :=
  Oak.BitwiseSourceImageParity.refuses_failed_artifact parsed_or (Or.inl (by decide +kernel))
theorem reject_source_type : Oak.BitwiseSourceImageParity.check source_changed_type wasm_and arm_and rv_and = none :=
  (Oak.BitwiseSourceImageParity.refuses_unsupported (by decide +kernel)).1
theorem reject_wasm : Oak.BitwiseSourceImageParity.check source_and (wasm_and.set 0 1) arm_and rv_and = none :=
  Oak.BitwiseSourceImageParity.refuses_failed_artifact parsed_and (Or.inl (by decide +kernel))
theorem reject_arm_body : Oak.BitwiseSourceImageParity.check source_and wasm_and arm_changed_body rv_and = none := by
  apply Oak.BitwiseSourceImageParity.refuses_failed_artifact parsed_and
  exact Or.inr (Or.inl (refuses_body (by decide +kernel)))
theorem reject_rv_body : Oak.BitwiseSourceImageParity.check source_and wasm_and arm_and rv_changed_body = none := by
  apply Oak.BitwiseSourceImageParity.refuses_failed_artifact parsed_and
  exact Or.inr (Or.inr (refuses_body (by decide +kernel)))
theorem reject_startup : Oak.BitwiseSourceImageParity.check source_and wasm_and arm_and rv_changed_startup = none := by
  apply Oak.BitwiseSourceImageParity.refuses_failed_artifact parsed_and
  exact Or.inr (Or.inr (refuses_profile (fun h => h.2.2.2.2.2.2.2.2.2.2.1) (by decide +kernel)))
theorem reject_entry : Oak.BitwiseSourceImageParity.check source_and wasm_and arm_and rv_changed_entry = none := by
  apply Oak.BitwiseSourceImageParity.refuses_failed_artifact parsed_and
  exact Or.inr (Or.inr (refuses_profile (fun h => h.1.2.1) (by decide +kernel)))

theorem reject_stack_underflow : ¬ OakSailImageLoad.ImageLayout rv_and 80 ∧
    OakSailEntrySource.acceptsEntry source_and claim_and rv_and 80 = false := by decide +kernel
theorem reject_stack_alignment : ¬ OakSailImageLoad.ImageLayout rv_and 69633 ∧
    OakSailEntrySource.acceptsEntry source_and claim_and rv_and 69633 = false := by decide +kernel
theorem reject_stack_overlap : ¬ OakSailImageLoad.ImageLayout rv_and 65680 ∧
    OakSailEntrySource.acceptsEntry source_and claim_and rv_and 65680 = false := by decide +kernel
theorem reject_stack_upper : ¬ OakSailImageLoad.ImageLayout rv_and 33554448 ∧
    OakSailEntrySource.acceptsEntry source_and claim_and rv_and 33554448 = false := by decide +kernel

-- Entry's bounded prefix excludes the following ADDI/ECALL bytes. The strict
-- original-image checker owns those bytes too, so the implication is one-way.
theorem prefix_accepts_changed_suffix :
    OakSailEntrySource.acceptsEntry source_and claim_and rv_changed_suffix 69632 = true := by decide +kernel
theorem strict_rejects_changed_suffix :
    Oak.BitwiseSourceImageParity.check source_and wasm_and arm_and rv_changed_suffix = none := by
  apply Oak.BitwiseSourceImageParity.refuses_failed_artifact parsed_and
  exact Or.inr (Or.inr (refuses_profile (fun h => h.2.2.2.2.2.2.2.2.2.2.1) (by decide +kernel)))
`
