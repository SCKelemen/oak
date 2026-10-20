package compiler_test

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"reflect"
	"strings"
	"sync/atomic"
	"testing"
	"time"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/bitwisecheck"
	"github.com/SCKelemen/oak/compiler"
	leansources "github.com/SCKelemen/oak/spec/lean"
	"github.com/SCKelemen/oak/target"
)

const checkedBitwiseImageSource = "bitwise: (x: u32, y: u32): u32 = x & y\n"

func TestEmitKernelCheckedBitwiseImageBundleRefusesInvalidInstallation(t *testing.T) {
	for _, tc := range []struct {
		name         string
		installation *bitwisecheck.ImageInstallation
	}{{"nil", nil}, {"zero", new(bitwisecheck.ImageInstallation)}} {
		t.Run(tc.name, func(t *testing.T) {
			bundle, err := compiler.EmitKernelCheckedBitwiseImageBundle(t.Context(), tc.installation,
				compiler.SourceText{Path: "original.oak", Text: checkedBitwiseImageSource}).Get()
			if bundle != nil || !errors.Is(err, bitwisecheck.ErrInvalidInstallation) {
				t.Fatalf("uninitialized checker must refuse: bundle=%v error=%v", bundle, err)
			}
		})
	}
}

func TestEmitKernelCheckedBitwiseImageBundleRefusesCanceledContext(t *testing.T) {
	ctx, cancel := context.WithCancel(t.Context())
	cancel()
	bundle, err := compiler.EmitKernelCheckedBitwiseImageBundle(ctx, nil, compiler.SourceText{Text: checkedBitwiseImageSource}).Get()
	if bundle != nil || !errors.Is(err, context.Canceled) {
		t.Fatalf("canceled request must refuse: bundle=%v error=%v", bundle, err)
	}
	bundle, err = compiler.EmitKernelCheckedBitwiseImageBundle(nil, nil, compiler.SourceText{Text: checkedBitwiseImageSource}).Get()
	if bundle != nil || err == nil {
		t.Fatalf("nil context must refuse: bundle=%v error=%v", bundle, err)
	}
}

func TestKernelCheckedBitwiseImageBundleDoesNotPromoteLegacyAuthority(t *testing.T) {
	comp := compiler.New().WithSource("original.oak", checkedBitwiseImageSource)
	module, err := comp.EmitWasm().Get()
	if err != nil {
		t.Fatal(err)
	}
	if module.TranslationVerified || module.ByteValidation == nil {
		t.Fatal("ordinary Wasm emission authority changed")
	}
	if _, err := comp.WithVerifiedProfile().EmitWasm().Get(); err == nil {
		t.Fatal("checked image API must not enable legacy verified Wasm emission")
	}
	if new(bitwisecheck.CheckedImageBundle).Valid() || new(bitwisecheck.CheckedBundle).Valid() {
		t.Fatal("zero bundle cannot carry admission authority")
	}
	if reflect.TypeFor[bitwisecheck.CheckedBundle]().ConvertibleTo(reflect.TypeFor[bitwisecheck.CheckedImageBundle]()) {
		t.Fatal("object authority must not be convertible to image authority")
	}
	for _, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
		comp := compiler.New().WithSource("original.oak", checkedBitwiseImageSource).
			WithTarget(target.Target{OS: target.OSLinux, Arch: arch})
		if _, err := comp.EmitExecutable().Get(); err == nil {
			t.Fatal("ordinary executable API must still require main")
		}
		if _, err := comp.EmitNativeObject(asm.ELF).Get(); err != nil {
			t.Fatalf("ordinary native object API changed: %v", err)
		}
	}
}

// This is the equipped-lane production acceptance test, not a proof simulator.
// The caller supplies only the offline official archive location. Install must
// verify that archive and freshly build the embedded proof closure itself.
// The required-backend runner names every positive case and rejects all skips.
func TestEmitKernelCheckedBitwiseImageBundleReal(t *testing.T) {
	archive := os.Getenv("OAK_BITWISECHECK_LEAN_ARCHIVE")
	if archive == "" {
		if os.Getenv("OAK_REQUIRE_BITWISE_IMAGECHECK") == "1" {
			t.Fatal("OAK_REQUIRE_BITWISE_IMAGECHECK=1 requires OAK_BITWISECHECK_LEAN_ARCHIVE")
		}
		t.Skip("pinned Lean archive unavailable; equipped CI requires the real checked-image-bundle API")
	}
	legacyBefore := checkedImageLegacyAuthoritySnapshot(t)
	ctx, cancel := context.WithTimeout(t.Context(), 45*time.Minute)
	defer cancel()
	installation, err := bitwisecheck.InstallImages(ctx, archive)
	if err != nil {
		t.Fatalf("install pinned checker: %v", err)
	}
	t.Cleanup(func() {
		if err := installation.Close(); err != nil {
			t.Errorf("close pinned checker: %v", err)
		}
	})
	if !installation.Valid() {
		t.Fatal("successful Install returned an invalid checker")
	}

	families := []struct{ name, first, second string }{
		{"bitwise", "x", "y"}, {"Mix9", "left0", "Right9"},
	}
	operations := []struct{ name, token string }{{"and", "&"}, {"or", "|"}, {"xor", "^"}}
	var baseline *bitwisecheck.CheckedImageBundle
	admitted := 0
	t.Run("Canonical", func(t *testing.T) {
		for _, family := range families {
			for _, op := range operations {
				t.Run(family.name+"/"+op.name, func(t *testing.T) {
					original := fmt.Sprintf("%s: (%s: u32, %s: u32): u32 = %s %s %s\n", family.name, family.first, family.second, family.first, op.token, family.second)
					bundle, err := compiler.EmitKernelCheckedBitwiseImageBundle(ctx, installation,
						compiler.SourceText{Path: "original.oak", Text: original}).Get()
					if err != nil {
						t.Fatalf("real production bundle: %v", err)
					}
					assertCheckedBitwiseImageBundle(t, bundle, original, family.name, family.first, family.second, op.name)
					admitted++
					if family.name == "bitwise" && op.name == "and" {
						baseline = bundle
					}
				})
			}
		}
	})
	if admitted != 6 || baseline == nil {
		t.Fatalf("require six real bundles and eighteen final artifacts, got %d bundles", admitted)
	}

	t.Run("LegacyAuthorityUnchanged", func(t *testing.T) {
		if !bytes.Equal(legacyBefore, checkedImageLegacyAuthoritySnapshot(t)) {
			t.Fatal("checked-image admission changed an ordinary native verdict or verified-profile result")
		}
		TestKernelCheckedBitwiseImageBundleDoesNotPromoteLegacyAuthority(t)
	})

	t.Run("SourceBounds", func(t *testing.T) {
		for _, control := range []struct{ id, name, first, second string }{
			{"OneByteName", "f", "x", "y"},
			{"MaximumName", strings.Repeat("N", 256), "x", "y"},
			{"MaximumSource", strings.Repeat("N", 256), strings.Repeat("a", 441), strings.Repeat("b", 441)},
		} {
			t.Run(control.id, func(t *testing.T) {
				original := fmt.Sprintf("%s: (%s: u32, %s: u32): u32 = %s & %s\n", control.name, control.first, control.second, control.first, control.second)
				if control.id == "MaximumSource" && len(original) != bitwisecheck.MaxSourceBytes {
					t.Fatalf("max source fixture is %d bytes", len(original))
				}
				bundle, err := compiler.EmitKernelCheckedBitwiseImageBundle(ctx, installation,
					compiler.SourceText{Path: "bounds.oak", Text: original}).Get()
				if err != nil {
					t.Fatal(err)
				}
				assertCheckedBitwiseImageBundle(t, bundle, original, control.name, control.first, control.second, "and")
			})
		}
	})

	t.Run("SourceRefusals", func(t *testing.T) {
		controls := []struct{ name, source string }{
			{"comment", checkedBitwiseImageSource + "// extra\n"},
			{"main", checkedBitwiseImageSource + "main: (): i32 = 0\n"},
			{"nul", checkedBitwiseImageSource + "\x00"},
			{"name257", strings.Repeat("N", 257) + ": (x: u32, y: u32): u32 = x & y\n"},
			{"extra_declaration", checkedBitwiseImageSource + "other: (a: u32, b: u32): u32 = a & b\n"},
			{"crlf", strings.ReplaceAll(checkedBitwiseImageSource, "\n", "\r\n")},
			{"bom", "\xef\xbb\xbf" + checkedBitwiseImageSource},
			{"wrong_type", strings.ReplaceAll(checkedBitwiseImageSource, "u32", "u64")},
			{"wrong_reference", strings.Replace(checkedBitwiseImageSource, "x & y", "x & x", 1)},
			{"swapped_references", strings.Replace(checkedBitwiseImageSource, "x & y", "y & x", 1)},
			{"spacing", strings.Replace(checkedBitwiseImageSource, " = ", "  = ", 1)},
			{"missing_lf", strings.TrimSuffix(checkedBitwiseImageSource, "\n")},
			{"unsupported_operation", strings.Replace(checkedBitwiseImageSource, " & ", " + ", 1)},
			{"oversized", strings.Repeat("x", bitwisecheck.MaxSourceBytes+1)},
		}
		for _, control := range controls {
			t.Run(control.name, func(t *testing.T) {
				bundle, err := compiler.EmitKernelCheckedBitwiseImageBundle(ctx, installation,
					compiler.SourceText{Path: "refuse.oak", Text: control.source}).Get()
				if err == nil || bundle != nil {
					t.Fatalf("unsupported original bytes must refuse: bundle=%v error=%v", bundle, err)
				}
				if strings.Contains(err.Error(), "kernel admission") && !strings.Contains(err.Error(), "unsupported original image source") && !errors.Is(err, bitwisecheck.ErrBounds) {
					assertBitwiseImageAdmissionRefusal(t, err)
				} else if errors.Is(err, context.Canceled) || errors.Is(err, context.DeadlineExceeded) || errors.Is(err, bitwisecheck.ErrInvalidInstallation) {
					t.Fatalf("source control failed for an unrelated setup/process reason: %v", err)
				}
			})
		}
	})

	t.Run("ArtifactRefusals", func(t *testing.T) {
		controls := []struct {
			name   string
			modify func(*[4][]byte)
		}{
			{"source_operation", func(b *[4][]byte) { b[0] = bytes.Replace(b[0], []byte(" & "), []byte(" | "), 1) }},
			{"source_name", func(b *[4][]byte) { b[0] = bytes.Replace(b[0], []byte("bitwise"), []byte("changed"), 1) }},
			{"wasm_trailing", func(b *[4][]byte) { b[1] = append(b[1], 0) }},
			{"wasm_truncated", func(b *[4][]byte) { b[1] = b[1][:len(b[1])-1] }},
			{"arm_body", func(b *[4][]byte) { b[2][4108] ^= 1 }},
			{"arm_trailing", func(b *[4][]byte) { b[2] = append(b[2], 0) }},
			{"rv_abi", func(b *[4][]byte) { b[3][48] = 0 }},
			{"rv_body", func(b *[4][]byte) { b[3][4112] ^= 1 }},
			{"swapped_targets", func(b *[4][]byte) { b[2], b[3] = b[3], b[2] }},
		}
		for _, control := range controls {
			t.Run(control.name, func(t *testing.T) {
				input := [4][]byte{baseline.SourceBytes(), baseline.WasmBytes(), baseline.ARM64ImageBytes(), baseline.RV64ImageBytes()}
				control.modify(&input)
				bundle, err := installation.CheckImageBundle(ctx, input[0], input[1], input[2], input[3])
				if err == nil || bundle != nil {
					t.Fatalf("one mismatched member must refuse the entire bundle: bundle=%v error=%v", bundle, err)
				}
				assertBitwiseImageAdmissionRefusal(t, err)
			})
		}
	})

	t.Run("CrossProfileInstallationRefusal", func(t *testing.T) {
		// Safe Go conversion can preserve identical private wrapper layout. It
		// must never bypass the installation's distinct internal profile seal.
		value := reflect.ValueOf(installation)
		if value.Type().ConvertibleTo(reflect.TypeFor[*bitwisecheck.Installation]()) {
			objectInstallation := value.Convert(reflect.TypeFor[*bitwisecheck.Installation]()).Interface().(*bitwisecheck.Installation)
			if objectInstallation.Valid() {
				t.Fatal("image installation gained object authority by conversion")
			}
			bundle, err := objectInstallation.CheckBundle(ctx, baseline.SourceBytes(), baseline.WasmBytes(), baseline.ARM64ImageBytes(), baseline.RV64ImageBytes())
			if bundle != nil || !errors.Is(err, bitwisecheck.ErrInvalidInstallation) {
				t.Fatalf("cross-profile object request was not refused: %v", err)
			}
			if err := objectInstallation.Close(); !errors.Is(err, bitwisecheck.ErrInvalidInstallation) {
				t.Fatalf("cross-profile Close was not refused: %v", err)
			}
			if !installation.Valid() {
				t.Fatal("cross-profile handle closed the live image installation")
			}
		}
	})

	t.Run("RelocatableObjectsAreNotImages", func(t *testing.T) {
		objects := [2][]byte{}
		for i, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
			objects[i], err = compiler.New().WithSource("original.oak", checkedBitwiseImageSource).
				WithTarget(target.Target{OS: target.OSLinux, Arch: arch}).EmitNativeObject(asm.ELF).Get()
			if err != nil {
				t.Fatal(err)
			}
		}
		bundle, err := installation.CheckImageBundle(ctx, baseline.SourceBytes(), baseline.WasmBytes(), objects[0], objects[1])
		if bundle != nil || !errors.Is(err, bitwisecheck.ErrBounds) {
			t.Fatalf("ET_REL was not refused as an image: bundle=%v error=%v", bundle, err)
		}
	})

	t.Run("CopyCustody", func(t *testing.T) {
		for _, getter := range []func() []byte{baseline.SourceBytes, baseline.WasmBytes, baseline.ARM64ImageBytes, baseline.RV64ImageBytes} {
			before := getter()
			changed := getter()
			changed[0] ^= 1
			if !bytes.Equal(before, getter()) {
				t.Fatal("mutating a returned copy changed the checked bundle")
			}
		}
		receipt := baseline.Receipt()
		receipt.Assumptions[0] = "changed"
		if baseline.Receipt().Assumptions[0] == "changed" {
			t.Fatal("receipt slices must be copied")
		}
		receipt.Guarantees[0] = "changed"
		receipt.Exclusions[0] = "changed"
		if baseline.Receipt().Guarantees[0] == "changed" || baseline.Receipt().Exclusions[0] == "changed" {
			t.Fatal("receipt guarantee/exclusion slices must be copied")
		}
		for i := range receipt.Roots {
			if len(receipt.Roots[i].Axioms) != 0 {
				receipt.Roots[i].Axioms[0] = "changed"
				if baseline.Receipt().Roots[i].Axioms[0] == "changed" {
					t.Fatal("receipt axiom slices must be copied")
				}
			}
		}
		encoded, err := json.Marshal(baseline)
		if err != nil {
			t.Fatal(err)
		}
		var replay bitwisecheck.CheckedImageBundle
		if err := json.Unmarshal(encoded, &replay); err == nil || replay.Valid() {
			t.Fatal("serialized historical receipt restored checked authority")
		}
		var objectReplay bitwisecheck.CheckedBundle
		if err := json.Unmarshal(encoded, &objectReplay); err == nil || objectReplay.Valid() {
			t.Fatal("image receipt promoted to object authority")
		}
	})

	t.Run("RenamedParametersFreshAdmission", func(t *testing.T) {
		renamed := "bitwise: (left0: u32, Right9: u32): u32 = left0 & Right9\n"
		bundle, err := compiler.EmitKernelCheckedBitwiseImageBundle(ctx, installation,
			compiler.SourceText{Path: "renamed.oak", Text: renamed}).Get()
		if err != nil {
			t.Fatal(err)
		}
		assertCheckedBitwiseImageBundle(t, bundle, renamed, "bitwise", "left0", "Right9", "and")
		if !bytes.Equal(bundle.WasmBytes(), baseline.WasmBytes()) || !bytes.Equal(bundle.ARM64ImageBytes(), baseline.ARM64ImageBytes()) || !bytes.Equal(bundle.RV64ImageBytes(), baseline.RV64ImageBytes()) {
			t.Fatal("consistent parameter renaming should preserve these canonical artifacts")
		}
		if bundle.Receipt().Source == baseline.Receipt().Source {
			t.Fatal("renamed source must carry its own fresh source-bound admission")
		}
	})
	t.Run("Canceled", func(t *testing.T) {
		canceled, stop := context.WithCancel(ctx)
		stop()
		bundle, err := compiler.EmitKernelCheckedBitwiseImageBundle(canceled, installation,
			compiler.SourceText{Text: checkedBitwiseImageSource}).Get()
		if bundle != nil || !errors.Is(err, context.Canceled) {
			t.Fatalf("canceled equipped request did not refuse: %v", err)
		}
	})
	t.Run("StageCancellation", func(t *testing.T) {
		// This failure-only context makes cancellation boundaries deterministic;
		// it never supplies a checker result or creates admission authority.
		for index, stage := range []string{"after core/wasm32 emission", "after linux/arm64 object emission", "after linux/arm64 body proposal", "after linux/arm64 image emission", "after linux/riscv64 object emission", "after linux/riscv64 body proposal", "after linux/riscv64 image emission"} {
			t.Run([]string{"wasm", "arm64_object", "arm64_proposal", "arm64_image", "rv64_object", "rv64_proposal", "rv64_image"}[index], func(t *testing.T) {
				inner, stop := context.WithCancel(ctx)
				defer stop()
				boundary := &cancelAtImageErrContext{Context: inner, cancel: stop, at: int32(index + 2)}
				bundle, err := compiler.EmitKernelCheckedBitwiseImageBundle(boundary, installation,
					compiler.SourceText{Text: checkedBitwiseImageSource}).Get()
				if bundle != nil || !errors.Is(err, context.Canceled) || !strings.Contains(err.Error(), stage) {
					t.Fatalf("missing cancellation boundary %s: bundle=%v error=%v", stage, bundle, err)
				}
			})
		}
	})
	t.Run("Closed", func(t *testing.T) {
		if err := installation.Close(); err != nil {
			t.Fatal(err)
		}
		bundle, err := compiler.EmitKernelCheckedBitwiseImageBundle(ctx, installation,
			compiler.SourceText{Text: checkedBitwiseImageSource}).Get()
		if bundle != nil || !errors.Is(err, bitwisecheck.ErrInvalidInstallation) {
			t.Fatalf("closed checker did not refuse: %v", err)
		}
		if !baseline.Valid() {
			t.Fatal("closing an installation must preserve completed historical bundle admission")
		}
	})
	t.Log("six canonical matrix bundles, eighteen final production artifacts, three audited roots each; refusal, copy, and fresh-source controls used the real pinned checker")
}

func assertBitwiseImageAdmissionRefusal(t *testing.T, err error) {
	t.Helper()
	var exit *exec.ExitError
	// Mutated actual artifacts must fail at a checked proof/auditor boundary,
	// never merely because a process timed out, crashed, or lost its toolchain.
	message := err.Error()
	if !errors.As(err, &exit) || exit.ExitCode() != 1 ||
		!strings.Contains(message, "source image parity refused:") ||
		!strings.Contains(message, "forbidden axiom sorryAx") {
		t.Fatalf("negative control did not reach proof/auditor refusal: %v", err)
	}
}

type cancelAtImageErrContext struct {
	context.Context
	cancel context.CancelFunc
	at     int32
	calls  atomic.Int32
}

func (c *cancelAtImageErrContext) Err() error {
	if c.calls.Add(1) == c.at {
		c.cancel()
	}
	return c.Context.Err()
}

func assertCheckedBitwiseImageBundle(t *testing.T, bundle *bitwisecheck.CheckedImageBundle, source, name, first, second, operation string) {
	t.Helper()
	if !bundle.Valid() || string(bundle.SourceBytes()) != source {
		t.Fatal("missing checked authority or incorrect source snapshot")
	}
	r := bundle.Receipt()
	if r.Schema != bitwisecheck.ImageSchema || r.Profile != bitwisecheck.ImageProfile || r.LeanVersion != bitwisecheck.LeanVersion || r.LeanCommit != bitwisecheck.LeanCommit || r.ArchiveSHA256 != bitwisecheck.ArchiveSHA256 || r.ProofPackage != bitwisecheck.ImageProofPackage || r.ProofSourceSHA256 != leansources.ImageIdentity() || r.ProofSourceSHA256 == leansources.Identity() {
		t.Fatalf("unexpected proof identity: %+v", r)
	}
	if r.Declaration.Name != name || r.Declaration.Parameters != [2]string{first, second} || r.Declaration.Operation != operation || r.Declaration.InputWidths != [2]int{32, 32} || r.Declaration.ResultWidth != 32 {
		t.Fatalf("wrong original-source declaration: %+v", r.Declaration)
	}
	for i, pair := range []struct {
		bytes    []byte
		identity bitwisecheck.ByteIdentity
	}{
		{bundle.SourceBytes(), r.Source}, {bundle.WasmBytes(), r.Wasm}, {bundle.ARM64ImageBytes(), r.ARM64}, {bundle.RV64ImageBytes(), r.RV64},
	} {
		hash := sha256.Sum256(pair.bytes)
		if len(pair.bytes) == 0 || pair.identity.Length != len(pair.bytes) || pair.identity.SHA256 != hex.EncodeToString(hash[:]) {
			t.Fatalf("artifact %d does not match the immutable checked receipt", i)
		}
	}
	for i, expected := range []struct{ target, container, symbol string }{
		{"core/wasm32", "Wasm", name}, {"linux/arm64", "ELF64 ET_EXEC", "oak_" + name}, {"linux/riscv64", "ELF64 ET_EXEC", "oak_" + name},
	} {
		actual := r.Targets[i]
		if i > 0 {
			fileOffset, bodySize, address := 4108, 8, 65548
			if i == 2 {
				fileOffset, bodySize, address = 4112, 36, 65552
			}
			if actual.SectionIndex != 1 || actual.FileOffset != fileOffset || actual.BodySize != bodySize || actual.ELFEntry != 65536 || actual.FunctionAddress != address {
				t.Fatalf("incorrect ELF-entry/named-function distinction: %+v", actual)
			}
		}
		if actual.Target != expected.target || actual.Container != expected.container || actual.Symbol != expected.symbol || actual.ABI == "" {
			t.Fatalf("incorrect complete-artifact target identity: %+v", actual)
		}
	}
	seen := map[string]bool{}
	for i, root := range r.Roots {
		want := "Oak.SourceImageParityRequest." + []string{"admitted", "binding", "all_inputs"}[i]
		if root.Name != want || seen[root.Name] {
			t.Fatalf("missing or duplicate audited root: %+v", r.Roots)
		}
		seen[root.Name] = true
		for _, axiom := range root.Axioms {
			switch axiom {
			case "propext", "Quot.sound", "Classical.choice":
			default:
				t.Fatalf("unexpected axiom %q for %s", axiom, root.Name)
			}
		}
	}
	if len(seen) != 3 || len(r.Assumptions) == 0 || len(r.Exclusions) == 0 || len(r.Guarantees) == 0 {
		t.Fatal("receipt omitted root inventory or model boundaries")
	}
}

// Observe ordinary compiler authority before and after successful image
// admissions, without assuming it is proven or unproven for either backend.
func checkedImageLegacyAuthoritySnapshot(t *testing.T) []byte {
	t.Helper()
	state := map[string]any{}
	for _, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
		comp := compiler.New().WithSource("original.oak", checkedBitwiseImageSource).
			WithTarget(target.Target{OS: target.OSLinux, Arch: arch}).WithNativeBodies().WithNativeAsm()
		lowered, err := comp.Lower().Get()
		if err != nil {
			t.Fatal(err)
		}
		state[arch+"_verdicts"] = lowered.Model.NativeVerdicts
		verified, err := comp.WithVerifiedProfile().EmitNativeObject(asm.ELF).Get()
		state[arch+"_verified_bytes"] = verified
		state[arch+"_verified_error"] = fmt.Sprint(err)
	}
	out, err := json.Marshal(state)
	if err != nil {
		t.Fatal(err)
	}
	return out
}
