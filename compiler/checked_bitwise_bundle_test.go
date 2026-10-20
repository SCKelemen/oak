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
	"strings"
	"sync/atomic"
	"testing"
	"time"

	"github.com/SCKelemen/oak/bitwisecheck"
	"github.com/SCKelemen/oak/compiler"
)

const checkedBitwiseSource = "bitwise: (x: u32, y: u32): u32 = x & y\n"

func TestEmitKernelCheckedBitwiseBundleRefusesInvalidInstallation(t *testing.T) {
	for _, tc := range []struct {
		name         string
		installation *bitwisecheck.Installation
	}{{"nil", nil}, {"zero", new(bitwisecheck.Installation)}} {
		t.Run(tc.name, func(t *testing.T) {
			bundle, err := compiler.EmitKernelCheckedBitwiseBundle(t.Context(), tc.installation,
				compiler.SourceText{Path: "original.oak", Text: checkedBitwiseSource}).Get()
			if bundle != nil || !errors.Is(err, bitwisecheck.ErrInvalidInstallation) {
				t.Fatalf("uninitialized checker must refuse: bundle=%v error=%v", bundle, err)
			}
		})
	}
}

func TestEmitKernelCheckedBitwiseBundleRefusesCanceledContext(t *testing.T) {
	ctx, cancel := context.WithCancel(t.Context())
	cancel()
	bundle, err := compiler.EmitKernelCheckedBitwiseBundle(ctx, nil, compiler.SourceText{Text: checkedBitwiseSource}).Get()
	if bundle != nil || !errors.Is(err, context.Canceled) {
		t.Fatalf("canceled request must refuse: bundle=%v error=%v", bundle, err)
	}
	bundle, err = compiler.EmitKernelCheckedBitwiseBundle(nil, nil, compiler.SourceText{Text: checkedBitwiseSource}).Get()
	if bundle != nil || err == nil {
		t.Fatalf("nil context must refuse: bundle=%v error=%v", bundle, err)
	}
}

func TestKernelCheckedBitwiseBundleDoesNotPromoteLegacyAuthority(t *testing.T) {
	comp := compiler.New().WithSource("original.oak", checkedBitwiseSource)
	module, err := comp.EmitWasm().Get()
	if err != nil {
		t.Fatal(err)
	}
	if module.TranslationVerified || module.ByteValidation == nil {
		t.Fatal("ordinary Wasm emission authority changed")
	}
	if _, err := comp.WithVerifiedProfile().EmitWasm().Get(); err == nil {
		t.Fatal("checked bundle API must not enable legacy verified Wasm emission")
	}
	if new(bitwisecheck.CheckedBundle).Valid() {
		t.Fatal("zero bundle cannot carry admission authority")
	}
}

// This is the equipped-lane production acceptance test, not a proof simulator.
// The caller supplies only the offline official archive location. Install must
// verify that archive and freshly build the embedded proof closure itself.
// The required-backend runner names every positive case and rejects all skips.
func TestEmitKernelCheckedBitwiseBundleReal(t *testing.T) {
	archive := os.Getenv("OAK_BITWISECHECK_LEAN_ARCHIVE")
	if archive == "" {
		if os.Getenv("OAK_REQUIRE_BITWISECHECK") == "1" {
			t.Fatal("OAK_REQUIRE_BITWISECHECK=1 requires OAK_BITWISECHECK_LEAN_ARCHIVE")
		}
		t.Skip("pinned Lean archive unavailable; equipped CI requires the real checked-bundle API")
	}
	ctx, cancel := context.WithTimeout(t.Context(), 45*time.Minute)
	defer cancel()
	installation, err := bitwisecheck.Install(ctx, archive)
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
	var baseline *bitwisecheck.CheckedBundle
	admitted := 0
	t.Run("Canonical", func(t *testing.T) {
		for _, family := range families {
			for _, op := range operations {
				t.Run(family.name+"/"+op.name, func(t *testing.T) {
					original := fmt.Sprintf("%s: (%s: u32, %s: u32): u32 = %s %s %s\n", family.name, family.first, family.second, family.first, op.token, family.second)
					bundle, err := compiler.EmitKernelCheckedBitwiseBundle(ctx, installation,
						compiler.SourceText{Path: "original.oak", Text: original}).Get()
					if err != nil {
						t.Fatalf("real production bundle: %v", err)
					}
					assertCheckedBitwiseBundle(t, bundle, original, family.name, family.first, family.second, op.name)
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

	t.Run("SourceRefusals", func(t *testing.T) {
		controls := []struct{ name, source string }{
			{"comment", checkedBitwiseSource + "// extra\n"},
			{"extra_declaration", checkedBitwiseSource + "other: (a: u32, b: u32): u32 = a & b\n"},
			{"crlf", strings.ReplaceAll(checkedBitwiseSource, "\n", "\r\n")},
			{"bom", "\xef\xbb\xbf" + checkedBitwiseSource},
			{"wrong_type", strings.ReplaceAll(checkedBitwiseSource, "u32", "u64")},
			{"wrong_reference", strings.Replace(checkedBitwiseSource, "x & y", "x & x", 1)},
			{"swapped_references", strings.Replace(checkedBitwiseSource, "x & y", "y & x", 1)},
			{"spacing", strings.Replace(checkedBitwiseSource, " = ", "  = ", 1)},
			{"missing_lf", strings.TrimSuffix(checkedBitwiseSource, "\n")},
			{"unsupported_operation", strings.Replace(checkedBitwiseSource, " & ", " + ", 1)},
			{"oversized", strings.Repeat("x", bitwisecheck.MaxSourceBytes+1)},
		}
		for _, control := range controls {
			t.Run(control.name, func(t *testing.T) {
				bundle, err := compiler.EmitKernelCheckedBitwiseBundle(ctx, installation,
					compiler.SourceText{Path: "refuse.oak", Text: control.source}).Get()
				if err == nil || bundle != nil {
					t.Fatalf("unsupported original bytes must refuse: bundle=%v error=%v", bundle, err)
				}
				if strings.Contains(err.Error(), "kernel admission") {
					assertBitwiseAdmissionRefusal(t, err)
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
			{"arm_body", func(b *[4][]byte) { b[2][64] ^= 1 }},
			{"arm_trailing", func(b *[4][]byte) { b[2] = append(b[2], 0) }},
			{"rv_abi", func(b *[4][]byte) { b[3][48] = 0 }},
			{"rv_body", func(b *[4][]byte) { b[3][64] ^= 1 }},
			{"swapped_targets", func(b *[4][]byte) { b[2], b[3] = b[3], b[2] }},
		}
		for _, control := range controls {
			t.Run(control.name, func(t *testing.T) {
				input := [4][]byte{baseline.SourceBytes(), baseline.WasmBytes(), baseline.ARM64Bytes(), baseline.RV64Bytes()}
				control.modify(&input)
				bundle, err := installation.CheckBundle(ctx, input[0], input[1], input[2], input[3])
				if err == nil || bundle != nil {
					t.Fatalf("one mismatched member must refuse the entire bundle: bundle=%v error=%v", bundle, err)
				}
				assertBitwiseAdmissionRefusal(t, err)
			})
		}
	})

	t.Run("CopyCustody", func(t *testing.T) {
		for _, getter := range []func() []byte{baseline.SourceBytes, baseline.WasmBytes, baseline.ARM64Bytes, baseline.RV64Bytes} {
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
		var replay bitwisecheck.CheckedBundle
		if err := json.Unmarshal(encoded, &replay); err == nil || replay.Valid() {
			t.Fatal("serialized historical receipt restored checked authority")
		}
	})

	t.Run("RenamedParametersFreshAdmission", func(t *testing.T) {
		renamed := "bitwise: (left0: u32, Right9: u32): u32 = left0 & Right9\n"
		bundle, err := compiler.EmitKernelCheckedBitwiseBundle(ctx, installation,
			compiler.SourceText{Path: "renamed.oak", Text: renamed}).Get()
		if err != nil {
			t.Fatal(err)
		}
		assertCheckedBitwiseBundle(t, bundle, renamed, "bitwise", "left0", "Right9", "and")
		if !bytes.Equal(bundle.WasmBytes(), baseline.WasmBytes()) || !bytes.Equal(bundle.ARM64Bytes(), baseline.ARM64Bytes()) || !bytes.Equal(bundle.RV64Bytes(), baseline.RV64Bytes()) {
			t.Fatal("consistent parameter renaming should preserve these canonical artifacts")
		}
		if bundle.Receipt().Source == baseline.Receipt().Source {
			t.Fatal("renamed source must carry its own fresh source-bound admission")
		}
	})
	t.Run("Canceled", func(t *testing.T) {
		canceled, stop := context.WithCancel(ctx)
		stop()
		bundle, err := compiler.EmitKernelCheckedBitwiseBundle(canceled, installation,
			compiler.SourceText{Text: checkedBitwiseSource}).Get()
		if bundle != nil || !errors.Is(err, context.Canceled) {
			t.Fatalf("canceled equipped request did not refuse: %v", err)
		}
	})
	t.Run("StageCancellation", func(t *testing.T) {
		// This failure-only context makes cancellation boundaries deterministic;
		// it never supplies a checker result or creates admission authority.
		for index, stage := range []string{"after core/wasm32 emission", "after linux/arm64 emission", "after linux/riscv64 emission"} {
			t.Run([]string{"wasm", "arm64", "rv64"}[index], func(t *testing.T) {
				inner, stop := context.WithCancel(ctx)
				defer stop()
				boundary := &cancelAtErrContext{Context: inner, cancel: stop, at: int32(index + 2)}
				bundle, err := compiler.EmitKernelCheckedBitwiseBundle(boundary, installation,
					compiler.SourceText{Text: checkedBitwiseSource}).Get()
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
		bundle, err := compiler.EmitKernelCheckedBitwiseBundle(ctx, installation,
			compiler.SourceText{Text: checkedBitwiseSource}).Get()
		if bundle != nil || !errors.Is(err, bitwisecheck.ErrInvalidInstallation) {
			t.Fatalf("closed checker did not refuse: %v", err)
		}
		if !baseline.Valid() {
			t.Fatal("closing an installation must preserve completed historical bundle admission")
		}
	})
	t.Log("six canonical matrix bundles, eighteen final production artifacts, three audited roots each; refusal, copy, and fresh-source controls used the real pinned checker")
}

func assertBitwiseAdmissionRefusal(t *testing.T, err error) {
	t.Helper()
	var exit *exec.ExitError
	// A failed admission proof can be explicitly disproved or reduction-stuck.
	// Both must reach the auditor's forbidden-placeholder refusal. This proves
	// no checked bundle escaped; it does not label a stuck proof semantic
	// rejection. The independent auditor gate also proves check = none controls.
	message := err.Error()
	proofFailure := strings.Contains(message, "proved that the proposition") ||
		strings.Contains(message, "did not reduce to `isTrue` or `isFalse`")
	auditRefusal := strings.Contains(message, "checked bundle refused: Oak.CheckedBundleRequest.admitted depends on forbidden axiom sorryAx")
	if !errors.As(err, &exit) || exit.ExitCode() != 1 || !proofFailure || !auditRefusal {
		t.Fatalf("negative control did not reach proof/auditor refusal: %v", err)
	}
}

type cancelAtErrContext struct {
	context.Context
	cancel context.CancelFunc
	at     int32
	calls  atomic.Int32
}

func (c *cancelAtErrContext) Err() error {
	if c.calls.Add(1) == c.at {
		c.cancel()
	}
	return c.Context.Err()
}

func assertCheckedBitwiseBundle(t *testing.T, bundle *bitwisecheck.CheckedBundle, source, name, first, second, operation string) {
	t.Helper()
	if !bundle.Valid() || string(bundle.SourceBytes()) != source {
		t.Fatal("missing checked authority or incorrect source snapshot")
	}
	r := bundle.Receipt()
	if r.Schema != bitwisecheck.Schema || r.Profile != bitwisecheck.Profile || r.LeanVersion != bitwisecheck.LeanVersion || r.LeanCommit != bitwisecheck.LeanCommit || r.ArchiveSHA256 != bitwisecheck.ArchiveSHA256 || r.ProofPackage != bitwisecheck.ProofPackage || len(r.ProofSourceSHA256) != 64 {
		t.Fatalf("unexpected proof identity: %+v", r)
	}
	if r.Declaration.Name != name || r.Declaration.Parameters != [2]string{first, second} || r.Declaration.Operation != operation || r.Declaration.InputWidths != [2]int{32, 32} || r.Declaration.ResultWidth != 32 {
		t.Fatalf("wrong original-source declaration: %+v", r.Declaration)
	}
	for i, pair := range []struct {
		bytes    []byte
		identity bitwisecheck.ByteIdentity
	}{
		{bundle.SourceBytes(), r.Source}, {bundle.WasmBytes(), r.Wasm}, {bundle.ARM64Bytes(), r.ARM64}, {bundle.RV64Bytes(), r.RV64},
	} {
		hash := sha256.Sum256(pair.bytes)
		if len(pair.bytes) == 0 || pair.identity.Length != len(pair.bytes) || pair.identity.SHA256 != hex.EncodeToString(hash[:]) {
			t.Fatalf("artifact %d does not match the immutable checked receipt", i)
		}
	}
	for i, expected := range []struct{ target, container, symbol string }{
		{"core/wasm32", "Wasm", name}, {"linux/arm64", "ELF64 ET_REL", "oak_" + name}, {"linux/riscv64", "ELF64 ET_REL", "oak_" + name},
	} {
		actual := r.Targets[i]
		if actual.Target != expected.target || actual.Container != expected.container || actual.Symbol != expected.symbol || actual.ABI == "" {
			t.Fatalf("incorrect complete-artifact target identity: %+v", actual)
		}
	}
	seen := map[string]bool{}
	for i, root := range r.Roots {
		want := "Oak.CheckedBundleRequest." + []string{"admitted", "binding", "all_inputs"}[i]
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
	if len(seen) != 3 || len(r.Assumptions) == 0 || len(r.Exclusions) == 0 {
		t.Fatal("receipt omitted root inventory or model boundaries")
	}
}
