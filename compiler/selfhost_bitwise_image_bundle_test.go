package compiler

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/binary"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/bitwisecheck"
	leansources "github.com/SCKelemen/oak/spec/lean"
	"github.com/SCKelemen/oak/target"
)

// Missing tools remain optional for ordinary development, but cannot make the
// equipped producer gate pass through the generic E2E helper's skip path.
func requireSelfhostImageCC(t *testing.T) {
	t.Helper()
	if os.Getenv("OAK_REQUIRE_SELFHOST_IMAGE_PRODUCERS") == "1" {
		if _, err := exec.LookPath("cc"); err != nil {
			t.Fatal("OAK_REQUIRE_SELFHOST_IMAGE_PRODUCERS=1 requires cc")
		}
	}
}

type selfhostImageTuple struct {
	name, first, second, operation string
	op                             int
	// Original source, complete Wasm, complete ARM ELF, complete RV ELF.
	// The artifact slices below are exclusively captured compiled-Oak output.
	raw [4][]byte
}

func selfhostImageTuples(t *testing.T) []selfhostImageTuple {
	t.Helper()
	requireSelfhostImageCC(t)
	var tuples []selfhostImageTuple
	var native []selfhostBitwiseELFCase
	for _, family := range [][3]string{{"bitwise", "x", "y"}, {"Mix9", "left", "right"}} {
		for i, op := range [][2]string{{"and", "&"}, {"or", "|"}, {"xor", "^"}} {
			original := fmt.Sprintf("%s: (%s: u32, %s: u32): u32 = %s %s %s\n", family[0], family[1], family[2], family[1], op[1], family[2])
			tc := selfhostImageTuple{name: family[0], first: family[1], second: family[2], operation: op[0], op: i + 1}
			tc.raw[0] = []byte(original)
			// The Go driver supplies only name/op/body proposals, never a source
			// compiler claim. All envelope bytes are written by the Oak routines.
			tc.raw[1] = captureSelfhostBitwiseWasm(t, uint32(tc.op), []byte(tc.name), 320)
			tuples = append(tuples, tc)
			for _, arch := range []uint32{1, 2} {
				native = append(native, selfhostBitwiseELFCase{label: tc.name + "/" + tc.operation,
					name: []byte(tc.name), text: selfhostBitwiseLinkedText(arch, tc.op), arch: arch, capacity: 5120})
			}
		}
	}
	buffers, lengths := selfhostBitwiseELFRun(t, native)
	for n, tc := range native {
		length := lengths[n]
		if length == 0 || uint64(length) > uint64(len(buffers[n])) {
			t.Fatalf("%s: invalid captured native length %d", tc.label, length)
		}
		for offset := int(length); offset < len(buffers[n]); offset++ {
			if buffers[n][offset] != byte(offset%251+1) {
				t.Fatalf("%s: changed native suffix at %d", tc.label, offset)
			}
		}
		// The Oak-reported boundary selects the actual file. No trimming,
		// re-encoding, Go metadata, gap normalization or ELF reconstruction.
		tuples[n/2].raw[2+n%2] = bytes.Clone(buffers[n][:length])
	}
	return tuples
}

// This oracle freshly compiles the SAME original source snapshot, not a
// reconstructed name/op source. It cannot supply any input to admission.
func selfhostImageFreshReferences(t *testing.T, original []byte, name string) [3][]byte {
	t.Helper()
	var reference [3][]byte
	module, err := New().WithSource("original.oak", string(original)).EmitWasm().Get()
	if err != nil {
		t.Fatal(err)
	}
	if module.TranslationVerified || module.ByteValidation == nil {
		t.Fatal("ordinary Wasm authority changed")
	}
	reference[0] = module.Bytes
	for n, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
		object, err := New().WithSource("original.oak", string(original)).
			WithTarget(target.Target{OS: target.OSLinux, Arch: arch}).EmitNativeObject(asm.ELF).Get()
		if err != nil {
			t.Fatal(err)
		}
		body, err := checkedImageProposeBody(object, "oak_"+name, arch)
		if err != nil {
			t.Fatal(err)
		}
		reference[n+1], err = asm.WriteExecutable([]asm.EncodedFunction{body}, asm.ExecutableOptions{
			OS: asm.OSLinux, Arch: body.Arch, Entry: "oak_" + name, RV64FloatABI: "double",
		})
		if err != nil {
			t.Fatal(err)
		}
	}
	return reference
}

func assertSelfhostImageParity(t *testing.T, tc selfhostImageTuple) {
	t.Helper()
	references := selfhostImageFreshReferences(t, tc.raw[0], tc.name)
	for n, reference := range references {
		selfhostBitwiseELFEqual(t, []string{"complete Wasm", "complete ARM ELF", "complete RV ELF"}[n], tc.raw[n+1], reference)
	}
	for n, raw := range tc.raw {
		t.Logf("raw %s length=%d sha256=%x", []string{"original source", "Oak Wasm", "Oak ARM ELF", "Oak RV ELF"}[n], len(raw), sha256.Sum256(raw))
	}
}

func TestE2ESelfHostedBitwiseImageBytes(t *testing.T) {
	for _, tc := range selfhostImageTuples(t) {
		t.Run(tc.name+"/"+tc.operation, func(t *testing.T) { assertSelfhostImageParity(t, tc) })
	}
}

func TestSelfHostedBitwiseImageBundleReal(t *testing.T) {
	archive := os.Getenv("OAK_BITWISECHECK_LEAN_ARCHIVE")
	if archive == "" {
		if os.Getenv("OAK_REQUIRE_BITWISE_IMAGECHECK") == "1" || os.Getenv("OAK_REQUIRE_SELFHOST_IMAGE_PRODUCERS") == "1" {
			t.Fatal("required raw-image admission needs OAK_BITWISECHECK_LEAN_ARCHIVE")
		}
		t.Skip("pinned Lean archive unavailable; equipped CI requires raw Oak image admission")
	}
	tuples := selfhostImageTuples(t)
	ctx, cancel := context.WithTimeout(t.Context(), 55*time.Minute)
	defer cancel()
	installation, err := bitwisecheck.InstallImages(ctx, archive)
	if err != nil {
		t.Fatalf("install unchanged pinned image checker: %v", err)
	}
	t.Cleanup(func() {
		if err := installation.Close(); err != nil {
			t.Errorf("close image checker: %v", err)
		}
	})
	admitted := 0
	t.Run("Canonical", func(t *testing.T) {
		for _, tc := range tuples {
			t.Run(tc.name+"/"+tc.operation, func(t *testing.T) {
				assertSelfhostImageParity(t, tc)
				// Deliberately call the unchanged checker directly. The compiler
				// convenience bundle API would regenerate Go artifacts instead.
				bundle, err := installation.CheckImageBundle(ctx, tc.raw[0], tc.raw[1], tc.raw[2], tc.raw[3])
				if err != nil || !bundle.Valid() {
					t.Fatalf("actual Oak artifacts were not admitted: %v", err)
				}
				got := [4][]byte{bundle.SourceBytes(), bundle.WasmBytes(), bundle.ARM64ImageBytes(), bundle.RV64ImageBytes()}
				r := bundle.Receipt()
				identities := [4]bitwisecheck.ByteIdentity{r.Source, r.Wasm, r.ARM64, r.RV64}
				for n := range tc.raw {
					selfhostBitwiseELFEqual(t, "admitted owned bytes", got[n], tc.raw[n])
					if identities[n].Length != len(tc.raw[n]) || identities[n].SHA256 != fmt.Sprintf("%x", sha256.Sum256(tc.raw[n])) {
						t.Fatal("receipt identity differs from actual captured bytes")
					}
				}
				if r.Declaration.Name != tc.name || r.Declaration.Parameters != [2]string{tc.first, tc.second} || r.Declaration.Operation != tc.operation || r.Profile != bitwisecheck.ImageProfile || r.ProofSourceSHA256 != leansources.ImageIdentity() {
					t.Fatalf("original source or unchanged checker identity differs: %+v", r)
				}
				t.Logf("admitted profile=%s proof_source_sha256=%s Lean=%s archive_sha256=%s", r.Profile, r.ProofSourceSHA256, r.LeanVersion, r.ArchiveSHA256)
				for n, root := range r.Roots {
					if root.Name != "Oak.SourceImageParityRequest."+[]string{"admitted", "binding", "all_inputs"}[n] {
						t.Fatal("missing checked admission root")
					}
					for _, axiom := range root.Axioms {
						switch axiom {
						case "propext", "Quot.sound", "Classical.choice":
						default:
							t.Fatalf("unexpected axiom %q for %s", axiom, root.Name)
						}
					}
					t.Logf("checked root=%s axioms=%v", root.Name, root.Axioms)
				}
				// Optional diagnostic export retains the exact captured files;
				// a serialized receipt never restores checked authority.
				if dir := os.Getenv("OAK_SELFHOST_IMAGE_CORPUS_OUT"); dir != "" {
					if err := os.MkdirAll(dir, 0o755); err != nil {
						t.Fatal(err)
					}
					for n, suffix := range []string{".oak", ".wasm", ".arm64.elf", ".rv64.elf"} {
						if err := os.WriteFile(filepath.Join(dir, tc.name+"-"+tc.operation+suffix), tc.raw[n], 0o600); err != nil {
							t.Fatal(err)
						}
					}
					receipt, err := json.MarshalIndent(r, "", "  ")
					if err != nil {
						t.Fatal(err)
					}
					if err := os.WriteFile(filepath.Join(dir, tc.name+"-"+tc.operation+".receipt.json"), receipt, 0o600); err != nil {
						t.Fatal(err)
					}
				}
				admitted++
			})
		}
	})
	if admitted != 6 {
		t.Fatalf("require six original tuples and eighteen actual complete Oak artifacts; admitted %d", admitted)
	}
	t.Run("Refusals", func(t *testing.T) {
		for _, control := range selfhostImageMutations() {
			t.Run(control.name, func(t *testing.T) {
				var raw [4][]byte
				for n := range raw {
					raw[n] = bytes.Clone(tuples[0].raw[n])
				}
				control.modify(&raw)
				bundle, err := installation.CheckImageBundle(ctx, raw[0], raw[1], raw[2], raw[3])
				var exit *exec.ExitError
				if bundle != nil || err == nil || !errors.As(err, &exit) || exit.ExitCode() != 1 ||
					!strings.Contains(err.Error(), "source image parity refused:") || !strings.Contains(err.Error(), "forbidden axiom sorryAx") {
					t.Fatalf("mutated actual output must reach proof/auditor refusal, not timeout, crash or setup failure: bundle=%v error=%v", bundle, err)
				}
			})
		}
	})
	t.Log("six raw compiled-Oak tuples admitted directly; complete fresh Go parity and proof/auditor mutation refusals; no producer-refinement or source-compiler claim")
}

type selfhostImageMutation struct {
	name   string
	modify func(*[4][]byte)
}

func selfhostImageMutations() []selfhostImageMutation {
	controls := []selfhostImageMutation{
		{"source_name_replay", func(raw *[4][]byte) { raw[0] = bytes.Replace(raw[0], []byte("bitwise"), []byte("changed"), 1) }},
		{"source_operation_replay", func(raw *[4][]byte) { raw[0] = bytes.Replace(raw[0], []byte(" & "), []byte(" | "), 1) }},
		{"wasm_name", func(raw *[4][]byte) { raw[1][bytes.Index(raw[1], []byte("bitwise"))] ^= 1 }},
		{"wasm_body", func(raw *[4][]byte) { raw[1][len(raw[1])-2] ^= 1 }},
		{"wasm_truncated", func(raw *[4][]byte) { raw[1] = raw[1][:len(raw[1])-1] }},
		{"wasm_trailing", func(raw *[4][]byte) { raw[1] = append(raw[1], 0) }},
	}
	for n, arch := range []string{"arm", "rv"} {
		member, stub, load := n+2, 12, 32
		if n == 1 {
			stub, load = 16, 64
		}
		for _, change := range []struct {
			name   string
			offset int
		}{{"startup", 4096}, {"body", 4096 + stub}, {"entry", 24}, {"flags", 48},
			{"symbol", 4096 + load + 24 + 8}, {"padding", 4096 + load - 1}} {
			controls = append(controls, selfhostImageMutation{arch + "_" + change.name,
				func(raw *[4][]byte) { raw[member][change.offset] ^= 1 }})
		}
		controls = append(controls,
			selfhostImageMutation{arch + "_name", func(raw *[4][]byte) { raw[member][bytes.Index(raw[member], []byte("oak_bitwise"))+4] ^= 1 }},
			selfhostImageMutation{arch + "_section", func(raw *[4][]byte) {
				offset := binary.LittleEndian.Uint64(raw[member][40:48])
				raw[member][offset+64+4] ^= 1
			}},
			selfhostImageMutation{arch + "_truncated", func(raw *[4][]byte) { raw[member] = raw[member][:len(raw[member])-1] }},
			selfhostImageMutation{arch + "_trailing", func(raw *[4][]byte) { raw[member] = append(raw[member], 0) }},
		)
	}
	return controls
}
