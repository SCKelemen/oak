package asm

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func TestNativeTargetClosedBoundary(t *testing.T) {
	for _, arch := range []string{"", "unknown", "amd64", "wasm32", "riscv64", "aarch64", "ARM64"} {
		target, err := ResolveNativeTarget(arch)
		if err == nil || target != (NativeTarget{}) {
			t.Fatalf("resolved %q: %+v, %v", arch, target, err)
		}
		if code, relocs, err := target.Encode(&Function{Arch: arch}); err == nil || code != nil || relocs != nil {
			t.Fatalf("invalid target encoded %q", arch)
		}
		if target.AcceptsRelocation("call26") {
			t.Fatal("zero target admitted relocation")
		}
		if arch != "" {
			if code, relocs, err := EncodeFunction(&Function{Arch: arch}); err == nil || code != nil || relocs != nil {
				t.Fatalf("legacy encoder admitted %q", arch)
			}
			if _, err := WriteObject(ELF, []EncodedFunction{{Symbol: "f", Arch: arch}}); err == nil {
				t.Fatalf("object admitted %q", arch)
			}
		}
	}
	if _, _, err := EncodeFunction(nil); err == nil {
		t.Fatal("nil function admitted")
	}
	for _, arch := range []string{ArchArm64, ArchRV64} {
		target, err := ResolveNativeTarget(arch)
		if err != nil || target.Arch() != arch {
			t.Fatal(arch, target, err)
		}
		for _, fn := range []*Function{nil, {}, {Arch: "unknown"}, {Arch: map[string]string{ArchArm64: ArchRV64, ArchRV64: ArchArm64}[arch]}} {
			if code, relocs, err := target.Encode(fn); err == nil || code != nil || relocs != nil {
				t.Fatalf("%s encoded mismatched function", arch)
			}
		}
		fn := &Function{Arch: arch, Items: []Item{Instruction{Mnemonic: "nop"}}}
		code, relocs, err := target.Encode(fn)
		want := []byte{0x1f, 0x20, 0x03, 0xd5}
		if arch == ArchRV64 {
			want = []byte{0x13, 0, 0, 0}
		}
		if err != nil || len(relocs) != 0 || !bytes.Equal(code, want) {
			t.Fatalf("%s: %x %v %v", arch, code, relocs, err)
		}
	}
	// The legacy empty ARM64 API is explicit and does not mutate its input.
	fn := &Function{Items: []Item{Instruction{Mnemonic: "nop"}}}
	if code, _, err := EncodeFunction(fn); err != nil || !bytes.Equal(code, []byte{0x1f, 0x20, 0x03, 0xd5}) || fn.Arch != "" {
		t.Fatal("legacy ARM64 changed", err)
	}
}

// The legacy encoding adapter may default only the empty spelling; it must
// otherwise agree with the strict selector used by generation and verification.
func TestNativeTargetEncodingAdapter(t *testing.T) {
	for _, arch := range []string{"", ArchArm64, ArchRV64, "unknown", "riscv64", "wasm32", " ARM64"} {
		canonical := arch
		if canonical == "" {
			canonical = ArchArm64
		}
		target, strictErr := ResolveNativeTarget(canonical)
		got, err := encodingArchitecture(arch)
		if (err == nil) != (strictErr == nil) || got != target.Arch() {
			t.Fatalf("adapter %q: %q, %v; strict: %q, %v", arch, got, err, target.Arch(), strictErr)
		}
	}
}

func TestNativeTargetRelocationOwnership(t *testing.T) {
	for _, arch := range []string{ArchArm64, ArchRV64} {
		target, _ := ResolveNativeTarget(arch)
		for _, r := range relocationKindFootprints {
			want := arch == ArchRV64
			if r.kind != "riscv_call_plt" && r.kind != "riscv_pcrel" {
				want = !want
			}
			if target.AcceptsRelocation(r.kind) != want {
				t.Fatalf("%s %s ownership", arch, r.kind)
			}
			// Even a valid footprint and symbol cannot cross the lane boundary.
			_, err := layOut([]EncodedFunction{{Symbol: "f", Arch: arch, Bytes: make([]byte, r.width), Relocs: []Relocation{{Kind: r.kind, Symbol: "g"}}}})
			if (err == nil) != want {
				t.Fatalf("%s %s layout: %v", arch, r.kind, err)
			}
		}
		if target.AcceptsRelocation("future_relocation") {
			t.Fatal("unknown relocation admitted")
		}
	}
}

// Finite pins bind production selection/ownership results to the Lean model.
// They supplement the universal model theorems, not Go implementation refinement.
func TestNativeTargetLeanCorrespondence(t *testing.T) {
	var pins []string
	for _, arch := range []string{ArchArm64, ArchRV64, "", "unknown", "riscv64", "wasm32"} {
		target, err := ResolveNativeTarget(arch)
		result := "none"
		if err == nil {
			result = "some ." + target.Arch()
		}
		pins = append(pins, fmt.Sprintf("example : resolve %q = %s := by decide", arch, result))
		for _, r := range append(append([]relocationKindFootprint(nil), relocationKindFootprints[:]...), relocationKindFootprint{kind: "unknown"}) {
			pins = append(pins, fmt.Sprintf("example : acceptsRelocation (resolve %q) %q = %v := by decide", arch, r.kind, target.AcceptsRelocation(r.kind)))
		}
	}
	path := filepath.Join(t.TempDir(), "NativeTargetPins.lean")
	source := "import Oak.NativeTarget\nopen Oak.NativeTarget\n" + strings.Join(pins, "\n") + "\n"
	if err := os.WriteFile(path, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_NATIVE_TARGET_LEAN") != "" {
			t.Fatal("native target correspondence requires lake on PATH")
		}
		t.Skip("lake not on PATH; formal CI checks production pins")
	}
	buildLeanImports(t, lake, path)
	cmd := exec.Command(lake, "env", "lean", path)
	cmd.Dir = filepath.Join("..", "spec", "lean")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("Lean native target pins: %v\n%s", err, out)
	}
}
