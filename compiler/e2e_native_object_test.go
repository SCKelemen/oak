package compiler

import (
	"bytes"
	"debug/elf"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/toolchain"
)

// Freestanding modules realized natively (docs/spec/94-assembler.md §9): a
// module whose every body is in the native subset is one relocatable
// object of Oak's own code (`oak build -link oak` on a freestanding
// target); a module with bodies left to C is the C object and the Oak
// companion object partially linked by the driver into one relocatable
// object, so the pilot links one file as before.

func TestE2ENativeObjectAlone(t *testing.T) {
	for _, tgt := range []target.Target{
		{OS: target.OSFreestanding, Arch: target.ArchArm64},
		{OS: target.OSFreestanding, Arch: target.ArchRiscv64},
	} {
		t.Run(tgt.String(), func(t *testing.T) {
			object, err := New().WithSource("native.oak", nativeProgram).WithTarget(tgt).EmitNativeObject(asm.ELF).Get()
			if err != nil {
				t.Fatalf("native object: %v", err)
			}
			file, err := elf.NewFile(bytes.NewReader(object))
			if err != nil {
				t.Fatal(err)
			}
			if file.Type != elf.ET_REL {
				t.Fatalf("type %v, want ET_REL", file.Type)
			}
			symbols, err := file.Symbols()
			if err != nil {
				t.Fatal(err)
			}
			names := map[string]bool{}
			for _, s := range symbols {
				names[s.Name] = true
			}
			for _, want := range []string{"oak_main", "oak_mix", "oak_sum_to", "oak_fact"} {
				if !names[want] {
					t.Errorf("%s: the object lacks %s; symbols %v", tgt, want, names)
				}
			}
		})
	}
	// A module with a body left to C is refused by name.
	source := "scale: (x: f64) -> f64 = x * 2.0\n\nmain: (): i32 {\n  scale(1.0) == 2.0 ? 0 | 1\n}\n"
	_, err := New().WithSource("native.oak", source).WithTarget(target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}).EmitNativeObject(asm.ELF).Get()
	if err == nil || !strings.Contains(err.Error(), "scale stayed with the C backend") {
		t.Fatalf("a module with a C body was written as a native object: %v", err)
	}
}

// The mixed module: the C object and the companion object joined by the
// driver's partial link, as `oak build -target freestanding/arm64 -native
// -asm native` does.
func TestE2EFreestandingPartialLink(t *testing.T) {
	tgt := target.Target{OS: target.OSFreestanding, Arch: target.ArchArm64}
	drv, err := toolchain.Resolve(tgt, toolchain.Options{}, nil, nil)
	if err != nil || drv.Kind != "zig" {
		t.Skipf("no zig for %s (%v)", tgt, err)
	}
	// Floating point stays with C on no target here, so a span of records
	// (outside both lanes' subsets today) is the body left to C.
	source := nativeProgram + "\nRec: type = struct { a: u32, b: u32 }\n\nfirst_a: (v: []Rec) -> u32 = v[u32(0)].a\n"
	native, err := New().WithSource("native.oak", source).WithTarget(tgt).WithNativeBodies().EmitNative(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	if native.Object == nil {
		t.Fatal("no companion object")
	}
	dir := t.TempDir()
	cPath, cObject, oakObject, merged := filepath.Join(dir, "m.c"), filepath.Join(dir, "m_c.o"), filepath.Join(dir, "m_oak.o"), filepath.Join(dir, "m.o")
	if err := os.WriteFile(cPath, []byte(native.C), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(oakObject, native.Object, 0o644); err != nil {
		t.Fatal(err)
	}
	compile := append(append([]string{}, drv.Args...), "-std=c99", "-O1", "-ffp-contract=off", "-c", "-o", cObject, cPath)
	if out, err := exec.Command(drv.Path, compile...).CombinedOutput(); err != nil {
		t.Fatalf("compile: %v\n%s", err, out)
	}
	link := append(append([]string{}, drv.Args...), "-nostdlib", "-r", "-o", merged, cObject, oakObject)
	if out, err := exec.Command(drv.Path, link...).CombinedOutput(); err != nil {
		t.Fatalf("partial link: %v\n%s", err, out)
	}
	file, err := elf.Open(merged)
	if err != nil {
		t.Fatal(err)
	}
	defer file.Close()
	symbols, err := file.Symbols()
	if err != nil {
		t.Fatal(err)
	}
	defined := map[string]bool{}
	for _, s := range symbols {
		if s.Section != elf.SHN_UNDEF {
			defined[s.Name] = true
		}
	}
	for _, want := range []string{"oak_mix", "oak_first_a", "oak_main"} {
		if !defined[want] {
			t.Errorf("the merged object lacks %s", want)
		}
	}
}
