package codegen

import (
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

func TestAArch64SimdWithoutNeonPreservesMachineIntrinsics(t *testing.T) {
	clang := requireAArch64Clang(t)
	generated := generateSourceC(t, `
package main
fn probe(address: u64, input: simd.U8x16) -> u64 {
  limited: simd.U8x16 = simd.min_u8x16(input, simd.splat_u8x16(u8(7)))
  present: Bool = simd.any_u8x16(limited)
  value: u32 = present ? u32(1) | u32(0)
  arm64.mmio_write_wo_u32(arm64.mmio_unsafe_wo_u32(address), value)
  arm64.isb()
  arm64.read_currentel()
}
`)
	dir := t.TempDir()
	cPath := filepath.Join(dir, "probe.c")
	if err := os.WriteFile(cPath, []byte(generated), 0o600); err != nil {
		t.Fatal(err)
	}
	for _, name := range []string{"scalar", "forced-scalar", "neon"} {
		neon := name == "neon"
		t.Run(name, func(t *testing.T) {
			sPath := filepath.Join(dir, name+".s")
			args := []string{"--target=aarch64-none-elf", "-march=armv8-a", "-std=c11", "-O2", "-ffreestanding", "-Wall", "-Wextra", "-Werror", "-Wno-unused-function"}
			if !neon {
				args = append(args, "-mgeneral-regs-only", "-mstrict-align")
			}
			if name == "forced-scalar" {
				// Some build drivers advertise NEON to preprocessing despite
				// disabling it for code generation. The kernel override wins.
				args = append(args, "-D__ARM_NEON=1", "-DOAK_SCALAR_SIMD=1")
			}
			args = append(args, "-S", cPath, "-o", sPath)
			if output, err := exec.Command(clang, args...).CombinedOutput(); err != nil {
				t.Fatalf("cross-compile: %v\n%s", err, output)
			}
			data, err := os.ReadFile(sPath)
			if err != nil {
				t.Fatal(err)
			}
			body := aarch64FunctionBody(t, strings.ToLower(string(data)), "probe")
			for _, instruction := range []string{"mrs", "isb", "str"} {
				requireInstruction(t, body, instruction)
			}
			if !strings.Contains(body, "currentel") {
				t.Fatalf("CurrentEL access disappeared:\n%s", body)
			}
			vectorRegister := regexp.MustCompile(`\b[vdqshb][0-9]+\b`)
			if !neon && vectorRegister.MatchString(body) {
				t.Fatalf("general-register target uses SIMD/FP registers:\n%s", body)
			}
			if neon {
				requireInstruction(t, body, "umin")
			}
		})
	}
}

func TestAArch64ExplicitVectorRequiresNeon(t *testing.T) {
	clang := requireAArch64Clang(t)
	generated := generateSourceC(t, `
package main
fn sum(input: simd.U8x16) -> u32 { arm64.uaddlv_u8x16(input) }
`)
	dir := t.TempDir()
	cPath := filepath.Join(dir, "vector.c")
	if err := os.WriteFile(cPath, []byte(generated), 0o600); err != nil {
		t.Fatal(err)
	}
	for _, extra := range [][]string{
		{"-mgeneral-regs-only"},
		{"-DOAK_SCALAR_SIMD=1"},
	} {
		args := append([]string{"--target=aarch64-none-elf"}, extra...)
		args = append(args, "-ffreestanding", "-std=c11", "-c", cPath, "-o", filepath.Join(dir, "vector.o"))
		output, err := exec.Command(clang, args...).CombinedOutput()
		if err == nil || !strings.Contains(string(output), "arm64 vector intrinsics require NEON") {
			t.Fatalf("expected explicit NEON target error, got %v:\n%s", err, output)
		}
	}
}
