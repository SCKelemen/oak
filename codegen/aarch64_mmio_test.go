package codegen

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

const aarch64MmioSource = `
package main

fn mmio_load8(addr: u64) -> u8
  arm64.mmio_read_rw_u8(arm64.mmio_unsafe_rw_u8(addr))
fn mmio_load16(addr: u64) -> u16
  arm64.mmio_read_rw_u16(arm64.mmio_unsafe_rw_u16(addr))
fn mmio_load32(addr: u64) -> u32
  arm64.mmio_read_rw_u32(arm64.mmio_unsafe_rw_u32(addr))
fn mmio_load64(addr: u64) -> u64
  arm64.mmio_read_rw_u64(arm64.mmio_unsafe_rw_u64(addr))

fn mmio_store8(addr: u64, value: u8) -> ()
  arm64.mmio_write_rw_u8(arm64.mmio_unsafe_rw_u8(addr), value)
fn mmio_store16(addr: u64, value: u16) -> ()
  arm64.mmio_write_rw_u16(arm64.mmio_unsafe_rw_u16(addr), value)
fn mmio_store32(addr: u64, value: u32) -> ()
  arm64.mmio_write_rw_u32(arm64.mmio_unsafe_rw_u32(addr), value)
fn mmio_store64(addr: u64, value: u64) -> ()
  arm64.mmio_write_rw_u64(arm64.mmio_unsafe_rw_u64(addr), value)
`

func compileMmioAArch64Assembly(t *testing.T) (generated, assembly string) {
	t.Helper()
	clang := requireAArch64Clang(t)
	generated = generateSourceC(t, aarch64MmioSource)
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "free("} {
		if strings.Contains(generated, forbidden) {
			t.Fatalf("generated MMIO path unexpectedly references heap primitive %q:\n%s", forbidden, generated)
		}
	}
	if strings.Contains(generated, "atomic_thread_fence") {
		t.Fatalf("MMIO lowering acquired hidden C atomic fence:\n%s", generated)
	}

	dir := t.TempDir()
	cPath := filepath.Join(dir, "mmio.c")
	sPath := filepath.Join(dir, "mmio.s")
	if err := os.WriteFile(cPath, []byte(generated), 0o600); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(clang,
		"--target=aarch64-none-elf", "-march=armv8-a",
		"-std=c11", "-O2", "-ffreestanding",
		"-Wall", "-Wextra", "-Werror", "-Wno-unused-function",
		"-S", cPath, "-o", sPath,
	)
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("cross-compile generated MMIO C: %v\n%s\n--- C ---\n%s", err, output, generated)
	}
	bytes, err := os.ReadFile(sPath)
	if err != nil {
		t.Fatal(err)
	}
	return generated, strings.ToLower(string(bytes))
}

func TestAArch64MmioExactAccessWidthAndNoHiddenBarrier(t *testing.T) {
	_, assembly := compileMmioAArch64Assembly(t)
	cases := []struct {
		fn       string
		mnemonic string
	}{
		{"mmio_load8", "ldrb"},
		{"mmio_load16", "ldrh"},
		{"mmio_load32", "ldr"},
		{"mmio_load64", "ldr"},
		{"mmio_store8", "strb"},
		{"mmio_store16", "strh"},
		{"mmio_store32", "str"},
		{"mmio_store64", "str"},
	}
	for _, tc := range cases {
		t.Run(tc.fn, func(t *testing.T) {
			body := aarch64FunctionBody(t, assembly, tc.fn)
			requireInstruction(t, body, tc.mnemonic)
			for _, barrier := range []string{"dmb", "dsb", "isb"} {
				if hasInstruction(body, barrier) {
					t.Fatalf("%s acquired hidden %s barrier:\n%s", tc.fn, barrier, body)
				}
			}
		})
	}
}

func TestAArch64MmioGeneratedCFailsClosedOnHost(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("host C compiler is not available")
	}
	generated := generateSourceC(t, `
package main
fn load(addr: u64) -> u32
  arm64.mmio_read_rw_u32(arm64.mmio_unsafe_rw_u32(addr))
`)
	dir := t.TempDir()
	cPath := filepath.Join(dir, "mmio.c")
	oPath := filepath.Join(dir, "mmio.o")
	if err := os.WriteFile(cPath, []byte(generated), 0o600); err != nil {
		t.Fatal(err)
	}
	// Force the non-AArch64 branch regardless of the host architecture
	// (-DOAK_PORTABLE_INTRINSICS): MMIO must fail closed with #error rather
	// than acquire a fake portable lowering. On an actual AArch64 host the
	// unforced build correctly compiles to the real access sequence.
	cmd := exec.Command(cc, "-std=c11", "-O2", "-DOAK_PORTABLE_INTRINSICS", "-c", cPath, "-o", oPath)
	output, err := cmd.CombinedOutput()
	if err == nil {
		t.Fatal("non-AArch64 compilation of architectural MMIO unexpectedly succeeded")
	}
	if !strings.Contains(string(output), "arm64 MMIO") {
		t.Fatalf("host failure did not explain AArch64 MMIO requirement:\n%s\n--- C ---\n%s", output, generated)
	}
}
