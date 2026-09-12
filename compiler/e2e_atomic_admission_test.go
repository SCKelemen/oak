package compiler

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// Lock-free admission (docs/spec/65-machine-memory.md §6): the generated C
// asserts, per atomic carrier the program declares, that the target's C11
// atomics of that width are always lock-free. A carrier the program never
// declares is not asserted, so a u32-only program still builds on a core
// without 64-bit exclusives.
const admissionProgram = `
hits: Atomic[u32]
table: [16]u32

record(i: u32): u32 {
  table[i] = table[i] + u32(1)
  atomic_fetch_add_relaxed(hits, u32(1))
}

main: (): i32 {
  _ = record(u32(3))
  i32_bits_u32(record(u32(5)) - u32(1))
}
`

func TestE2EAtomicAdmissionAssertsDeclaredCarriers(t *testing.T) {
	output, err := New().WithSource("admission.oak", admissionProgram).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, "#if !defined(OAK_ATOMIC_ACCEPT_LOCKED)") {
		t.Fatalf("admission block missing:\n%s", output)
	}
	if !strings.Contains(output, "typedef char oak_atomic_lock_free_u32[") {
		t.Fatalf("u32 carrier not asserted:\n%s", output)
	}
	for _, other := range []string{"u8", "u16", "u64", "i8", "i16", "i32", "i64"} {
		if strings.Contains(output, "oak_atomic_lock_free_"+other+"[") {
			t.Fatalf("undeclared carrier %s asserted:\n%s", other, output)
		}
	}
	// The host is always lock-free at these widths: the program builds and
	// runs, and the assertion is inert.
	code, abnormal := buildAndRun(t, "admission", admissionProgram)
	if abnormal || code != 0 {
		t.Fatalf("exit = (%d, abnormal=%v), want 0", code, abnormal)
	}
}

func TestE2EAtomicAdmissionAbsentWithoutAtomics(t *testing.T) {
	output, err := New().WithSource("plain.oak", `
main: (): i32 {
  x: u32 = u32(40)
  i32_bits_u32(x + u32(2)) - i32(42)
}
`).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if strings.Contains(output, "oak_atomic_lock_free_") || strings.Contains(output, "OAK_ATOMIC_ACCEPT_LOCKED") {
		t.Fatalf("admission block emitted for a program without atomics:\n%s", output)
	}
}

// Record fields and array elements declare storage too: a u64 field is a
// u64 carrier even when every named cell is u32.
func TestE2EAtomicAdmissionSeesFieldCarriers(t *testing.T) {
	output, err := New().WithSource("fields.oak", `
Node: type = struct {
  value: u8
  next: Atomic[u64]
}

nodes: [4]Node
head: Atomic[u32]

main: (): i32 {
  atomic_store_relaxed(nodes[u32(1)].next, u64(7))
  atomic_store_relaxed(head, u32(1))
  i32_bits_u32(u32_trunc_u64(atomic_load_relaxed(nodes[u32(1)].next)) - u32(7))
}
`).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, carrier := range []string{"u32", "u64"} {
		if !strings.Contains(output, "oak_atomic_lock_free_"+carrier+"[") {
			t.Fatalf("%s carrier not asserted:\n%s", carrier, output)
		}
	}
}

// crossCompile runs clang for the given bare-metal target over the C text
// and reports whether it compiled. It skips the test when no clang on PATH
// can target that triple at all (checked with an empty translation unit).
func crossCompile(t *testing.T, target, cpu, code string, extra ...string) (ok bool, stderr string) {
	t.Helper()
	clang, err := exec.LookPath("clang")
	if err != nil {
		t.Skip("no clang on PATH")
	}
	dir := t.TempDir()
	probe := filepath.Join(dir, "probe.c")
	if err := os.WriteFile(probe, []byte("int oak_probe;\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	base := []string{"--target=" + target, "-mcpu=" + cpu, "-mthumb", "-ffreestanding", "-DOAK_FREESTANDING", "-std=c99", "-Os", "-c"}
	if out, err := exec.Command(clang, append(append([]string{}, base...), probe, "-o", filepath.Join(dir, "probe.o"))...).CombinedOutput(); err != nil {
		t.Skipf("clang cannot target %s: %v\n%s", target, err, out)
	}
	src := filepath.Join(dir, "program.c")
	if err := os.WriteFile(src, []byte(code), 0o600); err != nil {
		t.Fatal(err)
	}
	args := append(append([]string{}, base...), extra...)
	args = append(args, src, "-o", filepath.Join(dir, "program.o"))
	out, err := exec.Command(clang, args...).CombinedOutput()
	return err == nil, string(out)
}

// On Cortex-M0+ (Armv6-M, no exclusive load/store) a u32 fetch-add is a
// libatomic call; the admission block turns that silent fallback into a
// build failure, which OAK_ATOMIC_ACCEPT_LOCKED lifts knowingly. On
// Cortex-M4 (Armv7E-M, LDREX/STREX) the same C builds untouched.
func TestE2EAtomicAdmissionRejectsLockedTarget(t *testing.T) {
	code, err := New().WithSource("admission.oak", admissionProgram).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if ok, out := crossCompile(t, "thumbv7em-none-eabi", "cortex-m4", code); !ok {
		t.Fatalf("cortex-m4 build failed:\n%s", out)
	}
	if ok, out := crossCompile(t, "thumbv6m-none-eabi", "cortex-m0plus", code); ok {
		t.Fatal("cortex-m0plus build succeeded; the u32 admission assertion should have failed it")
	} else if !strings.Contains(out, "oak_atomic_lock_free_u32") {
		t.Fatalf("cortex-m0plus build failed for another reason:\n%s", out)
	}
	if ok, out := crossCompile(t, "thumbv6m-none-eabi", "cortex-m0plus", code, "-DOAK_ATOMIC_ACCEPT_LOCKED"); !ok {
		t.Fatalf("cortex-m0plus build with OAK_ATOMIC_ACCEPT_LOCKED failed:\n%s", out)
	}
}

// The strict profile's zero-warning posture extends to the C build: the
// admission block has no OAK_ATOMIC_ACCEPT_LOCKED opt-out
// (docs/spec/85-discipline.md §7), so a locked fallback is refused outright.
func TestE2EAtomicAdmissionStrictHasNoOptOut(t *testing.T) {
	strict, err := New().WithProfile("strict").WithSource("admission.oak", admissionProgram).EmitC().Get()
	if err != nil {
		t.Fatalf("strict compilation failed: %v", err)
	}
	if strings.Contains(strict, "OAK_ATOMIC_ACCEPT_LOCKED") {
		t.Fatalf("strict build kept the opt-out:\n%s", strict)
	}
	if !strings.Contains(strict, "typedef char oak_atomic_lock_free_u32[") {
		t.Fatalf("strict build lost the assertion:\n%s", strict)
	}
	if ok, out := crossCompile(t, "thumbv6m-none-eabi", "cortex-m0plus", strict, "-DOAK_ATOMIC_ACCEPT_LOCKED"); ok {
		t.Fatal("strict cortex-m0plus build accepted the locked fallback despite the define")
	} else if !strings.Contains(out, "oak_atomic_lock_free_u32") {
		t.Fatalf("strict cortex-m0plus build failed for another reason:\n%s", out)
	}
}
