package toolchain

import (
	"errors"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/target"
)

func lookupOf(names ...string) Lookup {
	return func(name string) (string, error) {
		for _, n := range names {
			if n == name {
				return "/tools/" + name, nil
			}
		}
		return "", errors.New("not found")
	}
}

func envOf(pairs map[string]string) func(string) string {
	return func(k string) string { return pairs[k] }
}

func TestResolveOrder(t *testing.T) {
	rv := target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}
	none := envOf(nil)
	// Explicit OAK_CC wins over everything and is taken as targeting rv.
	d, err := Resolve(rv, Options{}, lookupOf("mycc", "zig", "cc"), envOf(map[string]string{"OAK_CC": "mycc", "OAK_CFLAGS": "-march=rv64gc -mabi=lp64d"}))
	if err != nil || d.Kind != "explicit" || d.Path != "/tools/mycc" || strings.Join(d.Args, " ") != "-march=rv64gc -mabi=lp64d" || !d.Static {
		t.Fatalf("explicit: %+v %v", d, err)
	}
	if _, err := Resolve(rv, Options{}, lookupOf(), envOf(map[string]string{"OAK_CC": "missing"})); err == nil {
		t.Fatal("a missing OAK_CC must fail, not fall through")
	}
	// zig before clang before gnu.
	d, err = Resolve(rv, Options{}, lookupOf("cc", "zig", "clang", "riscv64-linux-gnu-gcc"), none)
	if err != nil || d.Kind != "zig" || strings.Join(d.Args, " ") != "cc --target=riscv64-linux-musl" || !d.Static || d.Object {
		t.Fatalf("zig: %+v %v", d, err)
	}
	// clang for a hosted cross target needs a sysroot.
	if d, err = Resolve(rv, Options{}, lookupOf("cc", "clang", "riscv64-linux-gnu-gcc"), none); err != nil || d.Kind != "gnu" || d.Path != "/tools/riscv64-linux-gnu-gcc" {
		t.Fatalf("clang without sysroot must yield to gnu: %+v %v", d, err)
	}
	d, err = Resolve(rv, Options{}, lookupOf("cc", "clang"), envOf(map[string]string{"OAK_SYSROOT": "/sysroots/rv"}))
	if err != nil || d.Kind != "clang" || strings.Join(d.Args, " ") != "--target=riscv64-unknown-linux-musl --sysroot=/sysroots/rv" {
		t.Fatalf("clang with sysroot: %+v %v", d, err)
	}
	// Nothing: a definite refusal naming what to install.
	if _, err := Resolve(rv, Options{}, lookupOf("cc"), none); err == nil || !strings.Contains(err.Error(), "zig") || !strings.Contains(err.Error(), "riscv64-linux-gnu-gcc") {
		t.Fatalf("refusal: %v", err)
	}
	// The host target takes cc first, never static.
	host := target.Host()
	if host.Supported() {
		d, err = Resolve(host, Options{}, lookupOf("cc", "zig"), none)
		if err != nil || d.Kind != "host" || d.Static {
			t.Fatalf("host: %+v %v", d, err)
		}
	}
	// Freestanding: an object, no libc, clang needs no sysroot.
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	d, err = Resolve(bare, Options{}, lookupOf("cc", "clang"), none)
	if err != nil || d.Kind != "clang" || !d.Object || d.Static || !strings.Contains(strings.Join(d.Args, " "), "-mcpu=generic_rv64 -ffreestanding -nostdlib -fno-unwind-tables -fno-asynchronous-unwind-tables -DOAK_FREESTANDING") {
		t.Fatalf("freestanding: %+v %v", d, err)
	}
	d, err = Resolve(bare, Options{}, lookupOf("riscv64-elf-gcc"), none)
	if err != nil || d.Kind != "gnu" || strings.Contains(strings.Join(d.Args, " "), "-mcpu") {
		t.Fatalf("freestanding gnu (no LLVM processor names for RISC-V gcc): %+v %v", d, err)
	}
	// Microcontrollers: the Cortex-M default, an explicit processor, the
	// environment, and the GNU spelling.
	mcu := target.Target{OS: target.OSFreestanding, Arch: target.ArchArm}
	d, err = Resolve(mcu, Options{}, lookupOf("zig"), none)
	if err != nil || strings.Join(d.Args, " ") != "cc --target=thumb-freestanding-eabi -mcpu=cortex_m4 -ffreestanding -nostdlib -fno-unwind-tables -fno-asynchronous-unwind-tables -DOAK_FREESTANDING" || !d.Object {
		t.Fatalf("cortex-m default: %+v %v", d, err)
	}
	if d, _ = Resolve(mcu, Options{CPU: "cortex_m0"}, lookupOf("zig"), none); !strings.Contains(strings.Join(d.Args, " "), "-mcpu=cortex_m0") {
		t.Fatalf("explicit cpu: %+v", d)
	}
	if d, _ = Resolve(mcu, Options{}, lookupOf("zig"), envOf(map[string]string{"OAKCPU": "cortex_m33"})); !strings.Contains(strings.Join(d.Args, " "), "-mcpu=cortex_m33") {
		t.Fatalf("OAKCPU: %+v", d)
	}
	if d, _ = Resolve(mcu, Options{CPU: "cortex_m7"}, lookupOf("arm-none-eabi-gcc"), none); d.Kind != "gnu" || !strings.Contains(strings.Join(d.Args, " "), "-mcpu=cortex-m7") {
		t.Fatalf("gnu arm spelling: %+v", d)
	}
	rv32 := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv32}
	if d, _ = Resolve(rv32, Options{}, lookupOf("zig"), none); !strings.Contains(strings.Join(d.Args, " "), "--target=riscv32-freestanding-none -mcpu=generic_rv32") {
		t.Fatalf("rv32: %+v", d)
	}
	// An explicit OAK_CC is never second-guessed with a processor flag.
	if d, _ = Resolve(mcu, Options{CPU: "cortex_m0"}, lookupOf("mycc"), envOf(map[string]string{"OAK_CC": "mycc"})); strings.Contains(strings.Join(d.Args, " "), "-mcpu") {
		t.Fatalf("explicit compiler got a cpu flag: %+v", d)
	}
}
