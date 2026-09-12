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
	d, err := Resolve(rv, lookupOf("mycc", "zig", "cc"), envOf(map[string]string{"OAK_CC": "mycc", "OAK_CFLAGS": "-march=rv64gc -mabi=lp64d"}))
	if err != nil || d.Kind != "explicit" || d.Path != "/tools/mycc" || strings.Join(d.Args, " ") != "-march=rv64gc -mabi=lp64d" || !d.Static {
		t.Fatalf("explicit: %+v %v", d, err)
	}
	if _, err := Resolve(rv, lookupOf(), envOf(map[string]string{"OAK_CC": "missing"})); err == nil {
		t.Fatal("a missing OAK_CC must fail, not fall through")
	}
	// zig before clang before gnu.
	d, err = Resolve(rv, lookupOf("cc", "zig", "clang", "riscv64-linux-gnu-gcc"), none)
	if err != nil || d.Kind != "zig" || strings.Join(d.Args, " ") != "cc --target=riscv64-linux-musl" || !d.Static || d.Object {
		t.Fatalf("zig: %+v %v", d, err)
	}
	// clang for a hosted cross target needs a sysroot.
	if d, err = Resolve(rv, lookupOf("cc", "clang", "riscv64-linux-gnu-gcc"), none); err != nil || d.Kind != "gnu" || d.Path != "/tools/riscv64-linux-gnu-gcc" {
		t.Fatalf("clang without sysroot must yield to gnu: %+v %v", d, err)
	}
	d, err = Resolve(rv, lookupOf("cc", "clang"), envOf(map[string]string{"OAK_SYSROOT": "/sysroots/rv"}))
	if err != nil || d.Kind != "clang" || strings.Join(d.Args, " ") != "--target=riscv64-unknown-linux-musl --sysroot=/sysroots/rv" {
		t.Fatalf("clang with sysroot: %+v %v", d, err)
	}
	// Nothing: a definite refusal naming what to install.
	if _, err := Resolve(rv, lookupOf("cc"), none); err == nil || !strings.Contains(err.Error(), "zig") || !strings.Contains(err.Error(), "riscv64-linux-gnu-gcc") {
		t.Fatalf("refusal: %v", err)
	}
	// The host target takes cc first, never static.
	host := target.Host()
	if host.Supported() {
		d, err = Resolve(host, lookupOf("cc", "zig"), none)
		if err != nil || d.Kind != "host" || d.Static {
			t.Fatalf("host: %+v %v", d, err)
		}
	}
	// Freestanding: an object, no libc, clang needs no sysroot.
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	d, err = Resolve(bare, lookupOf("cc", "clang"), none)
	if err != nil || d.Kind != "clang" || !d.Object || d.Static || !strings.Contains(strings.Join(d.Args, " "), "-ffreestanding -nostdlib -DOAK_FREESTANDING") {
		t.Fatalf("freestanding: %+v %v", d, err)
	}
	d, err = Resolve(bare, lookupOf("riscv64-elf-gcc"), none)
	if err != nil || d.Kind != "gnu" {
		t.Fatalf("freestanding gnu: %+v %v", d, err)
	}
}
