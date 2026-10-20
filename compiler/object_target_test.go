package compiler

import (
	"bytes"
	"debug/elf"
	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
	"testing"
)

func TestEmptyAsmObjectTarget(t *testing.T) {
	for _, tc := range []struct {
		arch    string
		machine elf.Machine
	}{{target.ArchArm64, elf.EM_AARCH64}, {target.ArchRiscv64, elf.EM_RISCV}} {
		c := New().WithSource("empty.oak", "").WithTarget(target.Target{OS: target.OSLinux, Arch: tc.arch})
		raw, err := c.EmitAsmObject(asm.ELF).Get()
		if err != nil {
			t.Fatal(err)
		}
		f, err := elf.NewFile(bytes.NewReader(raw))
		if err != nil {
			t.Fatal(err)
		}
		if f.Machine != tc.machine {
			t.Fatalf("%s: got %v want %v", tc.arch, f.Machine, tc.machine)
		}
		f.Close()
	}
	c := New().WithSource("empty.oak", "").WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchAmd64})
	if raw, err := c.EmitAsmObject(asm.ELF).Get(); err == nil || raw != nil {
		t.Fatal("target without native lane emitted an object")
	}
}
