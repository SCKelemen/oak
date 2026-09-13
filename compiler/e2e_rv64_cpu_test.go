package compiler

import (
	"encoding/binary"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
)

// The processor decides the RV64 lane's encodings (docs/spec/94-assembler.md
// §9, 90-backend.md §2a): a unit that uses the vector extension needs a
// -cpu with V, and units compress under C unless they spell option rvc or
// norvc themselves.
const rv64VectorOak = `
vfirst: (v: []u32) -> u32

main: (): i32 {
  0
}
`

const rv64VectorUnit = `
vfirst: (v: []u32) -> u32 = {
  bind a0, a1 = v
  clobber t0, t1, v1
  slli t1, a1, 32
  srli t1, t1, 32
  vsetvli t0, t1, e32, m1, ta, ma
  vle32.v v1, (a0)
  vmv.x.s a0, v1
  ret
}
`

func TestE2ERV64VectorUnitNeedsV(t *testing.T) {
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	for _, c := range []struct {
		cpu  string
		want string
	}{{"generic_rv64+m", "-cpu ...+v"}, {"sifive_u74", "-cpu ...+v"}, {"", "-cpu ...+v"}, {"generic_rv64+m+v", ""}, {"rv64gcv", ""}} {
		comp := New().WithSource("vfirst.oak", rv64VectorOak).WithAsmUnit("vfirst.rv64.oakasm", rv64VectorUnit).WithTarget(bare).WithCPU(c.cpu)
		_, err := comp.EmitC().Get()
		switch {
		case c.want == "" && err != nil:
			t.Errorf("cpu %q: %v", c.cpu, err)
		case c.want != "" && (err == nil || !strings.Contains(err.Error(), c.want)):
			t.Errorf("cpu %q: expected a refusal naming %q, got %v", c.cpu, c.want, err)
		}
	}
	// The hosted target's default processor carries no V either.
	if _, err := New().WithSource("vfirst.oak", rv64VectorOak).WithAsmUnit("vfirst.rv64.oakasm", rv64VectorUnit).WithTarget(rv64Linux).EmitC().Get(); err == nil || !strings.Contains(err.Error(), "-cpu ...+v") {
		t.Errorf("linux/riscv64 default: %v", err)
	}
}

func rv64ObjectFlags(t *testing.T, comp Compilation) uint32 {
	t.Helper()
	native, err := comp.EmitNative(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	return binary.LittleEndian.Uint32(native.Object[48:52])
}

// Compression follows the processor: C on the -cpu compresses the native
// encoding and flags the object; the hosted default (rv64gc) compresses;
// the freestanding default (generic_rv64+m) does not; an explicit option
// in the unit wins either way.
func TestE2ERV64CompressionFollowsCPU(t *testing.T) {
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	unit := func(tgt target.Target, cpu, body string) Compilation {
		return New().WithSource("pick.oak", rv64PickOak).WithAsmUnit("pick.rv64.oakasm", body).WithTarget(tgt).WithCPU(cpu)
	}
	for _, c := range []struct {
		tgt        target.Target
		cpu, body  string
		compressed bool
	}{
		{bare, "generic_rv64+m", rv64PickUnit, false},
		{bare, "generic_rv64+m+c", rv64PickUnit, true},
		{bare, "rv64imc", rv64PickUnit, true},
		{rv64Linux, "", rv64PickUnit, true},
		{bare, "generic_rv64+m+c", strings.Replace(rv64PickUnit, "  bind a0 = x\n", "  bind a0 = x\n  option norvc\n", 1), false},
		{bare, "generic_rv64+m", strings.Replace(rv64PickUnit, "  bind a0 = x\n", "  bind a0 = x\n  option rvc\n", 1), true},
	} {
		flags := rv64ObjectFlags(t, unit(c.tgt, c.cpu, c.body))
		if (flags&0x1 != 0) != c.compressed {
			t.Errorf("%s -cpu %q: e_flags %#x, compressed %v", c.tgt, c.cpu, flags, c.compressed)
		}
	}
}
