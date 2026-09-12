package asm

import (
	"bytes"
	"strings"
	"testing"
)

// The vector extension as checker state (docs/spec/94-assembler.md §9): a
// strip-mining sum over a []u32 — the remaining count `len - idx` is the
// AVL of every vsetvli, the chunk is loaded through the guarded element
// address &v[idx], and the reduction lands in a scalar (Oak.RiscV.
// strip_access_in_bounds bounds the access, strip_progress the loop).
const rv64VStripDecl = "vstrip: (v: []u32, k: u32) -> u32"
const rv64VStripBody = `
  bind a0, a1 = v
  bind a2 = k
  clobber t0, t1, t2, t3, t4, t5, v1, v2, v3
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 0
  mv t5, a2
loop:
  bgeu t0, t1, done
  sub t2, t1, t0
  vsetvli t3, t2, e32, m1, ta, ma
  slli t4, t0, 2
  add t4, a0, t4
  vle32.v v1, (t4)
  vmv.v.x v2, t5
  vredsum.vs v3, v1, v2
  vmv.x.s t5, v3
  add t0, t0, t3
  j loop
done:
  mv a0, t5
  ret`

func TestRV64VectorChecker(t *testing.T) {
	accept := map[string][2]string{
		"strip-mined sum": {rv64VStripDecl, rv64VStripBody},
		"whole view as the AVL": {"vfirst: (v: []u32) -> u32", `
  bind a0, a1 = v
  clobber t0, t1, v1
  slli t1, a1, 32
  srli t1, t1, 32
  vsetvli t0, t1, e32, m1, ta, ma
  vle32.v v1, (a0)
  vmv.x.s a0, v1
  ret`},
		"immediate AVL within the minimum": {"vhead: (s: [*]u8) -> u32", `
  bind a0, a1 = s
  clobber t0, t1, v1, v2
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 8
  bltu t1, t0, empty
  vsetivli t0, 8, e8, m1, ta, ma
  vle8.v v1, (a0)
  vadd.vv v2, v1, v1
  vse8.v v2, (a0)
  li a0, 0
  ret
empty:
  ebreak`},
		"masks and select": {"vmask: (v: []u32, k: u32) -> u32", `
  bind a0, a1 = v
  bind a2 = k
  clobber t0, t1, v0, v1, v2, v3
  slli t1, a1, 32
  srli t1, t1, 32
  vsetvli t0, t1, e32, m1, ta, ma
  vle32.v v1, (a0)
  vmsne.vx v0, v1, a2
  vmv.v.x v2, a2
  vmerge.vvm v3, v1, v2, v0
  vmseq.vv v0, v3, v1
  vcpop.m a0, v0
  ret`},
	}
	for name, c := range accept {
		if findings := rv64Check(t, c[0], c[1]); len(findings) != 0 {
			t.Errorf("%s: %v", name, findings)
		}
	}
	rejections := map[string][3]string{
		"no configuration":            {rv64VStripDecl, strings.Replace(rv64VStripBody, "  vsetvli t3, t2, e32, m1, ta, ma\n", "  li t3, 4\n", 1), "without a vector configuration"},
		"configuration lost at label": {rv64VStripDecl, strings.Replace(rv64VStripBody, "  vle32.v v1, (t4)\n", "again:\n  vle32.v v1, (t4)\n", 1), "without a vector configuration"},
		"width against SEW":           {rv64VStripDecl, strings.Replace(rv64VStripBody, "e32, m1, ta, ma", "e8, m1, ta, ma", 1), "e8 configuration"},
		"AVL not the remaining":       {rv64VStripDecl, strings.Replace(rv64VStripBody, "  sub t2, t1, t0\n", "  mv t2, t1\n", 1), "same guarded index"},
		"index rewritten between":     {rv64VStripDecl, strings.Replace(rv64VStripBody, "  sub t2, t1, t0\n  vsetvli t3, t2, e32, m1, ta, ma\n  slli t4, t0, 2\n  add t4, a0, t4\n", "  slli t4, t0, 2\n  add t4, a0, t4\n  addi t0, t0, 1\n  bgeu t0, t1, done\n  sub t2, t1, t0\n  vsetvli t3, t2, e32, m1, ta, ma\n", 1), "neither rewritten in between"},
		"unclobbered vector register": {rv64VStripDecl, strings.Replace(rv64VStripBody, ", v1, v2, v3", ", v1, v2", 1), "not a declared clobber"},
		"unwritten vector source":     {rv64VStripDecl, strings.Replace(rv64VStripBody, "  vmv.v.x v2, t5\n", "", 1), "neither bound nor written"},
		"store to a view":             {rv64VStripDecl, strings.Replace(rv64VStripBody, "  vle32.v v1, (t4)\n", "  vle32.v v1, (t4)\n  vse32.v v1, (t4)\n", 1), "read-only view"},
		"LMUL above one":              {rv64VStripDecl, strings.Replace(rv64VStripBody, "e32, m1, ta, ma", "e32, m2, ta, ma", 1), "only LMUL=1"},
		"immediate past the minimum": {"vhead: (s: [*]u8) -> u32", `
  bind a0, a1 = s
  clobber t0, t1, v1
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 8
  bltu t1, t0, empty
  vsetivli t0, 9, e8, m1, ta, ma
  vle8.v v1, (a0)
  li a0, 0
  ret
empty:
  ebreak`, "neither the span's normalized length"},
		"vector state across a call": {"vcall: (v: []u32) -> u32", `
  bind a0, a1 = v
  clobber t0, t1, v1
  frame 16
  addi sp, sp, -16
  sd ra, 8(sp)
  slli t1, a1, 32
  srli t1, t1, 32
  vsetvli t0, t1, e32, m1, ta, ma
  call helper
  vle32.v v1, (a0)
  vmv.x.s a0, v1
  ld ra, 8(sp)
  addi sp, sp, 16
  ret`, "without a vector configuration"},
	}
	for name, c := range rejections {
		findings := rv64Check(t, c[0], c[1])
		if len(findings) == 0 {
			t.Errorf("%s: accepted", name)
			continue
		}
		if !strings.Contains(strings.Join(findings, "\n"), c[2]) {
			t.Errorf("%s: findings %v lack %q", name, findings, c[2])
		}
	}
	// The vtype is spelled in full.
	if _, errs := rv64Unit(t, rv64VStripDecl, strings.Replace(rv64VStripBody, "e32, m1, ta, ma", "e32, m1", 1)); len(errs) == 0 {
		t.Error("a vsetvli without its tail and mask policies parsed")
	}
	fn, errs := rv64Unit(t, rv64VStripDecl, rv64VStripBody)
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, _ := parseSignature(rv64VStripDecl)
	if findings := Check(fn, sig, nil); len(findings) != 0 || !fn.VectorFile {
		t.Fatalf("vector file not recorded: %v %v", findings, fn.VectorFile)
	}
}

// A vector unit is checked and trusted: the verifier's terms are integers.
func TestRV64VectorVerifyTrusts(t *testing.T) {
	v := rv64Verify(t, rv64VStripDecl, "{\n  total: u32 = k\n  i: u32 = u32(0)\n  while i < len(v) {\n    total = total + v[i]\n    i = i + u32(1)\n  }\n  total\n}", rv64VStripBody)
	if v.Kind != VerdictTrusted {
		t.Errorf("expected a trusted verdict, got %s (%s)", v.Kind, v.Message)
	}
}

// Every vector mnemonic of the subset agrees with GNU as under -march=rv64imv.
func TestRV64VectorEncoderAgreesWithGNUAs(t *testing.T) {
	requireRV64Tools(t, "riscv64-elf-as", "riscv64-elf-objcopy")
	body := `
  bind a0, a1 = v
  bind a2 = k
  clobber t0, t1, t2, v0, v1, v2, v3, v4
  slli t1, a1, 32
  srli t1, t1, 32
  vsetvli t0, t1, e32, m1, ta, ma
  vsetvli t2, t1, e8, m1, tu, mu
  vsetvli zero, t1, e64, m2, ta, mu
  vsetivli t0, 4, e16, m1, ta, ma
  vsetvli t0, t1, e32, m1, ta, ma
  vle32.v v1, (a0)
  vse32.v v1, (a0)
  vadd.vv v2, v1, v1
  vsub.vv v3, v2, v1
  vand.vv v4, v3, v2
  vor.vv v2, v4, v3
  vxor.vv v3, v2, v4
  vminu.vv v4, v3, v2
  vmaxu.vv v2, v4, v3
  vmv.v.x v3, a2
  vredsum.vs v4, v2, v3
  vmv.x.s t2, v4
  vmseq.vv v0, v1, v2
  vmerge.vvm v4, v1, v2, v0
  vcpop.m t0, v0
  vmsne.vx v0, v1, a2
  vsetvli t0, t1, e8, m1, ta, ma
  vle8.v v1, (a0)
  vse8.v v1, (a0)
  mv a0, t2
  ret`
	fn, errs := rv64Unit(t, "venc: (v: [*]u32, k: u32) -> u32", body)
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	// The mixed-width accesses and the m2 spelling are for the encoder;
	// the checker is not consulted here.
	ours, _, err := EncodeFunction(fn)
	if err != nil {
		t.Fatal(err)
	}
	theirs := gnuAssembleWith(t, rv64GNUText(fn), "rv64imv", "lp64")
	if !bytes.Equal(ours, theirs) {
		offset := 0
		for offset < len(ours) && offset < len(theirs) && bytes.Equal(ours[offset:offset+4], theirs[offset:offset+4]) {
			offset += 4
		}
		t.Fatalf("encodings differ at byte %d: ours %x, GNU as %x", offset, ours[offset:min(offset+4, len(ours))], theirs[offset:min(offset+4, len(theirs))])
	}
}
