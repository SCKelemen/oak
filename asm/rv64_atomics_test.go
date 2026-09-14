package asm

import (
	"bytes"
	"strings"
	"testing"
)

// The A extension (docs/spec/94-assembler.md §9, asm/rv64_atomics.go):
// GCC's compare-exchange loop over a span cell — lr.w.aqrl, sc.w.rl, the
// element address formed in two instructions before the loop head — is
// checked and proven under the sequential model, as are an amoadd and an
// amoswap; the wrong stored value is refuted.
const rv64CasDecl = "cas_rv: (v: [*]Atomic[u32], i: u32, expected, desired: u32) -> u32"
const rv64CasBody = `
  bind a0, a1 = v
  bind a2 = i
  bind a3 = expected
  bind a4 = desired
  clobber a5
  bgeu a2, a1, trap
  slli a5, a2, 32
  srli a2, a5, 30
  add a5, a0, a2
retry:
  lr.w.aqrl a0, 0(a5)
  bne a0, a3, done
  sc.w.rl a2, a4, 0(a5)
  bnez a2, retry
done:
  sext.w a0, a0
  ret
trap:
  ebreak`

func TestRV64AtomicsChecker(t *testing.T) {
	if findings := rv64Check(t, rv64CasDecl, rv64CasBody); len(findings) != 0 {
		t.Errorf("GCC's compare-exchange loop must be accepted: %v", findings)
	}
	amo := "  bind a0, a1 = v\n  bind a2 = i\n  bind a3 = x\n  clobber a5\n  bgeu a2, a1, trap\n  slli a5, a2, 32\n  srli a5, a5, 30\n  add a5, a0, a5\n  amoadd.w.aqrl a0, a3, 0(a5)\n  ret\ntrap:\n  ebreak"
	if findings := rv64Check(t, "bump_rv: (v: [*]Atomic[u32], i: u32, x: u32) -> u32", amo); len(findings) != 0 {
		t.Errorf("an amoadd through a guarded element must be accepted: %v", findings)
	}
	rejections := map[string][3]string{
		"unguarded":       {rv64CasDecl, strings.Replace(rv64CasBody, "  bgeu a2, a1, trap\n", "", 1), "guarded element address"},
		"read-only view":  {"cas_view: (v: []Atomic[u32], i: u32, expected, desired: u32) -> u32", rv64CasBody, "read-only"},
		"address skipped": {rv64CasDecl, strings.Replace(rv64CasBody, "  add a5, a0, a2\nretry:", "  beq a3, a4, retry\n  add a5, a0, a2\nretry:", 1), "guarded element address"},
	}
	// An offset on an atomic is refused by the parser: the form has none.
	if _, errs := rv64Unit(t, rv64CasDecl, strings.Replace(rv64CasBody, "0(a5)", "4(a5)", 2)); len(errs) == 0 || !strings.Contains(errs[0].Error(), "zero offset") {
		t.Errorf("an atomic with an offset must be refused at parse, got %v", errs)
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
}

func TestRV64AtomicsVerify(t *testing.T) {
	v := rv64Verify(t, rv64CasDecl, "atomic_compare_exchange_acq_rel_acquire(v[i], expected, desired)", rv64CasBody)
	if v.Kind != VerdictProven || !strings.Contains(v.Message, "the span memory it writes (v)") {
		t.Errorf("GCC's compare-exchange loop must be proven in its result and its span, got %s: %s", v.Kind, v.Message)
	}
	wrong := rv64Verify(t, rv64CasDecl, "atomic_compare_exchange_acq_rel_acquire(v[i], expected, desired)", strings.Replace(rv64CasBody, "  sc.w.rl a2, a4, 0(a5)", "  addi a4, a4, 1\n  sc.w.rl a2, a4, 0(a5)", 1))
	if wrong.Kind != VerdictMismatch {
		t.Errorf("a compare-exchange storing another value must be a mismatch, got %s: %s", wrong.Kind, wrong.Message)
	}
	head := "  bind a0, a1 = v\n  bind a2 = i\n  bind a3 = x\n  clobber a5\n  bgeu a2, a1, trap\n  slli a5, a2, 32\n  srli a5, a5, 30\n  add a5, a0, a5\n"
	tail := "\n  ret\ntrap:\n  ebreak"
	for name, c := range map[string][2]string{
		"fetch-add": {"atomic_fetch_add_acq_rel(v[i], x)", head + "  amoadd.w.aqrl a0, a3, 0(a5)" + tail},
		"exchange":  {"atomic_exchange_acq_rel(v[i], x)", head + "  amoswap.w.aqrl a0, a3, 0(a5)" + tail},
		"lr/sc add": {"atomic_fetch_add_relaxed(v[i], x)", head + "retry:\n  lr.w a0, 0(a5)\n  add a2, a0, a3\n  sc.w a2, a2, 0(a5)\n  bnez a2, retry\n  sext.w a0, a0" + tail},
	} {
		v := rv64Verify(t, "bump_rv: (v: [*]Atomic[u32], i: u32, x: u32) -> u32", c[0], c[1])
		if v.Kind != VerdictProven || !strings.Contains(v.Message, "the span memory it writes (v)") {
			t.Errorf("%s: must be proven in its result and its span, got %s: %s", name, v.Kind, v.Message)
		}
	}
}

// The encoder's atomics agree with GNU as, ordering bits included.
func TestRV64AtomicsEncoderAgreesWithGNUAs(t *testing.T) {
	requireRV64Tools(t, "riscv64-elf-as", "riscv64-elf-objcopy")
	fn, errs := rv64Unit(t, "atomics_rv: (v: [*]Atomic[u64], x: u64) -> u64", `
  bind a0, a1 = v
  bind a2 = x
  clobber a3, a4
  lr.w a3, 0(a0)
  lr.w.aq a3, 0(a0)
  lr.d.aqrl a3, 0(a0)
  sc.w.rl a4, a2, 0(a0)
  sc.d a4, a2, 0(a0)
  amoswap.w.aqrl a3, a2, 0(a0)
  amoadd.d.aq a3, a2, 0(a0)
  amoand.w a3, a2, 0(a0)
  amoor.d.rl a3, a2, 0(a0)
  amoxor.w.aqrl a3, a2, 0(a0)
  amomin.d a3, a2, 0(a0)
  amomaxu.w.aq a3, a2, 0(a0)
  mv a0, a3
  ret`)
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	ours, _, err := EncodeFunction(fn)
	if err != nil {
		t.Fatal(err)
	}
	theirs := gnuAssembleWith(t, rv64GNUText(fn), "rv64ima", "lp64")
	if !bytes.Equal(ours, theirs) {
		t.Fatalf("encodings differ: ours %x, GNU as %x", ours, theirs)
	}
}
