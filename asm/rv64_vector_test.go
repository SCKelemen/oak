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

// The masked strip loop at LMUL=2 (docs/spec/94-assembler.md §9): the sum
// of the elements that differ from k. Groups are even registers (v2, v4,
// v6, v8 with their partners), v0 the mask; `mu` keeps the masked-off
// lanes of the accumulator at zero so the reduction sums only the matches.
const rv64VMaskedDecl = "vmasked: (v: []u32, k: u32) -> u32"
const rv64VMaskedBody = `
  bind a0, a1 = v
  bind a2 = k
  clobber t0, t1, t2, t3, t4, t5, v0, v2, v3, v4, v5, v6, v7, v8, v9
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 0
  li t5, 0
loop:
  bgeu t0, t1, done
  sub t2, t1, t0
  vsetvli t3, t2, e32, m2, ta, mu
  slli t4, t0, 2
  add t4, a0, t4
  vle32.v v2, (t4)
  vmsne.vx v0, v2, a2
  vmv.v.x v4, zero
  vadd.vv v4, v4, v2, v0.t
  vmv.v.x v8, t5
  vredsum.vs v6, v4, v8
  vmv.x.s t5, v6
  add t0, t0, t3
  j loop
done:
  mv a0, t5
  ret`

// Widening (docs/spec/94-assembler.md §9): the u32 elements are multiplied
// by three into u64 products — a 2*LMUL destination group — and reduced at
// the wide width after a reconfiguration to e64/m2; the low 32 bits of the
// sum are returned.
const rv64VWideDecl = "vwide: (v: []u32, k: u32) -> u32"
const rv64VWideBody = `
  bind a0, a1 = v
  bind a2 = k
  clobber t0, t1, t2, t3, t4, t5, t6, v2, v4, v5, v6, v8, v9, v10, v11
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 0
  li t5, 0
  li t6, 3
loop:
  bgeu t0, t1, done
  sub t2, t1, t0
  vsetvli t3, t2, e32, m1, ta, ma
  slli t4, t0, 2
  add t4, a0, t4
  vle32.v v2, (t4)
  vmv.v.x v6, t6
  vwmulu.vv v4, v2, v6
  vsetvli t3, t2, e64, m2, ta, ma
  vmv.v.x v10, t5
  vredsum.vs v8, v4, v10
  vmv.x.s t5, v8
  vsetvli t3, t2, e32, m1, ta, ma
  add t0, t0, t3
  j loop
done:
  mv a0, t5
  ret`

// The strip-mined sum at a fractional LMUL (docs/spec/94-assembler.md §9,
// fourth increment): the u32 elements load at e32/mf2 — half a register
// per strip — and widen to e64/m1 for the reduction, so the widening
// destination is the one-register group the fraction's double makes
// (Oak.RiscV.wide_group_fractional).
const rv64VFracDecl = "vfrac: (v: []u32, k: u32) -> u32"
const rv64VFracBody = `
  bind a0, a1 = v
  bind a2 = k
  clobber t0, t1, t2, t3, t4, t5, t6, v2, v4, v6, v8, v10
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 0
  li t5, 0
  li t6, 0
loop:
  bgeu t0, t1, done
  sub t2, t1, t0
  vsetvli t3, t2, e32, mf2, ta, ma
  slli t4, t0, 2
  add t4, a0, t4
  vle32.v v2, (t4)
  vmv.v.x v6, t6
  vwaddu.vv v4, v2, v6
  vsetvli t3, t2, e64, m1, ta, ma
  vmv.v.x v10, t5
  vredsum.vs v8, v4, v10
  vmv.x.s t5, v8
  vsetvli t3, t2, e32, mf2, ta, ma
  add t0, t0, t3
  j loop
done:
  mv a0, t5
  ret`

// The floating-point strip (docs/spec/94-assembler.md §9, fifth increment):
// each u32 element converts to f32 (x), and the strip computes
// q = x * k + (x - k)^2 with one rounding for the multiply-add, then folds
// the q's in order into the running f32 sum carried in ft1 — the ordered
// reduction over the strips is the sequential sum over the whole span
// (Oak.RiscV.ordered_strips_fold). The result is the f32's bits.
const rv64VFSumDecl = "vfsum: (v: []u32, k: u32) -> u32"
const rv64VFSumBody = `
  bind a0, a1 = v
  bind a2 = k
  clobber t0, t1, t2, t3, t4, ft0, ft1, v2, v4, v6, v8, v10, v12
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 0
  fcvt.s.wu ft0, a2
  fmv.w.x ft1, zero
loop:
  bgeu t0, t1, done
  sub t2, t1, t0
  vsetvli t3, t2, e32, m1, ta, ma
  slli t4, t0, 2
  add t4, a0, t4
  vle32.v v2, (t4)
  vfcvt.f.xu.v v4, v2
  vfmv.v.f v8, ft0
  vfsub.vv v6, v4, v8
  vfmul.vv v6, v6, v6
  vfmacc.vv v6, v4, v8
  vfmv.v.f v10, ft1
  vfredosum.vs v12, v6, v10
  vfmv.f.s ft1, v12
  add t0, t0, t3
  j loop
done:
  fmv.x.w a0, ft1
  ret`

// A fixed vector at a guarded index (docs/spec/94-assembler.md §9, the
// native backend's idiom): the slack guard `li k, 4; bltu len, k; sub t,
// len, k; bltu t, idx` proves idx + 4 <= len (Oak.RiscV.slack_guard), so the
// four elements at &v[idx] are inside the span
// (Oak.RiscV.slack_access_in_bounds) and an immediate AVL of 4 loads them.
// The result is their wrapping sum, or zero when the span is too short.
const rv64VSlackDecl = "vslack: (v: []u32, k: u32) -> u32"
const rv64VSlackBody = `
  bind a0, a1 = v
  bind a2 = k
  clobber t0, t1, t2, t3, v1, v2, v3
  slli t1, a1, 32
  srli t1, t1, 32
  slli t0, a2, 32
  srli t0, t0, 32
  li t2, 4
  bltu t1, t2, none
  sub t3, t1, t2
  bltu t3, t0, none
  slli t0, t0, 2
  add t0, a0, t0
  vsetivli zero, 4, e32, m1, ta, ma
  vle32.v v1, (t0)
  vmv.v.x v2, zero
  vredsum.vs v3, v1, v2
  vmv.x.s a0, v3
  ret
none:
  li a0, 0
  ret`

// A fixed vector through the frame (a vector local's slot): an immediate
// AVL at a frame address inside the declared frame
// (Oak.RiscV.frame_vector_in_bounds).
const rv64VFrameDecl = "vframe: (v: []u32) -> u32"
const rv64VFrameBody = `
  bind a0, a1 = v
  clobber t0, t1, t2, v1, v2
  frame 16
  addi sp, sp, -16
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 4
  bltu t1, t0, none
  vsetivli zero, 4, e32, m1, ta, ma
  vle32.v v1, (a0)
  addi t2, sp, 0
  vse32.v v1, (t2)
  vle32.v v2, (t2)
  vmv.x.s a0, v2
  addi sp, sp, 16
  ret
none:
  li a0, 0
  addi sp, sp, 16
  ret`

// The float vectors' fixed-lane forms (docs/spec/93-simd.md §1.2a, the
// native lowering's sequences, nativegen/rv64_simd.go): four u32 elements
// at the span base converted to f32, divided by k, negated then made
// absolute, rooted, the catalog's NaN-propagating minimum against 1.0
// rebuilt from vfmin/vmfne/vmerge, 2.0 inserted at lane 1 through
// vid/vmseq.vx/vfmerge, and the pairwise tree (l0 + l1) + (l2 + l3)
// through two slide-and-add steps (Oak.Simd.rvv_reduce4). The result is
// the f32's bits, or zero when the span is shorter than four.
const rv64VFPairDecl = "vfpair: (v: []u32, k: u32) -> u32"
const rv64VFPairBody = `
  bind a0, a1 = v
  bind a2 = k
  clobber t0, t1, t2, ft0, ft1, v0, v1, v8, v9, v10
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 4
  bltu t1, t0, short
  vsetivli zero, 4, e32, m1, ta, ma
  vle32.v v8, (a0)
  vfcvt.f.xu.v v8, v8
  fcvt.s.wu ft0, a2
  vfmv.v.f v9, ft0
  vfdiv.vv v8, v8, v9
  vfsgnjn.vv v8, v8, v8
  vfsgnjx.vv v8, v8, v8
  vfsqrt.v v8, v8
  li t2, 1065353216
  fmv.w.x ft1, t2
  vfmv.v.f v10, ft1
  vfmin.vv v1, v8, v10
  vmfne.vv v0, v8, v8
  vmerge.vvm v1, v1, v8, v0
  vmfne.vv v0, v10, v10
  vmerge.vvm v8, v1, v10, v0
  vid.v v1
  li t2, 1
  vmseq.vx v0, v1, t2
  li t2, 1073741824
  fmv.w.x ft1, t2
  vfmerge.vfm v8, v8, ft1, v0
  vslidedown.vi v1, v8, 1
  vfadd.vv v8, v8, v1
  vslidedown.vi v1, v8, 2
  vfadd.vv v8, v8, v1
  vfmv.f.s ft0, v8
  fmv.x.w a0, ft0
  ret
short:
  li a0, 0
  ret`

func TestRV64VectorChecker(t *testing.T) {
	accept := map[string][2]string{
		"strip-mined sum":      {rv64VStripDecl, rv64VStripBody},
		"slack guard":          {rv64VSlackDecl, rv64VSlackBody},
		"frame vector":         {rv64VFrameDecl, rv64VFrameBody},
		"slack guard by addi":  {rv64VSlackDecl, strings.Replace(rv64VSlackBody, "  sub t3, t1, t2\n", "  addi t3, t1, -4\n", 1)},
		"fractional LMUL":      {rv64VFracDecl, rv64VFracBody},
		"floating-point strip": {rv64VFSumDecl, rv64VFSumBody},
		"float lane forms":     {rv64VFPairDecl, rv64VFPairBody},
		"64-bit elements at m2": {"v64: (v: []u64) -> u64", `
  bind a0, a1 = v
  clobber t0, t1, v2, v3
  slli t1, a1, 32
  srli t1, t1, 32
  vsetvli t0, t1, e64, m2, ta, ma
  vle64.v v2, (a0)
  vmv.x.s a0, v2
  ret`},
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
		"masked sum at LMUL=2": {rv64VMaskedDecl, rv64VMaskedBody},
		"widening products":    {rv64VWideDecl, rv64VWideBody},
		"extension and narrowing": {"vext: (v: []u32, k: u32) -> u32", `
  bind a0, a1 = v
  bind a2 = k
  clobber t0, t1, v2, v4, v5, v6
  slli t1, a1, 32
  srli t1, t1, 32
  vsetvli t0, t1, e32, m1, ta, ma
  vle32.v v2, (a0)
  vwaddu.vv v4, v2, v2
  vnsrl.wi v6, v4, 1
  vsetvli t0, t1, e64, m2, ta, ma
  vzext.vf2 v4, v2
  vsext.vf2 v4, v2
  vmv.x.s a0, v4
  ret`},
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
		"widening destination overlaps its source": {rv64VWideDecl, strings.Replace(rv64VWideBody, "  vwmulu.vv v4, v2, v6\n", "  vwmulu.vv v2, v2, v6\n", 1), "overlaps the source group"},
		"widening past 64-bit elements":            {rv64VWideDecl, strings.Replace(rv64VWideBody, "  vle32.v v2, (t4)\n  vmv.v.x v6, t6\n  vwmulu.vv v4, v2, v6\n", "  vle32.v v2, (t4)\n  vsetvli t3, t2, e64, m1, ta, ma\n  vmv.v.x v6, t6\n  vwmulu.vv v4, v2, v6\n", 1), "widening past 64-bit"},
		"wide group past the file":                 {rv64VWideDecl, strings.Replace(rv64VWideBody, "vsetvli t3, t2, e32, m1, ta, ma\n  slli t4", "vsetvli t3, t2, e32, m8, ta, ma\n  slli t4", 1), "past the file"},
		"unaligned wide group":                     {rv64VWideDecl, strings.Replace(rv64VWideBody, "  vwmulu.vv v4, v2, v6\n", "  vwmulu.vv v9, v2, v6\n", 1), "not aligned to the register group of LMUL=m2"},
		"unaligned group at LMUL=2":                {rv64VMaskedDecl, strings.Replace(rv64VMaskedBody, "  vle32.v v2, (t4)\n", "  vle32.v v3, (t4)\n", 1), "not aligned to the register group"},
		"mask register unwritten":                  {rv64VMaskedDecl, strings.Replace(rv64VMaskedBody, "  vmsne.vx v0, v2, a2\n", "", 1), "neither bound nor written"},
		"group not wholly clobbered":               {rv64VMaskedDecl, strings.Replace(rv64VMaskedBody, ", v9", "", 1), "not a declared clobber"},
		"float form at e16":                        {rv64VFSumDecl, strings.Replace(rv64VFSumBody, "  vfcvt.f.xu.v v4, v2\n", "  vsetvli t3, t2, e16, m1, ta, ma\n  vfcvt.f.xu.v v4, v2\n", 1), "need e32 or e64"},
		"multiply-add accumulator unwritten":       {rv64VFSumDecl, strings.Replace(rv64VFSumBody, "  vfmacc.vv v6, v4, v8\n", "  vfmacc.vv v12, v4, v8\n", 1), "read of v12, which is neither bound nor written"},
		"float register unclobbered":               {rv64VFSumDecl, strings.Replace(rv64VFSumBody, ", ft0, ft1", ", ft0", 1), "nor a declared clobber"},
		"slack guard without the length guard":     {rv64VSlackDecl, strings.Replace(rv64VSlackBody, "  bltu t1, t2, none\n", "", 1), "only a bound span base"},
		"AVL past the slack":                       {rv64VSlackDecl, strings.Replace(rv64VSlackBody, "vsetivli zero, 4, e32", "vsetivli zero, 8, e32", 1), "slack guard proved"},
		"slack guard over another constant":        {rv64VSlackDecl, strings.Replace(rv64VSlackBody, "  sub t3, t1, t2\n", "  li t3, 2\n  sub t3, t1, t3\n", 1), "slack guard proved"},
		"frame vector past the frame":              {rv64VFrameDecl, strings.Replace(rv64VFrameBody, "vsetivli zero, 4, e32, m1, ta, ma\n  vle32.v v1, (a0)\n  addi t2, sp, 0\n  vse32.v v1, (t2)", "vsetivli zero, 4, e32, m1, ta, ma\n  vle32.v v1, (a0)\n  addi t2, sp, 8\n  vse32.v v1, (t2)", 1), "outside the declared frame"},
		"frame vector with a register AVL":         {rv64VFrameDecl, strings.Replace(rv64VFrameBody, "  addi t2, sp, 0\n  vse32.v v1, (t2)", "  addi t2, sp, 0\n  vsetvli t0, t0, e32, m1, ta, ma\n  vse32.v v1, (t2)", 1), "needs an immediate AVL"},
		"gather over its own source":               {rv64VSlackDecl, strings.Replace(rv64VSlackBody, "  vmv.v.x v2, zero\n", "  vmv.v.x v2, zero\n  vrgather.vv v1, v1, v2\n", 1), "overlaps the source group"},
		"slide up over its own source":             {rv64VSlackDecl, strings.Replace(rv64VSlackBody, "  vmv.v.x v2, zero\n", "  vmv.v.x v2, zero\n  vslideup.vi v2, v2, 1\n", 1), "overlaps the source group"},
		"e64 at a fractional LMUL":                 {rv64VFracDecl, strings.Replace(rv64VFracBody, "e32, mf2, ta, ma", "e64, mf2, ta, ma", 1), "past ELEN=64"},
		"extension below mf8":                      {rv64VFracDecl, strings.Replace(rv64VFracBody, "  vsetvli t3, t2, e32, mf2, ta, ma\n  slli t4", "  vsetvli t3, t2, e8, mf8, ta, ma\n  vzext.vf2 v6, v2\n  slli t4", 1), "narrower than 8 bits"},
		"no configuration":                         {rv64VStripDecl, strings.Replace(rv64VStripBody, "  vsetvli t3, t2, e32, m1, ta, ma\n", "  li t3, 4\n", 1), "without a vector configuration"},
		"configuration lost at label":              {rv64VStripDecl, strings.Replace(rv64VStripBody, "  vle32.v v1, (t4)\n", "again:\n  vle32.v v1, (t4)\n", 1), "without a vector configuration"},
		"width against SEW":                        {rv64VStripDecl, strings.Replace(rv64VStripBody, "e32, m1, ta, ma", "e8, m1, ta, ma", 1), "e8 configuration"},
		"AVL not the remaining":                    {rv64VStripDecl, strings.Replace(rv64VStripBody, "  sub t2, t1, t0\n", "  mv t2, t1\n", 1), "same guarded index"},
		"index rewritten between":                  {rv64VStripDecl, strings.Replace(rv64VStripBody, "  sub t2, t1, t0\n  vsetvli t3, t2, e32, m1, ta, ma\n  slli t4, t0, 2\n  add t4, a0, t4\n", "  slli t4, t0, 2\n  add t4, a0, t4\n  addi t0, t0, 1\n  bgeu t0, t1, done\n  sub t2, t1, t0\n  vsetvli t3, t2, e32, m1, ta, ma\n", 1), "neither rewritten in between"},
		"unclobbered vector register":              {rv64VStripDecl, strings.Replace(rv64VStripBody, ", v1, v2, v3", ", v1, v2", 1), "not a declared clobber"},
		"unwritten vector source":                  {rv64VStripDecl, strings.Replace(rv64VStripBody, "  vmv.v.x v2, t5\n", "", 1), "neither bound nor written"},
		"store to a view":                          {rv64VStripDecl, strings.Replace(rv64VStripBody, "  vle32.v v1, (t4)\n", "  vle32.v v1, (t4)\n  vse32.v v1, (t4)\n", 1), "read-only view"},
		"LMUL above one":                           {rv64VStripDecl, strings.Replace(rv64VStripBody, "e32, m1, ta, ma", "e32, m2, ta, ma", 1), "not aligned to the register group"},
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
	// The vtype is spelled in full, and only maskable forms take v0.t.
	if _, errs := rv64Unit(t, rv64VStripDecl, strings.Replace(rv64VStripBody, "e32, m1, ta, ma", "e32, m1", 1)); len(errs) == 0 {
		t.Error("a vsetvli without its tail and mask policies parsed")
	}
	if _, errs := rv64Unit(t, rv64VMaskedDecl, strings.Replace(rv64VMaskedBody, "  vmv.v.x v4, zero\n", "  vmv.v.x v4, zero, v0.t\n", 1)); len(errs) == 0 {
		t.Error("a mask on vmv.v.x parsed")
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

// The floating-point forms at the parser: the unordered reduction is
// outside the table (float addition is not associative, and only the form
// whose result is the sequential sum is admitted,
// Oak.RiscV.ordered_strips_fold), and the F operand of a move is an F
// register.
func TestRV64VectorFloatParse(t *testing.T) {
	refused := map[string][2]string{
		"unordered reduction":   {strings.Replace(rv64VFSumBody, "vfredosum.vs", "vfredusum.vs", 1), `unknown instruction "vfredusum.vs"`},
		"integer register as F": {strings.Replace(rv64VFSumBody, "  vfmv.v.f v8, ft0\n", "  vfmv.v.f v8, t3\n", 1), "vfmv.v.f: operand 2 must be a floating-point register"},
		"vector register as F":  {strings.Replace(rv64VFSumBody, "  vfmv.f.s ft1, v12\n", "  vfmv.f.s v2, v12\n", 1), "vfmv.f.s: operand 1 must be a floating-point register"},
	}
	refused["float merge mask"] = [2]string{strings.Replace(rv64VFPairBody, "  vfmerge.vfm v8, v8, ft1, v0\n", "  vfmerge.vfm v8, v8, ft1, v1\n", 1), "vfmerge.vfm takes its mask from v0"}
	for name, tc := range refused {
		_, errs := rv64Unit(t, rv64VFSumDecl, tc[0])
		if len(errs) == 0 || !strings.Contains(errs[0].Error(), tc[1]) {
			t.Errorf("%s: %v lacks %q", name, errs, tc[1])
		}
	}
}

// Every vector mnemonic of the subset agrees with GNU as under -march=rv64imafdv.
func TestRV64VectorEncoderAgreesWithGNUAs(t *testing.T) {
	requireRV64Tools(t, "riscv64-elf-as", "riscv64-elf-objcopy")
	body := `
  bind a0, a1 = v
  bind a2 = k
  clobber t0, t1, t2, ft0, ft1, v0, v1, v2, v3, v4
  slli t1, a1, 32
  srli t1, t1, 32
  vsetvli t0, t1, e32, m1, ta, ma
  vsetvli t2, t1, e8, m1, tu, mu
  vsetvli zero, t1, e64, m2, ta, mu
  vsetvli t0, t1, e32, mf2, ta, ma
  vsetvli t2, t1, e16, mf4, tu, mu
  vsetvli zero, t1, e8, mf8, ta, ma
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
  vsetvli t0, t1, e16, m1, ta, ma
  vle16.v v1, (a0)
  vse16.v v1, (a0)
  vsetvli t0, t1, e32, m1, ta, ma
  vwaddu.vv v4, v2, v3
  vwadd.vv v4, v2, v3
  vwsubu.vv v4, v2, v3, v0.t
  vwsub.vv v4, v2, v3
  vwmulu.vv v4, v2, v3
  vwmul.vv v4, v2, v3, v0.t
  vzext.vf2 v4, v2
  vsext.vf2 v4, v2, v0.t
  vnsrl.wi v2, v4, 3
  vnsrl.wi v2, v4, 31, v0.t
  vsetvli t0, t1, e32, m2, ta, mu
  vle32.v v2, (a0), v0.t
  vse32.v v2, (a0), v0.t
  vadd.vv v4, v2, v2, v0.t
  vminu.vv v6, v4, v2, v0.t
  vredsum.vs v8, v4, v6, v0.t
  vmseq.vv v0, v2, v4, v0.t
  vmsne.vx v0, v2, a2, v0.t
  vcpop.m t0, v0, v0.t
  vsetvli t0, t1, e32, m4, ta, ma
  vle32.v v4, (a0)
  vsetvli t0, t1, e32, m8, tu, mu
  vle32.v v8, (a0)
  vsetvli t0, t1, e64, m1, ta, ma
  vle64.v v1, (a0)
  vse64.v v1, (a0)
  vle64.v v1, (a0), v0.t
  vse64.v v1, (a0), v0.t
  vsetvli t0, t1, e32, m1, ta, ma
  vfadd.vv v2, v1, v1
  vfadd.vv v2, v1, v1, v0.t
  vfsub.vv v3, v2, v1
  vfsub.vv v3, v2, v1, v0.t
  vfmul.vv v4, v3, v2
  vfmul.vv v4, v3, v2, v0.t
  vfmacc.vv v4, v2, v3
  vfmacc.vv v4, v2, v3, v0.t
  vfmv.v.f v3, ft0
  vfmv.f.s ft1, v4
  vfredosum.vs v4, v2, v3
  vfredosum.vs v4, v2, v3, v0.t
  vfcvt.f.xu.v v2, v1
  vfcvt.f.xu.v v2, v1, v0.t
  vfdiv.vv v4, v3, v2
  vfdiv.vv v4, v3, v2, v0.t
  vfsqrt.v v2, v1
  vfsqrt.v v2, v1, v0.t
  vfmin.vv v4, v3, v2
  vfmin.vv v4, v3, v2, v0.t
  vfmax.vv v4, v3, v2
  vfmax.vv v4, v3, v2, v0.t
  vfsgnjn.vv v2, v1, v1
  vfsgnjn.vv v2, v1, v1, v0.t
  vfsgnjx.vv v2, v1, v1
  vfsgnjx.vv v2, v1, v1, v0.t
  vmfne.vv v0, v1, v2
  vmfne.vv v0, v1, v2, v0.t
  vid.v v3
  vid.v v3, v0.t
  vmseq.vx v0, v1, a2
  vmseq.vx v0, v1, a2, v0.t
  vfmerge.vfm v4, v3, ft0, v0
  vssubu.vv v2, v1, v1
  vssubu.vv v2, v1, v1, v0.t
  vsrl.vx v2, v1, a2
  vsrl.vx v2, v1, a2, v0.t
  vmslt.vx v0, v1, a2
  vmsltu.vx v0, v1, a2, v0.t
  vrgather.vv v4, v1, v2
  vrgather.vv v4, v1, v2, v0.t
  vslideup.vi v4, v1, 3
  vslideup.vi v4, v1, 31, v0.t
  vslidedown.vi v4, v1, 0
  vslidedown.vi v4, v1, 13, v0.t
  vsetivli zero, 4, e32, m1, ta, ma
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
	theirs := gnuAssembleWith(t, rv64GNUText(fn), "rv64imafdv", "lp64")
	if !bytes.Equal(ours, theirs) {
		offset := 0
		for offset < len(ours) && offset < len(theirs) && bytes.Equal(ours[offset:offset+4], theirs[offset:offset+4]) {
			offset += 4
		}
		t.Fatalf("encodings differ at byte %d: ours %x, GNU as %x", offset, ours[offset:min(offset+4, len(ours))], theirs[offset:min(offset+4, len(theirs))])
	}
}
