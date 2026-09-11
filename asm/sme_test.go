package asm

import (
	"bytes"
	"fmt"
	"os/exec"
	"strconv"
	"strings"
	"testing"
)

// smeSamples spells the SVE/SME vocabulary an Oak kernel on the matrix
// unit uses (docs/spec/94-assembler.md §9): mode switches, predicates,
// the streaming-legal SVE data processing and accesses, the ZA outer
// products, tile slices, multi-vector groups, and the SME2 lookup table.
var smeSamples = []string{
	"smstart", "smstart sm", "smstart za", "smstop", "smstop sm", "smstop za",
	"zero {za}", "zero {za0.s, za1.s}", "zero {za0.d}", "zero {za2.d, za5.d}", "zero {za0.h}", "zero {za0.b}", "zero {zt0}",
	"ptrue p0.s", "ptrue p0.b, vl16", "ptrue p7.d, all", "ptrue p1.h, pow2", "ptrue pn8.s", "pfalse p0.b",
	"whilelt p0.s, x0, x1", "whilelt p1.s, w2, w3", "whilelt p0.s, wzr, w6", "whilelt pn8.s, x0, x1, vlx2", "whilelo p2.b, x3, x4", "whilele p0.d, x1, x2",
	"cntw x0", "cntw x0, all, mul #4", "cntb x9", "cntd x1, vl16", "incw x0", "incw x0, all, mul #2", "decd x3", "cntp x0, p0, p1.s", "cntp x0, pn8.s, vlx2",
	"rdvl x0, #1", "rdsvl x0, #1", "rdsvl x9, #-3", "addvl x0, x0, #1", "addvl sp, sp, #-2", "addpl x1, x2, #3", "addsvl x0, x0, #1", "addspl x0, x1, #2",
	"ld1w {z0.s}, p0/z, [x0]", "ld1w {z0.s}, p0/z, [x0, #1, mul vl]", "ld1w {z3.s}, p2/z, [sp, #-8, mul vl]", "ld1w {z0.s}, p0/z, [x0, x1, lsl #2]",
	"ld1d {z0.d}, p0/z, [x0, x1, lsl #3]", "ld1b {z0.b}, p0/z, [x0, x1]", "ld1h {z5.h}, p3/z, [x2, x9, lsl #1]", "ld1w {z0.d}, p0/z, [x0]",
	"st1w {z0.s}, p0, [x0]", "st1w {z0.s}, p0, [x0, #1, mul vl]", "st1d {z0.d}, p0, [x0, x1, lsl #3]", "st1b {z7.b}, p1, [x4, x5]",
	"ld1rw {z0.s}, p0/z, [x0]", "ld1rw {z0.s}, p0/z, [x0, #8]", "ld1rqw {z0.s}, p0/z, [x0]", "ld1rqd {z1.d}, p2/z, [x3, x4, lsl #3]",
	"ld2w {z0.s, z1.s}, p0/z, [x0]", "ld2w {z30.s, z31.s}, p3/z, [x1, #2, mul vl]", "ld3d {z4.d - z6.d}, p1/z, [x2, x3, lsl #3]", "ld4b {z0.b - z3.b}, p0/z, [x0, x1]",
	"st2w {z0.s, z1.s}, p0, [x0]", "st3h {z1.h - z3.h}, p2, [x4, #-3, mul vl]", "st4b {z0.b - z3.b}, p0, [x0, x1]",
	"ldr z0, [x0]", "ldr z1, [x0, #2, mul vl]", "str z0, [sp, #-1, mul vl]", "ldr p0, [x0]", "str p5, [x1, #3, mul vl]",
	"ld1w {za0h.s[w12, 0]}, p0/z, [x0, x1, lsl #2]", "ld1w {za0v.s[w12, 3]}, p0/z, [x0]", "ld1w {za3h.s[w15, 2]}, p7/z, [sp, x2, lsl #2]",
	"st1w {za1h.s[w13, 1]}, p0, [x0, x1, lsl #2]", "st1w {za0h.s[w12, 0]}, p0, [x4]", "ld1d {za5v.d[w14, 1]}, p1/z, [x0, x3, lsl #3]",
	"st1b {za0h.b[w12, 15]}, p0, [x0]", "ld1h {za1v.h[w13, 7]}, p2/z, [x1, x2, lsl #1]",
	"ldr za[w12, 0], [x0]", "ldr za[w13, 5], [x1, #5, mul vl]", "str za[w12, 0], [x0]", "str za[w15, 15], [sp, #15, mul vl]",
	"ldr zt0, [x0]", "str zt0, [x3]",
	"fmopa za0.s, p0/m, p1/m, z0.s, z1.s", "fmopa za3.s, p7/m, p6/m, z31.s, z30.s", "fmopa za0.d, p0/m, p1/m, z0.d, z1.d", "fmopa za7.d, p2/m, p3/m, z4.d, z5.d",
	"fmops za1.s, p0/m, p1/m, z2.s, z3.s", "fmops za0.d, p0/m, p0/m, z0.d, z0.d", "fmopa za0.s, p0/m, p1/m, z0.h, z1.h", "bfmopa za0.s, p0/m, p1/m, z0.h, z1.h",
	"smopa za0.s, p0/m, p1/m, z0.b, z1.b", "umopa za0.d, p0/m, p1/m, z0.h, z1.h", "sumopa za1.s, p2/m, p3/m, z4.b, z5.b", "usmops za0.s, p0/m, p1/m, z0.b, z1.b",
	"addha za0.s, p0/m, p1/m, z0.s", "addva za3.s, p0/m, p1/m, z0.s", "addha za0.d, p0/m, p1/m, z0.d",
	"mova z0.s, p0/m, za0h.s[w12, 0]", "mova z0.b, p0/m, za0h.b[w12, 0]", "mova z5.d, p3/m, za7v.d[w15, 1]", "mova z1.h, p0/m, za1v.h[w13, 6]", "mova z2.q, p0/m, za15v.q[w12, 0]",
	"mova za0v.s[w12, 0], p0/m, z0.s", "mova za2h.s[w14, 3], p1/m, z9.s", "mova za0h.b[w12, 5], p0/m, z0.b",
	"mova {z0.s - z3.s}, za0h.s[w12, 0:3]", "mova {z4.s, z5.s}, za1v.s[w13, 2:3]", "mova {z0.d, z1.d}, za.d[w8, 0, vgx2]", "mova {z0.d - z3.d}, za.d[w9, 7, vgx4]",
	"mova za0h.s[w12, 0:1], {z0.s, z1.s}", "mova za.d[w8, 0, vgx2], {z0.d, z1.d}", "mova za.d[w11, 3, vgx4], {z4.d - z7.d}",
	"fmla za.s[w8, 0, vgx4], {z0.s - z3.s}, z4.s", "fmla za.s[w8, 0, vgx2], {z0.s, z1.s}, {z2.s, z3.s}", "fmla za.s[w8, 7, vgx4], {z0.s - z3.s}, z4.s[1]",
	"fmla za.d[w11, 3, vgx2], {z2.d, z3.d}, z9.d", "fmls za.s[w9, 1, vgx4], {z4.s - z7.s}, {z8.s - z11.s}", "fmla za.s[w8, 0], {z0.s - z3.s}, z4.s",
	"fadd za.s[w8, 0, vgx4], {z0.s - z3.s}", "fsub za.d[w10, 2, vgx2], {z6.d, z7.d}", "add za.s[w8, 0, vgx4], {z0.s - z3.s}",
	"sdot za.s[w8, 0, vgx4], {z0.b - z3.b}, z4.b", "udot za.s[w8, 0, vgx2], {z0.b, z1.b}, {z2.b, z3.b}",
	"ld1w {z0.s - z3.s}, pn8/z, [x0]", "ld1w {z0.s, z1.s}, pn8/z, [x0, x1, lsl #2]", "ld1w {z0.s, z1.s}, pn8/z, [x0, #2, mul vl]", "ld1w {z4.s - z7.s}, pn15/z, [x2, #-8, mul vl]",
	"st1w {z0.s - z3.s}, pn8, [x0]", "st1d {z8.d, z9.d}, pn9, [x1, x2, lsl #3]", "ld1b {z0.b - z3.b}, pn10/z, [sp]",
	"ld1w {z0.s, z8.s}, pn8/z, [x0]", "ld1w {z16.s, z24.s}, pn9/z, [x1, #2, mul vl]", "ld1w {z1.s, z9.s}, pn8/z, [x0]",
	"ld1b {z0.b, z4.b, z8.b, z12.b}, pn8/z, [x0]", "st1d {z17.d, z21.d, z25.d, z29.d}, pn10, [x2, x3, lsl #3]", "st1w {z3.s, z7.s, z11.s, z15.s}, pn8, [x0]",
	"pext p0.s, pn8[0]", "pext p3.b, pn15[3]", "luti2 z0.s, zt0, z1[0]", "luti2 z5.b, zt0, z2[3]", "luti4 z0.h, zt0, z1[1]",
	"fadd z0.s, z1.s, z2.s", "fadd z0.s, p0/m, z0.s, z1.s", "fsub z0.d, p0/m, z0.d, z1.d", "fmul z0.s, z1.s, z2.s", "fmla z0.s, p0/m, z1.s, z2.s", "fmls z3.h, p2/m, z4.h, z5.h",
	"fmul z0.s, z1.s, z2.s[1]", "fmul z0.d, z1.d, z2.d[1]", "fmul z0.h, z1.h, z7.h[7]", "fmla z0.s, z1.s, z2.s[3]", "fmax z0.s, p0/m, z0.s, z1.s", "fneg z0.s, p0/m, z1.s", "fabs z2.d, p1/m, z3.d",
	"add z0.s, z1.s, z2.s", "sub z0.b, z1.b, z2.b", "add z0.s, z0.s, #1", "add z0.s, z0.s, #1, lsl #8", "sub z1.h, z1.h, #255", "mul z0.s, p0/m, z0.s, z1.s", "and z0.d, z1.d, z2.d", "orr z0.d, z1.d, z2.d", "eor z0.d, z1.d, z2.d",
	"lsl z0.s, z1.s, #2", "lsr z0.s, z1.s, #31", "asr z0.d, z1.d, #63", "lsl z0.s, p0/m, z0.s, z1.s",
	"dup z0.s, #0", "dup z0.s, #-128", "dup z0.b, #127", "dup z0.h, #1, lsl #8", "dup z0.s, w0", "dup z0.d, x1", "dup z0.s, z1.s[3]", "mov z0.s, #0", "mov z0.s, w0", "mov z0.d, x1",
	"fmov z0.s, #0.0", "fmov z0.s, #1.0", "fmov z0.d, #0.5", "fdup z0.s, #1.0", "fmov z0.s, p0/m, #1.0", "fcpy z0.s, p0/m, #1.0",
	"index z0.s, #0, #1", "index z0.s, w0, #1", "index z0.d, #0, x1", "index z0.b, w0, w1",
	"mov z0.d, z1.d", "mov z0.s, p0/m, z1.s", "movprfx z0, z1", "movprfx z0.s, p0/m, z1.s", "movprfx z0.s, p0/z, z1.s", "sel z0.s, p0, z1.s, z2.s", "cpy z0.s, p0/m, w1", "cpy z0.d, p0/m, sp",
	"zip1 z0.s, z1.s, z2.s", "uzp1 z0.s, z1.s, z2.s", "trn2 z0.b, z1.b, z2.b", "rev z0.s, z1.s", "ext z0.b, z0.b, z1.b, #4", "splice z0.s, p0, z0.s, z1.s",
	"faddv s0, p0, z0.s", "fmaxv d0, p1, z3.d", "uaddv d0, p0, z0.s", "smaxv b0, p0, z0.b", "fadda s0, p0, s0, z1.s",
	"fcvt z0.h, p0/m, z1.s", "fcvt z0.d, p0/m, z1.s", "scvtf z0.s, p0/m, z1.s", "fcvtzs z0.s, p0/m, z1.s", "ucvtf z0.d, p0/m, z1.d",
	"cmpeq p0.s, p1/z, z0.s, z1.s", "cmpgt p0.s, p1/z, z0.s, #5", "cmplo p2.b, p3/z, z0.b, z1.b", "cmpne p0.d, p0/z, z0.d, #0", "fcmgt p0.s, p1/z, z0.s, z1.s", "fcmeq p0.s, p1/z, z0.s, #0.0",
	"and p0.b, p1/z, p2.b, p3.b", "orr p0.b, p1/z, p2.b, p3.b", "not p0.b, p1/z, p2.b", "sel p0.b, p1, p2.b, p3.b", "mov p0.b, p1.b", "mov p0.b, p1/z, p2.b", "ptest p0, p1.b", "pnext p0.s, p1, p0.s", "brka p0.b, p1/z, p2.b",
	"uunpklo z0.h, z1.b", "sunpkhi z0.s, z1.h", "uzp2 z0.h, z1.h, z2.h", "tbl z0.s, {z1.s}, z2.s", "clz z0.s, p0/m, z1.s", "cnt z0.b, p0/m, z1.b",
	"sdot z0.s, z1.b, z2.b", "udot z0.d, z1.h, z2.h", "sdot z0.s, z1.b, z2.b[1]", "fmmla z0.s, z1.s, z2.s",
	"bfdot z0.s, z1.h, z2.h", "bfmlalb z0.s, z1.h, z2.h", "bfcvt z0.h, p0/m, z1.s",
	"whilelt pn8.b, x0, x1, vlx4", "whilege pn9.d, x2, x3, vlx2", "ptrue pn9.h", "pext {p0.s, p1.s}, pn8[1]",
	"add {z0.s, z1.s}, {z0.s, z1.s}, z2.s", "smax {z0.s - z3.s}, {z0.s - z3.s}, z4.s", "fmax {z0.s, z1.s}, {z0.s, z1.s}, {z2.s, z3.s}",
	"sqcvt z0.h, {z0.s, z1.s}", "fcvtzs {z0.s, z1.s}, {z0.s, z1.s}", "uzp {z0.s, z1.s}, z2.s, z3.s", "zip {z0.d - z3.d}, {z4.d - z7.d}",
	"movaz z0.s, za0h.s[w12, 0]", "movaz {z0.d, z1.d}, za.d[w8, 0, vgx2]",
	"sclamp z0.s, z1.s, z2.s", "fclamp z0.s, z1.s, z2.s", "fclamp {z0.s, z1.s}, z2.s, z3.s",
	"fdot za.s[w8, 0, vgx4], {z0.h - z3.h}, z4.h", "bfmlal za.s[w8, 0:1, vgx2], {z0.h, z1.h}, z2.h", "fvdot za.s[w8, 0, vgx2], {z0.h, z1.h}, z2.h[1]",
	"zero za.d[w8, 0, vgx2]", "zero za.d[w11, 7, vgx4]", "zero za.d[w8, 0:1]", "zero za.d[w8, 0:3, vgx2]",
	"sqrshr z0.h, {z0.s, z1.s}, #16", "urshl z0.s, p0/m, z0.s, z1.s", "sdot za.s[w8, 0, vgx4], {z0.h - z3.h}, z4.h[1]",
	"fmopa za0.h, p0/m, p1/m, z0.h, z1.h", "smopa za0.s, p0/m, p1/m, z0.h, z1.h", "fmopa za0.s, p0/m, p1/m, z0.b, z1.b",
}

// The SVE/SME vocabulary against the host LLVM assembler (skipped without
// it): both must produce the same word wherever LLVM knows the spelling on
// apple-m4; what LLVM rejects for the M4's features (fmopa za0.h needs
// sme-f16f16) we must reject too.
func TestSMEAgainstLLVM(t *testing.T) {
	llvmMC := findLLVMMC(t)
	// movprfx makes LLVM reject the marker that follows it in a batch: those
	// lines are assembled one per process.
	var batch []string
	for _, text := range smeSamples {
		if strings.HasPrefix(text, "movprfx") {
			batch = append(batch, "nop")
			continue
		}
		batch = append(batch, text)
	}
	expected := llvmEncode(t, llvmMC, batch)
	for i, text := range smeSamples {
		if strings.HasPrefix(text, "movprfx") {
			expected[i] = llvmEncodeOne(t, llvmMC, text)
		}
	}
	var failures []string
	agreed, rejected := 0, 0
	for i, text := range smeSamples {
		word, err := encodeText(t, text)
		if expected[i] == nil {
			if err == nil {
				failures = append(failures, fmt.Sprintf("  %-60s llvm rejects; we %08x", text, word))
			} else {
				rejected++
			}
			continue
		}
		if err != nil {
			failures = append(failures, fmt.Sprintf("  %-60s llvm %x; we fail: %v", text, expected[i], err))
			continue
		}
		if !bytes.Equal(wordBytes(word), expected[i]) {
			failures = append(failures, fmt.Sprintf("  %-60s llvm %x; we %x", text, expected[i], wordBytes(word)))
			continue
		}
		agreed++
	}
	t.Logf("%d SVE/SME spellings agree with llvm-mc, %d rejected by both", agreed, rejected)
	if len(failures) > 0 {
		t.Errorf("%d SVE/SME spellings disagree:\n%s", len(failures), strings.Join(failures, "\n"))
	}
}

// llvmEncodeOne assembles a single line in its own llvm-mc process.
func llvmEncodeOne(t *testing.T, llvmMC string, line string) []byte {
	cmd := exec.Command(llvmMC, "--triple=arm64", "-mcpu=apple-m4", "--show-encoding")
	cmd.Stdin = strings.NewReader(line + "\n")
	out, err := cmd.Output()
	if err != nil {
		return nil
	}
	for _, l := range strings.Split(string(out), "\n") {
		if m := llvmEncodingLine.FindStringSubmatch(l); m != nil {
			word := make([]byte, 4)
			for i := 0; i < 4; i++ {
				v, _ := strconv.ParseUint(m[i+1][2:], 16, 8)
				word[i] = byte(v)
			}
			return word
		}
	}
	return nil
}

// The checker's SME disciplines (asm/isa_sme.go): a complete outer-product
// kernel is admitted, and each rule has a body it refuses.
func TestSMEChecker(t *testing.T) {
	kernel := `fmopa_f32: (at: []f32, b: []f32, c: [*]f32, n: u32) -> () = {
  bind x0, w1 = at
  bind x2, w3 = b
  bind x4, w5 = c
  bind w6 = n
  clobber w9, w11, w12
  clobber z0, z1, p0
  clobber v8, v9, v10, v11, v12, v13, v14, v15
  frame 64
  sub sp, sp, #64
  stp d8, d9, [sp]           // smstart and smstop zero d8-d15, the caller's
  stp d10, d11, [sp, #16]
  stp d12, d13, [sp, #32]
  stp d14, d15, [sp, #48]
  udiv w9, w1, w6
  mov w11, w6
  lsl x11, x11, #2
  smstart
  whilelt p0.s, wzr, w6
  zero {za0.s}
loop:
  cbz w9, store
  ld1w {z0.s}, p0/z, [x0]
  ld1w {z1.s}, p0/z, [x2]
  fmopa za0.s, p0/m, p0/m, z0.s, z1.s
  add x0, x0, x11
  add x2, x2, x11
  sub w9, w9, #1
  b loop
store:
  mov w12, #0
rows:
  cmp w12, w6
  b.hs done
  st1w {za0h.s[w12, 0]}, p0, [x4]
  add x4, x4, x11
  add w12, w12, #1
  b rows
done:
  smstop
  ldp d8, d9, [sp]
  ldp d10, d11, [sp, #16]
  ldp d12, d13, [sp, #32]
  ldp d14, d15, [sp, #48]
  add sp, sp, #64
  ret
}
`
	unit, errs := ParseUnit("sme.oakasm", kernel)
	if len(errs) != 0 {
		t.Fatalf("parse: %v", errs)
	}
	sig, err := parseSignature("fmopa_f32: (at: []f32, b: []f32, c: [*]f32, n: u32) -> ()")
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(unit.Functions[0], sig, nil); len(findings) != 0 {
		t.Fatalf("kernel refused: %v", findings)
	}
	if _, _, err := EncodeFunction(unit.Functions[0]); err != nil {
		t.Fatalf("kernel not encodable: %v", err)
	}

	cases := []struct {
		name, decl, body, want string
	}{
		{"streaming instruction outside streaming mode", "f: (n: u32) -> ()", "  bind w0 = n\n  clobber z0, z1, z2\n  fadd z0.s, z1.s, z2.s\n  ret", "enter streaming mode"},
		{"ZA instruction with ZA disabled", "f: (n: u32) -> ()", "  bind w0 = n\n  smstart sm\n  zero {za0.s}\n  smstop\n  ret", "uses the ZA array"},
		{"outer product without ZA", "f: (n: u32) -> ()", "  bind w0 = n\n  clobber z0, p0\n  smstart sm\n  ptrue p0.s\n  dup z0.s, #1\n  fmopa za0.s, p0/m, p0/m, z0.s, z0.s\n  smstop\n  ret", "needs streaming mode and the ZA array"},
		{"Advanced SIMD in streaming mode", "f: (n: u32) -> ()", "  bind w0 = n\n  clobber v0, v1\n  smstart\n  movi v1.4s, #1\n  add v0.4s, v1.4s, v1.4s\n  smstop\n  ret", "illegal in streaming mode"},
		{"read of a zeroed vector", "f: (x: f32) -> f32", "  bind s0 = x\n  smstart\n  fadd s0, s0, s0\n  smstop\n  ret", "zeroed the vector registers"},
		{"result zeroed by smstop", "f: (x: f32) -> f32", "  bind s0 = x\n  clobber z1\n  smstart\n  fmov z1.s, #1.0\n  fmov s0, #2.0\n  smstop\n  ret", "ret without producing the result in v0"},
		{"ret in streaming mode", "f: (n: u32) -> ()", "  bind w0 = n\n  smstart\n  ret", "smstop first"},
		{"predicate without clobber", "f: (n: u32) -> ()", "  bind w0 = n\n  smstart\n  ptrue p0.s\n  smstop\n  ret", "clobber p0"},
		{"predicate read before write", "f: (a: []u32) -> ()", "  bind x0, w1 = a\n  clobber z0, p0\n  smstart\n  ld1w {z0.s}, p0/z, [x0]\n  smstop\n  ret", "read of p0/z before any write"},
		{"z register without clobber", "f: (n: u32) -> ()", "  bind w0 = n\n  smstart\n  dup z3.s, #0\n  smstop\n  ret", "clobber v3"},
		{"call in streaming mode", "f: (n: u32) -> ()", "  bind w0 = n\n  clobber x29, x30\n  frame 16\n  stp x29, x30, [sp, #-16]!\n  smstart\n  bl helper\n  smstop\n  ldp x29, x30, [sp], #16\n  ret", "no streaming interface"},
		{"template mismatch", "f: (n: u32) -> ()", "  bind w0 = n\n  clobber z0, z1, p0\n  smstart\n  ptrue p0.s\n  fmopa za0.s, p0/m, p0/m, z0.s, z1.d\n  smstop\n  ret", "match no reading"},
		{"tile of the wrong size", "f: (n: u32) -> ()", "  bind w0 = n\n  clobber z0, p0\n  smstart\n  ptrue p0.s\n  dup z0.s, #1\n  fmopa za5.s, p0/m, p0/m, z0.s, z0.s\n  smstop\n  ret", "za5 is not a tile"},
		{"slice index outside w12-w15", "f: (a: []u32) -> ()", "  bind x0, w1 = a\n  clobber z0, p0, w9\n  smstart\n  ptrue p0.s\n  mov w9, #0\n  ld1w {za0h.s[w9, 0]}, p0/z, [x0]\n  smstop\n  ret", "w9 is below the registers"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			unit, errs := ParseUnit(tc.name+".oakasm", tc.decl+" = {\n"+tc.body+"\n}\n")
			got := fmt.Sprint(errs)
			if len(errs) == 0 {
				sig, err := parseSignature(tc.decl)
				if err != nil {
					t.Fatal(err)
				}
				got = fmt.Sprint(Check(unit.Functions[0], sig, map[string]bool{"helper": true}))
			}
			if !strings.Contains(got, tc.want) {
				t.Errorf("want a finding containing %q, got %s", tc.want, got)
			}
		})
	}
}
