package asm

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strconv"
	"strings"
	"testing"
)

// The silicon differential (docs/spec/94-assembler.md §8): the verifier's
// term semantics for every modeled register-level instruction, executed
// symbolically here, must agree with the instruction executed natively on
// the host's AArch64 core over a deterministic input set. This turns the
// model — our reading of the Arm manual — into agreement with the
// hardware, bit for bit; a divergence names the instruction and inputs.
//
// Each case is one .oakasm body over parameters a, b (x0/x1 or w0/w1) with
// x9/x10 as scratch, returning in x0/w0. The same text is parsed by the
// unit parser and pasted into an inline-asm C function with the operands
// pinned to those registers.

type siliconCase struct {
	name  string
	width int // 32 or 64
	body  string
}

func siliconCases() []siliconCase {
	x := func(name, body string) siliconCase { return siliconCase{name, 64, body} }
	w := func(name, body string) siliconCase { return siliconCase{name, 32, body} }
	cases := []siliconCase{
		x("add", "add x0, x0, x1"), w("add w", "add w0, w0, w1"), x("sub", "sub x0, x0, x1"), w("sub w", "sub w0, w0, w1"),
		x("and", "and x0, x0, x1"), x("orr", "orr x0, x0, x1"), x("eor", "eor x0, x0, x1"), x("bic", "bic x0, x0, x1"), x("orn", "orn x0, x0, x1"), x("eon", "eon x0, x0, x1"),
		x("neg", "neg x0, x1"), x("mvn", "mvn x0, x1"), w("mvn w", "mvn w0, w1"),
		x("lsl reg", "and x1, x1, #63\n  lsl x0, x0, x1"), x("lsr reg", "and x1, x1, #63\n  lsr x0, x0, x1"), x("asr reg", "and x1, x1, #63\n  asr x0, x0, x1"), x("ror reg", "and x1, x1, #63\n  ror x0, x0, x1"),
		w("lsl w reg", "and w1, w1, #31\n  lsl w0, w0, w1"), w("lsr w reg", "and w1, w1, #31\n  lsr w0, w0, w1"), w("asr w reg", "and w1, w1, #31\n  asr w0, w0, w1"), w("ror w reg", "and w1, w1, #31\n  ror w0, w0, w1"),
		x("lsl imm", "lsl x0, x0, #13"), x("lsr imm", "lsr x0, x0, #13"), x("asr imm", "asr x0, x0, #13"), x("ror imm", "ror x0, x0, #13"), w("ror w imm", "ror w0, w0, #7"),
		x("extr", "extr x0, x0, x1, #17"), w("extr w", "extr w0, w0, w1, #5"),
		x("rev", "rev x0, x0"), w("rev w", "rev w0, w0"), x("rev16", "rev16 x0, x0"), w("rev16 w", "rev16 w0, w0"), x("rev32", "rev32 x0, x0"), x("rbit", "rbit x0, x0"), w("rbit w", "rbit w0, w0"),
		x("clz", "clz x0, x0"), w("clz w", "clz w0, w0"), x("cls", "cls x0, x0"), w("cls w", "cls w0, w0"),
		x("sxtb", "sxtb x0, w0"), x("sxth", "sxth x0, w0"), x("sxtw", "sxtw x0, w0"), w("uxtb", "uxtb w0, w0"), w("uxth", "uxth w0, w0"), w("sxtb w", "sxtb w0, w0"), w("sxth w", "sxth w0, w0"),
		x("movz/movk", "movz x0, #0x1234, lsl #16\n  movk x0, #0x5678, lsl #48\n  movk x0, #0x9abc"), x("movn", "movn x0, #0x10, lsl #32"),
		x("mul", "mul x0, x0, x1"), w("mul w", "mul w0, w0, w1"), x("madd", "madd x0, x0, x1, x1"), x("msub", "msub x0, x0, x1, x1"), x("mneg", "mneg x0, x0, x1"),
		x("smull", "smull x0, w0, w1"), x("umull", "umull x0, w0, w1"), x("smaddl", "smaddl x0, w0, w1, x1"), x("umaddl", "umaddl x0, w0, w1, x1"), x("smsubl", "smsubl x0, w0, w1, x1"), x("umsubl", "umsubl x0, w0, w1, x1"),
		x("smulh", "smulh x0, x0, x1"), x("umulh", "umulh x0, x0, x1"), x("udiv", "udiv x0, x0, x1"), x("sdiv", "sdiv x0, x0, x1"), w("udiv w", "udiv w0, w0, w1"), w("sdiv w", "sdiv w0, w0, w1"),
		x("ubfx", "ubfx x0, x0, #7, #20"), x("ubfiz", "ubfiz x0, x0, #7, #20"), x("sbfx", "sbfx x0, x0, #7, #20"), x("bfi", "bfi x0, x1, #7, #20"), w("sbfx w", "sbfx w0, w0, #3, #9"), w("bfi w", "bfi w0, w1, #3, #9"),
		x("sbfiz", "sbfiz x0, x0, #7, #20"), w("sbfiz w", "sbfiz w0, w1, #3, #9"), x("bfxil", "bfxil x0, x1, #7, #20"), w("bfxil w", "bfxil w0, w1, #3, #9"), x("bfc", "bfc x0, #7, #20"), w("bfc w", "bfc w0, #3, #9"),
		x("shifted lsl", "add x0, x0, x1, lsl #3"), x("shifted lsr", "sub x0, x0, x1, lsr #7"), x("shifted asr", "and x0, x0, x1, asr #7"), x("shifted ror", "eor x0, x0, x1, ror #9"),
		x("extended uxtw", "add x0, x0, w1, uxtw #2"), x("extended sxtw", "add x0, x0, w1, sxtw"), x("extended uxtb", "sub x0, x0, w1, uxtb"), x("extended sxth", "cmp x0, w1, sxth\n  cset x0, lo"),
		x("cmn", "cmn x0, x1\n  cset x0, eq"), x("tst", "tst x0, x1\n  cset x0, ne"), x("ands", "ands x0, x0, x1\n  cset x0, mi"), x("bics", "bics x9, x0, x1\n  cset x0, eq"),
		x("negs", "negs x0, x1\n  cset x0, vs"),
		x("adds/adc chain", "adds x9, x0, x1\n  adc x0, x0, x1"), x("adds/sbc chain", "adds x9, x0, x1\n  sbc x0, x0, x1"), x("subs/ngc", "subs x9, x0, x1\n  ngc x0, x1"),
		x("cinc", "cmp x0, x1\n  cinc x0, x0, lo"), x("cinv", "cmp x0, x1\n  cinv x0, x0, ge"), x("cneg", "cmp x0, x1\n  cneg x0, x1, lt"), x("csetm", "cmp x0, x1\n  csetm x0, hi"),
		x("csinc", "cmp x0, x1\n  csinc x0, x0, x1, ls"), x("csinv", "cmp x0, x1\n  csinv x0, x0, x1, gt"), x("csneg", "cmp x0, x1\n  csneg x0, x0, x1, le"),
		x("ccmp hs", "cmp x0, x1\n  ccmp x1, x0, #2, hs\n  cset x0, lo"), x("ccmp eq", "cmp x0, #7\n  ccmp x1, #9, #4, eq\n  cset x0, ne"), x("ccmn", "cmp x0, x1\n  ccmn x0, x1, #0, ne\n  cset x0, mi"),
	}
	// Every condition code after cmp, adds, subs, and tst.
	for _, code := range []string{"eq", "ne", "hs", "lo", "hi", "ls", "ge", "lt", "gt", "le", "mi", "pl", "vs", "vc"} {
		cases = append(cases,
			x("cmp/"+code, "cmp x0, x1\n  cset x0, "+code),
			w("cmp w/"+code, "cmp w0, w1\n  cset w0, "+code),
			x("adds/"+code, "adds x9, x0, x1\n  cset x0, "+code),
			w("adds w/"+code, "adds w9, w0, w1\n  cset w0, "+code),
			x("subs/"+code, "subs x9, x0, x1\n  csel x0, x0, x1, "+code),
			x("tst/"+code, "tst x0, x1\n  cset x0, "+code),
		)
	}
	return append(cases, siliconVectorCases()...)
}

// siliconVectorCases: the vector-file instructions the verifier models
// (asm/verify_vector.go), each over v0 = {a, a} and v1 = {b, a} — built
// from the scalar inputs by dup and ext — with the result read back from
// one 64-bit half of v0 (or a general register for the lane moves).
func siliconVectorCases() []siliconCase {
	setup := "dup v0.2d, x0\n  dup v1.2d, x1\n  ext v1.16b, v1.16b, v0.16b, #8\n  "
	var cases []siliconCase
	both := func(name, body string) {
		cases = append(cases,
			siliconCase{"vec " + name + " lo", 64, setup + body + "\n  umov x0, v0.d[0]"},
			siliconCase{"vec " + name + " hi", 64, setup + body + "\n  umov x0, v0.d[1]"})
	}
	scalar := func(name string, width int, body string) {
		cases = append(cases, siliconCase{"vec " + name, width, setup + body})
	}
	for _, arr := range []string{"16b", "8h", "4s", "2d"} {
		for _, op := range []string{"add", "sub", "cmeq", "cmhi", "cmhs", "uqsub", "uqadd"} {
			both(op+" "+arr, fmt.Sprintf("%s v0.%s, v0.%s, v1.%s", op, arr, arr, arr))
		}
		if arr != "2d" {
			for _, op := range []string{"umin", "umax"} {
				both(op+" "+arr, fmt.Sprintf("%s v0.%s, v0.%s, v1.%s", op, arr, arr, arr))
			}
		}
		both("cmeq zero "+arr, fmt.Sprintf("cmeq v0.%s, v1.%s, #0", arr, arr))
	}
	for _, op := range []string{"and", "orr", "eor", "bic"} {
		both(op, op+" v0.16b, v0.16b, v1.16b")
	}
	both("orr move", "orr v0.16b, v1.16b, v1.16b")
	both("ushr 16b", "ushr v0.16b, v1.16b, #3")
	both("sshr 16b", "sshr v0.16b, v1.16b, #7")
	both("shl 8h", "shl v0.8h, v1.8h, #5")
	both("ushr 4s", "ushr v0.4s, v1.4s, #9")
	both("sshr 2d", "sshr v0.2d, v1.2d, #33")
	both("dup 16b w", "dup v0.16b, w1")
	both("dup 8h w", "dup v0.8h, w1")
	both("dup 4s w", "dup v0.4s, w1")
	both("dup 16b lane", "dup v0.16b, v1.b[3]")
	both("dup 4s lane", "dup v0.4s, v1.s[2]")
	both("movi 16b", "movi v0.16b, #85")
	both("movi 4s", "movi v0.4s, #7")
	both("tbl", "tbl v0.16b, {v0.16b}, v1.16b")
	both("tbl nibbles", "ushr v1.16b, v1.16b, #4\n  tbl v0.16b, {v0.16b}, v1.16b")
	both("ext 3", "ext v0.16b, v0.16b, v1.16b, #3")
	both("ext 8", "ext v0.16b, v0.16b, v1.16b, #8")
	both("ext 15", "ext v0.16b, v0.16b, v1.16b, #15")
	both("umaxv b", "umaxv b0, v1.16b")
	both("umaxv h", "umaxv h0, v1.8h")
	both("umaxv s", "umaxv s0, v1.4s")
	both("uminv b", "uminv b0, v1.16b")
	both("addv 8b", "addv b0, v1.8b")
	both("addv 16b", "addv b0, v1.16b")
	both("addv 8h", "addv h0, v1.8h")
	both("addv 4s", "addv s0, v1.4s")
	both("addp scalar 2d", "addp d0, v1.2d")
	both("addp scalar alias", "addp d1, v1.2d\n mov v0.16b, v1.16b")
	both("cnt 16b", "cnt v0.16b, v1.16b")
	both("cnt 8b", "cnt v0.8b, v1.8b")
	both("fmov d from x", "fmov d0, x1")
	both("fmov s from w", "fmov s0, w1")
	scalar("umov b", 32, "umov w0, v1.b[5]")
	scalar("umov h", 32, "umov w0, v1.h[3]")
	scalar("umov s", 32, "umov w0, v1.s[1]")
	scalar("smov b w", 32, "smov w0, v1.b[9]")
	scalar("smov h w", 32, "smov w0, v1.h[2]")
	scalar("umov d", 64, "umov x0, v1.d[1]")
	scalar("smov s x", 64, "smov x0, v1.s[1]")
	scalar("smov b x", 64, "smov x0, v1.b[0]")
	scalar("fmov x from d", 64, "fmov x0, d1")
	scalar("fmov w from s", 32, "fmov w0, s1")
	// Floating point (asm/verify_float.go): the operation terms evaluate as
	// Go's IEEE arithmetic on a witness, so the hardware must agree bit for
	// bit — NaN payloads, signed zeros, and denormals included — on the
	// scalar views and the float arrangements.
	for _, arr := range []string{"4s", "2d"} {
		for _, op := range []string{"fadd", "fsub", "fmul", "fdiv", "fmin", "fmax", "fminnm", "fmaxnm", "faddp"} {
			both(op+" "+arr, fmt.Sprintf("%s v0.%s, v0.%s, v1.%s", op, arr, arr, arr))
		}
		both("fmla "+arr, fmt.Sprintf("fmla v0.%s, v1.%s, v1.%s", arr, arr, arr))
		both("fmls "+arr, fmt.Sprintf("fmls v0.%s, v1.%s, v1.%s", arr, arr, arr))
		for _, op := range []string{"fsqrt", "fneg", "fabs", "scvtf", "ucvtf", "fcvtzs", "fcvtzu"} {
			both(op+" "+arr, fmt.Sprintf("%s v0.%s, v1.%s", op, arr, arr))
		}
	}
	for _, view := range []string{"d", "s"} {
		v0, v1 := view+"0", view+"1"
		for _, op := range []string{"fadd", "fsub", "fmul", "fdiv", "fmin", "fmax", "fminnm", "fmaxnm"} {
			both(op+" "+view, fmt.Sprintf("%s %s, %s, %s", op, v0, v0, v1))
		}
		for _, op := range []string{"fmadd", "fmsub", "fnmadd", "fnmsub"} {
			both(op+" "+view, fmt.Sprintf("%s %s, %s, %s, %s", op, v0, v0, v1, v1))
		}
		for _, op := range []string{"fsqrt", "fneg", "fabs"} {
			both(op+" "+view, fmt.Sprintf("%s %s, %s", op, v0, v1))
		}
		for _, code := range []string{"eq", "ne", "mi", "ls", "gt", "ge", "hi", "lt", "le", "hs", "pl", "vs", "vc"} {
			both("fcmp/fcsel "+code+" "+view, fmt.Sprintf("fcmp %s, %s\n  fcsel %s, %s, %s, %s", v0, v1, v0, v0, v1, code))
		}
		both("fcmp zero/fcsel "+view, fmt.Sprintf("fcmp %s, #0.0\n  fcsel %s, %s, %s, mi", v1, v0, v0, v1))
	}
	both("fcvt d from s", "fcvt d0, s1")
	both("fcvt s from d", "fcvt s0, d1")
	both("scvtf d from x", "scvtf d0, x1")
	both("ucvtf d from x", "ucvtf d0, x1")
	both("scvtf s from w", "scvtf s0, w1")
	both("ucvtf s from w", "ucvtf s0, w1")
	both("scvtf d from w", "scvtf d0, w1")
	both("faddp d pair", "faddp d0, v1.2d")
	both("faddp s pair", "faddp s0, v1.2s")
	both("fmov d imm", "fmov d0, #2.5")
	both("fmov s imm", "fmov s0, #-1.0")
	both("mov s lane", "mov s0, v1.s[2]")
	both("mov lane insert", "mov v0.s[1], v1.s[3]")
	both("mov lane from w", "mov v0.s[2], w1")
	scalar("fcvtzs x from d", 64, "fcvtzs x0, d1")
	scalar("fcvtzu x from d", 64, "fcvtzu x0, d1")
	scalar("fcvtzs w from s", 32, "fcvtzs w0, s1")
	scalar("fcvtzu w from d", 32, "fcvtzu w0, d1")
	return cases
}

// siliconInputs is the deterministic operand set: boundaries and an LCG.
func siliconInputs() [][2]uint64 {
	boundary := []uint64{0, 1, 2, 3, 7, 8, 0x7F, 0x80, 0xFF, 0x100, 0x7FFF, 0x8000, 0xFFFF, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x100000000, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF}
	var inputs [][2]uint64
	for i, a := range boundary {
		inputs = append(inputs, [2]uint64{a, boundary[(i*7+3)%len(boundary)]})
	}
	state := uint64(0x2545F4914F6CDD1D)
	for i := 0; i < 40; i++ {
		state = state*6364136223846793005 + 1442695040888963407
		a := state
		state = state*6364136223846793005 + 1442695040888963407
		inputs = append(inputs, [2]uint64{a, state})
	}
	return inputs
}

func TestSiliconDifferential(t *testing.T) {
	if runtime.GOARCH != "arm64" {
		t.Skip("the silicon differential needs an AArch64 host")
	}
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler on PATH")
	}
	cases := siliconCases()
	inputs := siliconInputs()

	// The verifier's view: each body as a term over a and b.
	terms := make([]*term, len(cases))
	for i, c := range cases {
		decl := "f: (a, b: u64) -> u64"
		regs := "  bind x0 = a\n  bind x1 = b\n"
		if c.width == 32 {
			decl = "f: (a, b: u32) -> u32"
			regs = "  bind w0 = a\n  bind w1 = b\n"
		}
		unit, errs := ParseUnit("silicon.oakasm", decl+" = {\n"+regs+"  clobber x9, x10, v0, v1, v2, v3\n  "+c.body+"\n  ret\n}\n")
		if len(errs) != 0 {
			t.Fatalf("%s: parse: %v", c.name, errs)
		}
		sig, err := parseSignature(decl)
		if err != nil {
			t.Fatal(err)
		}
		if findings := Check(unit.Functions[0], sig, nil); len(findings) != 0 {
			t.Fatalf("%s: checker: %v", c.name, findings)
		}
		result, _, reason, ok := executeBody(unit.Functions[0], sig, nil)
		if !ok {
			t.Fatalf("%s: the verifier does not model this body (%s)", c.name, reason)
		}
		terms[i] = truncate(result, c.width)
	}

	// The silicon's view: the same bodies as inline asm, pinned registers.
	var source strings.Builder
	source.WriteString("#include <stdio.h>\n#include <stdint.h>\n")
	for i, c := range cases {
		fmt.Fprintf(&source, "static uint64_t run_%d(uint64_t a, uint64_t b) {\n", i)
		source.WriteString("  register uint64_t r0 __asm__(\"x0\") = a;\n  register uint64_t r1 __asm__(\"x1\") = b;\n")
		source.WriteString("  register uint64_t r9 __asm__(\"x9\") = 0;\n  register uint64_t r10 __asm__(\"x10\") = 0;\n")
		source.WriteString("  __asm__ volatile(\n")
		for _, line := range strings.Split(c.body, "\n") {
			fmt.Fprintf(&source, "    %q\n", strings.TrimSpace(line)+"\n\t")
		}
		source.WriteString("    : \"+r\"(r0), \"+r\"(r1), \"+r\"(r9), \"+r\"(r10) : : \"cc\", \"v0\", \"v1\", \"v2\", \"v3\");\n  return r0;\n}\n")
	}
	source.WriteString("int main(void) {\n  static const uint64_t inputs[][2] = {\n")
	for _, in := range inputs {
		fmt.Fprintf(&source, "    {%dULL, %dULL},\n", in[0], in[1])
	}
	source.WriteString("  };\n  const int n = sizeof(inputs) / sizeof(inputs[0]);\n")
	for i, c := range cases {
		mask := "0xFFFFFFFFFFFFFFFFULL"
		if c.width == 32 {
			mask = "0xFFFFFFFFULL"
		}
		fmt.Fprintf(&source, "  for (int j = 0; j < n; j++) printf(\"%d %%d %%llu\\n\", j, (unsigned long long)(run_%d(inputs[j][0] & %s, inputs[j][1] & %s) & %s));\n", i, i, mask, mask, mask)
	}
	source.WriteString("  return 0;\n}\n")

	dir := t.TempDir()
	cPath := filepath.Join(dir, "silicon.c")
	binPath := filepath.Join(dir, "silicon")
	if err := os.WriteFile(cPath, []byte(source.String()), 0o644); err != nil {
		t.Fatal(err)
	}
	if out, err := exec.Command(cc, "-std=c99", "-O1", "-o", binPath, cPath).CombinedOutput(); err != nil {
		t.Fatalf("cc failed: %v\n%s", err, out)
	}
	out, err := exec.Command(binPath).Output()
	if err != nil {
		t.Fatalf("running the harness: %v", err)
	}

	// Compare.
	divergences := 0
	for _, line := range strings.Split(strings.TrimSpace(string(out)), "\n") {
		fields := strings.Fields(line)
		if len(fields) != 3 {
			t.Fatalf("unexpected harness output %q", line)
		}
		i, _ := strconv.Atoi(fields[0])
		j, _ := strconv.Atoi(fields[1])
		got, _ := strconv.ParseUint(fields[2], 10, 64)
		c := cases[i]
		a, b := inputs[j][0], inputs[j][1]
		if c.width == 32 {
			a, b = a&0xFFFFFFFF, b&0xFFFFFFFF
		}
		want := terms[i].eval(map[string]uint64{"a": a, "b": b})
		if got != want {
			divergences++
			if divergences <= 20 {
				t.Errorf("%s: silicon %#x, model %#x at a=%#x b=%#x (term %s)", c.name, got, want, a, b, terms[i])
			}
		}
	}
	if divergences > 0 {
		t.Fatalf("%d divergences between the silicon and the verifier's semantics", divergences)
	}
	t.Logf("silicon agrees with the model on %d instruction bodies × %d inputs", len(cases), len(inputs))
}
