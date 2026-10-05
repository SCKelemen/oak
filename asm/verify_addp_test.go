package asm

import (
	"crypto/sha256"
	"fmt"
	"strings"
	"testing"
)

func TestVerifyScalarADDP(t *testing.T) {
	decl := "sum: (a, b, seed: u64) -> u64"
	setup := "bind x0 = a\n bind x1 = b\n bind x2 = seed\n clobber x9, x10, v0, v1\n dup v0.2d, x0\n ins v0.d[1], x1\n movi v1.16b, #255\n"
	for _, dst := range []int{0, 1} {
		t.Run(fmt.Sprintf("destination_v%d", dst), func(t *testing.T) {
			reduce := fmt.Sprintf("addp d%d, v0.2d\n", dst)
			result := fmt.Sprintf("umov x9, v%d.d[0]\n add x0, x2, x9\n ret", dst)
			if got := verifyCase(t, decl, "seed + (a + b)", setup+reduce+result); got.Kind != VerdictProven {
				t.Fatalf("free halves and seed: %s: %s", got.Kind, got.Message)
			}
			high := fmt.Sprintf("umov x0, v%d.d[1]\n ret", dst)
			if got := verifyCase(t, decl, "u64(0)", setup+reduce+high); got.Kind != VerdictProven {
				t.Fatalf("upper half not cleared: %s: %s", got.Kind, got.Message)
			}
			for name, wrong := range map[string]string{
				"wrong_half": strings.Replace(result, ".d[0]", ".d[1]", 1),
				"drop_seed":  strings.Replace(result, "x2, x9", "xzr, x9", 1),
				"narrow_add": strings.Replace(result, "add x0, x2, x9", "add w0, w2, w9", 1),
			} {
				if got := verifyCase(t, decl, "seed + (a + b)", setup+reduce+wrong); got.Kind != VerdictMismatch {
					t.Fatalf("%s: %s: %s", name, got.Kind, got.Message)
				}
			}
		})
	}
	// Observe both source halves after writing a distinct destination, with
	// unequal coefficients so swapping or overwriting either half disagrees.
	source := "umov x9, v0.d[0]\n umov x10, v0.d[1]\n add x0, x9, x10, lsl #1\n ret"
	if got := verifyCase(t, decl, "a + (b << 1)", setup+"addp d1, v0.2d\n"+source); got.Kind != VerdictProven {
		t.Fatalf("source preservation: %s: %s", got.Kind, got.Message)
	}
}

func TestScalarADDPRefusesOtherForms(t *testing.T) {
	v := func(n int, arrangement string, lane int) Register {
		return Register{Class: ClassV, Num: n, Vec: arrangement, Lane: lane}
	}
	for name, operands := range map[string][]Operand{
		"vector_three_operand": {v(1, "2d", -1), v(0, "2d", -1), v(0, "2d", -1)},
		"sve_three_operand":    {Register{Class: ClassZ, Num: 1, Vec: "d", Lane: -1}, Register{Class: ClassZ, Num: 0, Vec: "d", Lane: -1}, Register{Class: ClassZ, Num: 0, Vec: "d", Lane: -1}},
		"scalar_s":             {v(1, "s", -1), v(0, "2d", -1)},
		"vector_4s":            {v(1, "d", -1), v(0, "4s", -1)},
		"source_lane":          {v(1, "d", -1), v(0, "2d", 0)},
		"destination_lane":     {v(1, "d", 0), v(0, "2d", -1)},
		"missing_operand":      {v(1, "d", -1)},
	} {
		t.Run(name, func(t *testing.T) {
			state := symbolicState{}
			state.writeVec(0, vecOfLanes([]*term{paramTerm("a", 64), paramTerm("b", 64)}, 64))
			x := pathExecutor{}
			if _, ok := x.stepVector(Instruction{Mnemonic: "addp", Operands: operands}, &state); ok {
				t.Fatal("unsupported ADDP form acquired scalar semantics")
			}
			if len(state.vregs) != 1 {
				t.Fatal("refusal wrote destination")
			}
		})
	}
	x, state := pathExecutor{}, symbolicState{}
	if _, ok := x.stepVector(Instruction{Mnemonic: "addp", Operands: []Operand{v(1, "d", -1), v(0, "2d", -1)}}, &state); ok || len(state.vregs) != 0 {
		t.Fatal("unbound source must refuse without writing")
	}
}

func TestScalarADDPEncoding(t *testing.T) {
	// ADDP_asisdpair_only, not ADDP_asimdsame_only: the only variable
	// fields are Rn[9:5] and Rd[4:0]. Check every alias/register pair.
	for d := 0; d < 32; d++ {
		for n := 0; n < 32; n++ {
			instr := Instruction{Mnemonic: "addp", Operands: []Operand{
				Register{Class: ClassV, Num: d, Vec: "d", Lane: -1},
				Register{Class: ClassV, Num: n, Vec: "2d", Lane: -1},
			}}
			got, reloc, err := EncodeInstruction(instr, 0, nil)
			want := uint32(0x5ef1b800 | n<<5 | d)
			if err != nil || reloc != nil || got != want {
				t.Fatalf("d%d,v%d.2d: %#x != %#x (reloc %v, err %v)", d, n, got, want, reloc, err)
			}
		}
	}
}

// These exact declarations make the reviewed Sail grounding drift-sensitive.
// They are not a refinement proof, transitive dependency closure, or a model
// of FP/AdvSIMD enable traps. Native execution assumes the SIMD lane enabled.
func TestScalarADDPPinnedSailContract(t *testing.T) {
	for _, tc := range []struct{ file, name, source, mutation string }{
		{"aarch64_vector.sail", "vector_reduce_add_sisd_decode", `
val vector_reduce_add_sisd_decode : (bits(5), bits(5), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}
function vector_reduce_add_sisd_decode (Rd, Rn, opcode, size, U) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    if size != 0b11 then { throw(Error_Undefined()) };
    let 'esize = shl_int(8, UInt(size));
    let 'datasize = esize * 2;
    let 'elements = 2;
    let op = ReduceOp_ADD;
    __PostDecode();
    vector_reduce_add_sisd(d, datasize, esize, n, op)
}`, "esize * 2"},
		{"aarch64_vector.sail", "vector_reduce_add_sisd", `
val vector_reduce_add_sisd : forall 'd 'datasize 'esize 'n,
  ('n >= 0 & 'n <= 31) & 'datasize >= 0 & ('esize >= 0 & 'esize >= 0) & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), int('esize), int('n), ReduceOp) -> unit effect {escape, rreg, undef, wreg}
function vector_reduce_add_sisd (d, datasize, esize, n, op) = {
    CheckFPAdvSIMDEnabled64();
    let operand : bits('datasize) = V(n);
    V(d) = Reduce(op, operand, esize)
}`, "V(d)"},
		{"aarch64_vector.sail", "Reduce", `
val Reduce : forall 'N 'esize,
  'N >= 0 & ('esize >= 0 & 'esize >= 0).
  (ReduceOp, bits('N), int('esize)) -> bits('esize) effect {escape, rreg, undef, wreg}
function Reduce (op, input, esize) = {
    half : int = undefined : int;
    hi : bits('esize) = undefined : bits('esize);
    lo : bits('esize) = undefined : bits('esize);
    result : bits('esize) = undefined : bits('esize);
    if 'N == esize then { return(slice(input, 0, esize)) };
    let half = 'N / 2;
    let hi = Reduce(op, slice(input, half, negate(half) + 'N), esize);
    let lo = Reduce(op, slice(input, 0, half), esize);
    match op {
      ReduceOp_FMINNUM => { result = FPMinNum(lo, hi, FPCR) },
      ReduceOp_FMAXNUM => { result = FPMaxNum(lo, hi, FPCR) },
      ReduceOp_FMIN => { result = FPMin(lo, hi, FPCR) },
      ReduceOp_FMAX => { result = FPMax(lo, hi, FPCR) },
      ReduceOp_FADD => { result = FPAdd(lo, hi, FPCR) },
      ReduceOp_ADD => { result = lo + hi }
    };
    let result = result;
    result
}`, "lo + hi"},
		{"aarch64.sail", "aset_V", `
val aset_V : forall ('width : Int) ('n : Int), ('n >= 0 & 'n <= 31).
  (int('n), bits('width)) -> unit effect {escape, wreg}
function aset_V (n, value_name) = {
    assert('width == 8 | 'width == 16 | 'width == 32 | 'width == 64 | 'width == 128);
    _V[n] = ZeroExtend(value_name, 128)
}`, "ZeroExtend(value_name, 128)"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			canonical, err := sailSTRExecutionTokens(tc.source)
			if err != nil {
				t.Fatal(err)
			}
			pin := sailSTRExecutionFunctionPin{file: tc.file, name: tc.name, sha256: fmt.Sprintf("%x", sha256.Sum256([]byte(canonical)))}
			source := readSailSTRExecutionModel(t, tc.file)
			if err := auditSailSTRExecutionFunction(source, pin); err != nil {
				t.Fatal(err)
			}
			// Exercise the audit itself: a changed operation and a duplicate
			// function declaration must both fail, even with the original present.
			for _, mutant := range []string{strings.Replace(tc.source, tc.mutation, "WRONG", 1), tc.source + tc.source} {
				if err := auditSailSTRExecutionFunction(mutant, pin); err == nil {
					t.Fatal("source drift accepted")
				}
			}
		})
	}
}
