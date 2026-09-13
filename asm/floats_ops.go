package asm

import (
	"fmt"
	"math"
	"math/big"
)

// Floating-point arithmetic as uninterpreted operations (docs/spec/
// 94-assembler.md §8, "floating point as uninterpreted operations";
// docs/spec/125-verification.md §3). Addition, subtraction,
// multiplication, division, square root, fused multiply-add, the
// number-preferring minimum and maximum, the width and integer
// conversions, and the NaN a min/max yields are not bit operations the
// decider can blast — but the asm unit and its Oak body must apply the
// *same* IEEE operations to the *same* operands in the *same* order for
// the two to agree bit for bit on every input. So each is a term of its
// own kind (termFloat) that the witness evaluator computes as the IEEE
// operation (Go's float32/float64 arithmetic, round to nearest even, and
// an exactly rounded fma) and the bit-level decision treats as an
// uninterpreted function: equal operands give equal results, nothing
// else is assumed (Oak.Uninterpreted.ackermann_sound). A proof then says
// the unit is the body up to IEEE arithmetic itself, whose bit-level
// model is spec/lean/Oak/FloatOps.lean and whose agreement with the
// hardware the QEMU and Sail differentials check.
//
// The operation names are the AArch64 mnemonics the lane emits; the RV64
// lane's mnemonics map onto the same names (fadd.s → fadd at width 32).
// Widths distinguish f32 from f64; a conversion's source width is its
// operand's.

// floatOps are the operations and their operand counts.
var floatOps = map[string]int{
	"fadd": 2, "fsub": 2, "fmul": 2, "fdiv": 2, "fsqrt": 1, "fma": 3,
	"fminnm": 2, "fmaxnm": 2,
	// fnan is the NaN a min or max yields when an operand is NaN: some
	// NaN whose payload the platform chooses (docs/spec/20-types.md
	// §11.3.5), one function of the operands on both sides.
	"fnan": 2,
	// Conversions: fcvt changes the float width (operand width to the
	// term's), scvtf/ucvtf make a float from a signed/unsigned integer of
	// the operand's width, fcvtzs/fcvtzu make an integer of the term's
	// width from a float, toward zero, saturating, NaN to zero.
	"fcvt": 1, "scvtf": 1, "ucvtf": 1, "fcvtzs": 1, "fcvtzu": 1,
}

// floatTerm builds a floating-point operation term at width over args,
// folding it when every operand is a constant.
func floatTerm(op string, width int, args ...*term) *term {
	arity, known := floatOps[op]
	if !known || len(args) != arity {
		panic(fmt.Sprintf("floatTerm: %s over %d operands", op, len(args)))
	}
	t := &term{kind: termFloat, op: op, width: width, left: args[0]}
	if len(args) > 1 {
		t.right = args[1]
	}
	if len(args) > 2 {
		t.cond = args[2]
	}
	constant := true
	values := make([]uint64, len(args))
	widths := make([]int, len(args))
	for i, arg := range args {
		if arg.kind != termConst {
			constant = false
			break
		}
		values[i] = arg.value & mask(arg.width)
		widths[i] = arg.width
	}
	if constant {
		return constTerm(floatEval(op, width, values, widths)&mask(width), width)
	}
	return t
}

// floatOpSpan names the uninterpreted function the blaster abstracts an
// operation as: the operation at its width (its operands' widths are in
// the index bits).
func floatOpSpan(op string, width int) string { return fmt.Sprintf("float:%s:%d", op, width) }

// floatEval computes the IEEE operation on bit patterns at the operands'
// widths (a float operand's width is its format; a conversion's integer
// operand its integer width, which fixes the sign extension). NaN operands
// follow Arm's FPProcessNaNs (Arm ARM J1.3, shared by the C backend's
// arithmetic on AArch64): a signaling NaN operand wins over a quiet one,
// earlier operands over later, the result quieted; a fused multiply-add
// orders the addend before the multiplicands. The evaluation is written
// out rather than left to Go's `+`, whose operand order the compiler may
// swap (the payload a NaN result carries is exactly what the silicon
// differential checks).
func floatEval(op string, width int, args []uint64, widths []int) uint64 {
	f := func(v uint64, w int) float64 {
		if w == 32 {
			return float64(math.Float32frombits(uint32(v)))
		}
		return math.Float64frombits(v)
	}
	bits := func(x float64) uint64 {
		if width == 32 {
			return uint64(math.Float32bits(float32(x)))
		}
		return math.Float64bits(x)
	}
	switch op {
	case "fadd", "fsub", "fmul", "fdiv", "fnan":
		if nan, isNaN := armNaN(width, args[0], args[1]); isNaN {
			return nan
		}
		if width == 32 {
			a, b := math.Float32frombits(uint32(args[0])), math.Float32frombits(uint32(args[1]))
			var r float32
			switch op {
			case "fadd", "fnan":
				r = a + b
			case "fsub":
				r = a - b
			case "fmul":
				r = a * b
			case "fdiv":
				r = a / b
			}
			return canonicalNaN(uint64(math.Float32bits(r)), 32)
		}
		a, b := math.Float64frombits(args[0]), math.Float64frombits(args[1])
		var r float64
		switch op {
		case "fadd", "fnan":
			r = a + b
		case "fsub":
			r = a - b
		case "fmul":
			r = a * b
		case "fdiv":
			r = a / b
		}
		return canonicalNaN(math.Float64bits(r), 64)
	case "fminnm", "fmaxnm":
		// IEEE 754-2008 minNum/maxNum (Arm FPMinNum/FPMaxNum, RISC-V
		// fmin/fmax): a quiet NaN beside a number yields the number; a
		// signaling NaN, or two NaNs, follow FPProcessNaNs; -0.0 orders
		// below +0.0.
		aNaN, bNaN := isNaNBits(args[0], width), isNaNBits(args[1], width)
		switch {
		case aNaN && !bNaN && !isSNaNBits(args[0], width):
			return args[1]
		case bNaN && !aNaN && !isSNaNBits(args[1], width):
			return args[0]
		}
		if nan, isNaN := armNaN(width, args[0], args[1]); isNaN {
			return nan
		}
		a, b := f(args[0], width), f(args[1], width)
		less := a < b || (a == b && math.Signbit(a) && !math.Signbit(b))
		if (op == "fminnm") == less {
			return args[0]
		}
		return args[1]
	case "fsqrt":
		if nan, isNaN := armNaN(width, args[0]); isNaN {
			return nan
		}
		// Rounding the double-precision root to single is the correctly
		// rounded single root (the double has more than 2p+2 bits).
		return canonicalNaN(bits(math.Sqrt(f(args[0], width))), width)
	case "fma":
		// The addend is examined first (FPProcessNaNs3 on addend, op1, op2).
		if nan, isNaN := armNaN(width, args[2], args[0], args[1]); isNaN {
			return nan
		}
		if width == 32 {
			return canonicalNaN(uint64(math.Float32bits(fma32(math.Float32frombits(uint32(args[0])), math.Float32frombits(uint32(args[1])), math.Float32frombits(uint32(args[2]))))), 32)
		}
		return canonicalNaN(math.Float64bits(math.FMA(math.Float64frombits(args[0]), math.Float64frombits(args[1]), math.Float64frombits(args[2]))), 64)
	case "fcvt":
		return bits(f(args[0], widths[0]))
	case "scvtf":
		v := args[0]
		shift := uint(64 - widths[0])
		return bits(float64(int64(v<<shift) >> shift))
	case "ucvtf":
		return bits(float64(args[0]))
	case "fcvtzs", "fcvtzu":
		return convertToInt(f(args[0], widths[0]), width, op == "fcvtzs")
	}
	return 0
}

// isNaNBits and isSNaNBits classify a w-bit pattern; quietBits sets the
// quiet bit (the top mantissa bit).
func isNaNBits(v uint64, w int) bool {
	_, _, exponent, mantissa := floatMasks(w)
	return v&exponent == exponent && v&mantissa != 0
}

func isSNaNBits(v uint64, w int) bool {
	if !isNaNBits(v, w) {
		return false
	}
	_, _, _, mantissa := floatMasks(w)
	quiet := (mantissa + 1) >> 1
	return v&quiet == 0
}

func quietBits(v uint64, w int) uint64 {
	_, _, _, mantissa := floatMasks(w)
	return v | (mantissa+1)>>1
}

// armNaN is FPProcessNaNs over the operands in priority order: the first
// signaling NaN, else the first quiet NaN, quieted; false when no operand
// is a NaN.
func armNaN(w int, ops ...uint64) (uint64, bool) {
	for _, v := range ops {
		if isSNaNBits(v, w) {
			return quietBits(v, w), true
		}
	}
	for _, v := range ops {
		if isNaNBits(v, w) {
			return v, true
		}
	}
	return 0, false
}

// canonicalNaN is the default NaN an invalid operation over numbers
// produces (Arm's FPDefaultNaN: positive, quiet, zero payload); a number
// passes through.
func canonicalNaN(v uint64, w int) uint64 {
	if !isNaNBits(v, w) {
		return v
	}
	_, _, exponent, mantissa := floatMasks(w)
	return exponent | (mantissa+1)>>1
}

// fma32 is a*b + c rounded once to f32 (round to nearest even): the exact
// value is formed in a big.Float wide enough to hold it and rounded to the
// nearest single — subnormals at their coarser grid included (a fixed
// 24-bit precision would not). The callers have handled NaN operands;
// infinite ones follow the double fma.
func fma32(a, b, c float32) float32 {
	if math.IsInf(float64(a), 0) || math.IsInf(float64(b), 0) || math.IsInf(float64(c), 0) {
		return float32(math.FMA(float64(a), float64(b), float64(c)))
	}
	exact := new(big.Float).SetPrec(256).SetFloat64(float64(a))
	exact.Mul(exact, new(big.Float).SetPrec(256).SetFloat64(float64(b)))
	exact.Add(exact, new(big.Float).SetPrec(256).SetFloat64(float64(c)))
	if exact.Sign() == 0 {
		// An exact zero: the sign is the IEEE sum's (a*b and c of opposite
		// signs give +0 under round to nearest; equal signs keep it).
		return float32(math.FMA(float64(a), float64(b), float64(c)))
	}
	f, _ := exact.SetMode(big.ToNearestEven).Float32()
	return f
}

// convertToInt is fcvtzs/fcvtzu: toward zero, saturating at the integer
// range, NaN to zero (the same rule the backends' conversions follow).
func convertToInt(x float64, width int, signed bool) uint64 {
	if math.IsNaN(x) {
		return 0
	}
	x = math.Trunc(x)
	if signed {
		lo, hi := -math.Ldexp(1, width-1), math.Ldexp(1, width-1)-1
		switch {
		case x <= lo:
			return uint64(int64(-1)<<uint(width-1)) & mask(width)
		case x >= hi:
			return (uint64(1) << uint(width-1)) - 1
		}
		return uint64(int64(x)) & mask(width)
	}
	if x <= 0 {
		return 0
	}
	if x >= math.Ldexp(1, width) {
		return mask(width)
	}
	return uint64(x) & mask(width)
}
