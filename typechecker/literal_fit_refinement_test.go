package typechecker

import (
	"math"
	"math/big"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
)

// The literal range decision — literalFitsInType, literalFits, and
// machineSizedName — is transliterated in
// spec/lean/Oak/LiteralFitRefinement.lean, where it is proved to accept
// exactly the literals whose value the type represents
// (docs/spec/25-type-inference.md §3a; the ranges are 20-types.md §11, the
// machine-sized types at the configured data model's width). That proof is
// about the transliteration; this test pins the Go decision to the module's
// table (`lo`/`hi`) at every range boundary, under each data model the
// checker can be configured with, through the parser's encoding of each
// value (`denotes`): plain, wide, or negated.
func TestLiteralFitMatchesLeanTable(t *testing.T) {
	pow := func(n uint) *big.Int { return new(big.Int).Lsh(big.NewInt(1), n) }
	one := big.NewInt(1)
	type bounds struct{ lo, hi *big.Int }
	unsigned := func(bits uint) bounds { return bounds{big.NewInt(0), new(big.Int).Sub(pow(bits), one)} }
	signed := func(bits uint) bounds {
		return bounds{new(big.Int).Neg(pow(bits - 1)), new(big.Int).Sub(pow(bits-1), one)}
	}
	table := func(intSize, ptrSize uint) map[string]bounds {
		return map[string]bounds{
			"u8": unsigned(8), "byte": unsigned(8), "u16": unsigned(16),
			"u32": unsigned(32), "rune": unsigned(32), "u64": unsigned(64), "u128": unsigned(128),
			"i8": signed(8), "i16": signed(16), "i32": signed(32), "i64": signed(64),
			"int": signed(intSize), "uint": unsigned(intSize),
			"ptr": signed(ptrSize), "uptr": unsigned(ptrSize),
		}
	}

	// The literals a program can spell: magnitudes below 2^64, so values in
	// [-(2^63 - 1), 2^64 - 1] (the negated wide magnitude is rejected before
	// the fit check; min_int64_lost names what that costs).
	minSpellable := new(big.Int).Neg(new(big.Int).Sub(pow(63), one))
	maxSpellable := new(big.Int).Sub(pow(64), one)
	// decide routes a value the way the checker does: a negative value through
	// the negated-literal rule on its magnitude, a value above 2^63 - 1 as a
	// wide literal carrying its bit pattern, anything else as a plain literal.
	decide := func(tc *TypeChecker, n *big.Int, typeName string) bool {
		switch {
		case n.Sign() < 0:
			return tc.literalFitsInType(n.Int64(), typeName)
		case n.IsInt64():
			return tc.literalFits(&ast.IntegerLiteral{Value: n.Int64()}, typeName)
		default:
			return tc.literalFits(&ast.IntegerLiteral{Wide: true, Value: int64(n.Uint64())}, typeName)
		}
	}

	for _, sizes := range [][2]uint{{64, 64}, {32, 32}, {32, 64}, {64, 32}} {
		tc := NewWithPlatformSizes(object.NewEnvironment(), int(sizes[0]), int(sizes[1]))
		for typeName, b := range table(sizes[0], sizes[1]) {
			probes := []*big.Int{
				new(big.Int).Sub(b.lo, one), b.lo, b.hi, new(big.Int).Add(b.hi, one),
				big.NewInt(-1), big.NewInt(0), big.NewInt(math.MaxInt64), new(big.Int).Lsh(one, 63),
			}
			for _, n := range probes {
				if n.Cmp(minSpellable) < 0 || n.Cmp(maxSpellable) > 0 {
					continue
				}
				want := n.Cmp(b.lo) >= 0 && n.Cmp(b.hi) <= 0
				if got := decide(tc, n, typeName); got != want {
					t.Errorf("int=%d ptr=%d: literal %s fits %s = %v, the range [%s, %s] says %v",
						sizes[0], sizes[1], n, typeName, got, b.lo, b.hi, want)
				}
			}
		}
	}
}

// The decision through the checker: the machine-sized types range-check at
// the configured width (an ILP32 build used to admit `x: uint = 5000000000`
// and truncate it), wide literals reach `uint`/`uptr` only at 64 bits, and
// the negated wide magnitude is the one representable i64 that cannot be
// spelled.
func TestLiteralFitUnderDataModels(t *testing.T) {
	tests := []struct {
		name             string
		input            string
		intSize, ptrSize int
		wantError        string
	}{
		{"uint above 32 bits on ILP32", "x: uint = 5000000000", 32, 32, "literal 5000000000 does not fit in type uint"},
		{"uint above 32 bits on LP64 int", "x: uint = 5000000000", 32, 64, "literal 5000000000 does not fit in type uint"},
		{"uint at 64 bits", "x: uint = 5000000000", 64, 64, ""},
		{"int above 32 bits", "x: int = 5000000000", 32, 64, "literal 5000000000 does not fit in type int"},
		{"negated int above 32 bits", "x: int = -5000000000", 32, 64, "literal -5000000000 does not fit in type int"},
		{"int at its 32-bit bounds", "x: int = 2147483647\ny: int = -2147483648", 32, 64, ""},
		{"uptr follows the pointer width", "x: uptr = 5000000000", 32, 64, ""},
		{"uptr at 32 bits", "x: uptr = 5000000000", 64, 32, "literal 5000000000 does not fit in type uptr"},
		{"wide literal to uint at 64 bits", "x: uint = 18446744073709551615", 64, 64, ""},
		{"wide literal to uint at 32 bits", "x: uint = 18446744073709551615", 32, 64, "literal 18446744073709551615 does not fit in type uint"},
		{"wide literal to uptr at 64 bits", "x: uptr = 18446744073709551615", 32, 64, ""},
		{"wide literal to uptr at 32 bits", "x: uptr = 18446744073709551615", 64, 32, "literal 18446744073709551615 does not fit in type uptr"},
		{"wide literal to u128", "x: u128 = 18446744073709551615", 32, 32, ""},
		{"wide literal to i64", "x: i64 = 18446744073709551615", 64, 64, "does not fit in type i64"},
		{"most negative i64 is not spellable", "x: i64 = -9223372036854775808", 64, 64, "literal -9223372036854775808 does not fit in type i64"},
		{"next i64 is", "x: i64 = -9223372036854775807", 64, 64, ""},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			tc := setupTypeChecker(tt.input)
			tc.SetIntSize(tt.intSize)
			tc.SetPtrSize(tt.ptrSize)
			tc.CheckProgram(parseProgram(tt.input))
			errs := strings.Join(tc.Errors(), "\n")
			if tt.wantError == "" && errs != "" {
				t.Fatalf("unexpected errors: %s", errs)
			}
			if tt.wantError != "" && !strings.Contains(errs, tt.wantError) {
				t.Fatalf("errors %q do not mention %q", errs, tt.wantError)
			}
		})
	}
}
