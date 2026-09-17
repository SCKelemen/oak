package nativegen

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
)

func extentFoldExpression(op string, divisor int64) *ast.InfixExpression {
	return &ast.InfixExpression{Operator: op,
		Left:  &ast.InvocationExpression{Function: &ast.Identifier{Value: "len"}, Arguments: []ast.Expression{&ast.Identifier{Value: "v"}}},
		Right: &ast.InvocationExpression{Function: &ast.Identifier{Value: "u32"}, Arguments: []ast.Expression{&ast.IntegerLiteral{Value: divisor}}},
	}
}

func TestExtentQuotient(t *testing.T) {
	for _, n := range []int64{0, 1, 13, 4893, 4294967295} {
		g := generator{strength: true, spans: map[string]span{"v": {frameLen: n, array: &arrayLocal{length: n}}}}
		for _, d := range []int64{1, 2, 3, 7, 4294967295} {
			for _, op := range []string{"/", "%"} {
				want := uint64(n / d)
				if op == "%" {
					want = uint64(n % d)
				}
				if got, ok := g.extentQuotient(extentFoldExpression(op, d), scalars["u32"]); !ok || got != want {
					t.Fatalf("%d %s %d = %d, %v; want %d", n, op, d, got, ok, want)
				}
			}
		}
	}
}

func TestExtentQuotientRefusals(t *testing.T) {
	for name, mutate := range map[string]func(*generator, *ast.InfixExpression){
		"disabled":       func(g *generator, e *ast.InfixExpression) { g.strength = false },
		"dynamic span":   func(g *generator, e *ast.InfixExpression) { g.spans["v"] = span{} },
		"unknown name":   func(g *generator, e *ast.InfixExpression) { delete(g.spans, "v") },
		"missing origin": func(g *generator, e *ast.InfixExpression) { g.spans["v"] = span{frameLen: 13} },
		"mismatched extent": func(g *generator, e *ast.InfixExpression) {
			g.spans["v"] = span{frameLen: 2, array: &arrayLocal{length: 13}}
		},
		"negative extent": func(g *generator, e *ast.InfixExpression) {
			g.spans["v"] = span{frameLen: -1, array: &arrayLocal{length: -1}}
		},
		"wide extent": func(g *generator, e *ast.InfixExpression) {
			g.spans["v"] = span{frameLen: 1 << 32, array: &arrayLocal{length: 1 << 32}}
		},
		"zero divisor":     func(g *generator, e *ast.InfixExpression) { e.Right = &ast.IntegerLiteral{Value: 0} },
		"negative divisor": func(g *generator, e *ast.InfixExpression) { e.Right = &ast.IntegerLiteral{Value: -1} },
		"wide divisor":     func(g *generator, e *ast.InfixExpression) { e.Right = &ast.IntegerLiteral{Value: 1 << 32} },
		"other operator":   func(g *generator, e *ast.InfixExpression) { e.Operator = "+" },
		"narrow cast": func(g *generator, e *ast.InfixExpression) {
			e.Right.(*ast.InvocationExpression).Function = &ast.Identifier{Value: "u8"}
		},
		"nested cast": func(g *generator, e *ast.InfixExpression) {
			e.Right.(*ast.InvocationExpression).Arguments[0] = extentFoldExpression("/", 3).Right
		},
		"divisor call": func(g *generator, e *ast.InfixExpression) {
			e.Right = &ast.InvocationExpression{Function: &ast.Identifier{Value: "next"}}
		},
		"length call": func(g *generator, e *ast.InfixExpression) {
			e.Left.(*ast.InvocationExpression).Function = &ast.Identifier{Value: "next"}
		},
		"view expression": func(g *generator, e *ast.InfixExpression) {
			e.Left.(*ast.InvocationExpression).Arguments[0] = &ast.InvocationExpression{Function: &ast.Identifier{Value: "next"}}
		},
		"shadowed constant": func(g *generator, e *ast.InfixExpression) {
			e.Right = &ast.Identifier{Value: "D"}
			g.types = map[string]scalar{"D": scalars["u32"]}
		},
		"wrong constant type": func(g *generator, e *ast.InfixExpression) {
			e.Right = &ast.Identifier{Value: "D"}
			g.constants["D"] = asm.Constant{Type: "u64", Value: 3}
		},
	} {
		t.Run(name, func(t *testing.T) {
			g := generator{strength: true, spans: map[string]span{"v": {frameLen: 13, array: &arrayLocal{length: 13}}}, constants: map[string]asm.Constant{"D": {Type: "u32", Value: 3}}}
			e := extentFoldExpression("/", 3)
			mutate(&g, e)
			if got, ok := g.extentQuotient(e, scalars["u32"]); ok {
				t.Fatalf("unexpected fold to %d", got)
			}
		})
	}
	g := generator{strength: true, spans: map[string]span{"v": {frameLen: 13, array: &arrayLocal{length: 13}}}, constants: map[string]asm.Constant{"D": {Type: "u32", Value: 3}}}
	e := extentFoldExpression("/", 3)
	e.Right = &ast.Identifier{Value: "D"}
	if got, ok := g.extentQuotient(e, scalars["u32"]); !ok || got != 4 {
		t.Fatalf("constant divisor: %d, %v", got, ok)
	}
	for _, typ := range []string{"u8", "u16", "u64", "i32", "f32", "Bool"} {
		if _, ok := g.extentQuotient(e, scalars[typ]); ok {
			t.Fatalf("folded as %s", typ)
		}
	}
}

// A source-level power-of-two rewrite must not disable emitter folding on
// RV64. Check both the folded machine body and the unmodified source theorem.
func TestExtentQuotientNativeLanes(t *testing.T) {
	for _, arch := range []string{asm.ArchArm64, asm.ArchRV64} {
		for _, op := range []string{"/", "%"} {
			for _, strength := range []bool{false, true} {
				t.Run(fmt.Sprintf("%s/%s/%v", arch, op, strength), func(t *testing.T) {
					source := `extent: (x: u32): u32 {
  a: [13]u32
  whole: []u32 = view(&a)
  v: []u32 = whole
  n: u32 = len(v) ` + op + ` u32(3)
  n + x / u32(2)
}`
					fn, functions, _, tc := checkedFillFunction(t, source, "extent")
					body, err := CompileFor(Lane{Arch: arch, Strength: strength, NoReductions: true}, fn, functions, nil, nil, nil, tc)
					if err != nil {
						t.Fatal(err)
					}
					text := Describe(body)
					hasDivision := strings.Contains(text, "udiv ") || strings.Contains(text, "divu") || strings.Contains(text, "remu")
					if hasDivision == strength {
						t.Fatalf("Strength=%v, division=%v:\n%s", strength, hasDivision, text)
					}
					if strength && Reduced(body) == 0 {
						t.Fatal("emitter fold not reported")
					}
					if findings := asm.Check(body, fn, map[string]bool{"extent": true}); len(findings) != 0 {
						t.Fatalf("checker: %v\n%s", findings, text)
					}
					if v := asm.Verify(body, fn, fn.Body); v.Kind != asm.VerdictProven {
						t.Fatalf("verification: %s: %s\n%s", v.Kind, v.Message, text)
					}
				})
			}
		}
	}
}
