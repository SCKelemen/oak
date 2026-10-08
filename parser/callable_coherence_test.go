package parser

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
	"strings"
	"testing"
)

func TestCallableFormsShareClauses(t *testing.T) {
	for _, suffix := range []string{
		"effects { } forbids { Memory.Allocate } = a",
		"forbids { } effects { } laws { associative } = a",
		"effects { } laws { associative } dispatch { sve: optimized } = a",
		"(kernel) effects { } = a",
	} {
		t.Run(suffix, func(t *testing.T) {
			parse := func(src string) *ast.FunctionStatement {
				t.Helper()
				p := New(scanner.New(src))
				tree := p.ParseProgram()
				if len(p.Errors()) != 0 {
					t.Fatalf("%s: %v", src, p.Errors())
				}
				return tree.Statements[0].(*ast.FunctionStatement)
			}
			canonical := parse("choose[T]: (a, b: T): T " + suffix)
			legacy := parse("fn [T] choose(a, b: T): T " + suffix)
			if canonical.String() != legacy.String() {
				t.Fatalf("forms differ:\n%s\n%s", canonical.String(), legacy.String())
			}
			round := parse(canonical.String())
			if round.String() != canonical.String() || len(round.TypeParams) != 1 || (round.Forbids == nil) != (canonical.Forbids == nil) {
				t.Fatalf("lost callable facts: %s", round.String())
			}
		})
	}
}

func TestCallableClauseErrorsAgree(t *testing.T) {
	for _, suffix := range []string{
		"effects { } effects { } = x",
		"forbids { } forbids { } = x",
		"laws { } = x",
		"dispatch { } = x",
		"(kernel) (kernel) = x",
	} {
		for _, header := range []string{"f: (x: u32): u32 ", "fn f(x: u32): u32 "} {
			p := New(scanner.New(header + suffix))
			p.ParseProgram()
			if len(p.Errors()) == 0 {
				t.Fatalf("accepted %s%s", header, suffix)
			}
		}
	}
}

func TestCompatibilityBareBodyAndReceiver(t *testing.T) {
	for _, src := range []string{"fn f(x: u32): u32 x", "fn f(x: u32): u32 (x + 1)", "fn f(kernel: u32): u32 (kernel)", "fn (self: Box) get(x: u32): u32 effects { } = x"} {
		p := New(scanner.New(src))
		tree := p.ParseProgram()
		if len(p.Errors()) != 0 {
			t.Fatalf("%s: %v", src, p.Errors())
		}
		fn := tree.Statements[0].(*ast.FunctionStatement)
		if strings.Contains(src, "self") && fn.Receiver == nil {
			t.Fatal("receiver was lost")
		}
	}
}

func TestCallablePrintingPreservesAttachment(t *testing.T) {
	for _, source := range []string{
		"pub identity[T]: (x: T): T effects { } forbids { } = x",
		"operator(+) add: (x, y: Vec): Vec laws { associative } = x",
		"export(\"oak_f\") pub f: (x: i32): i32 effects { } = x",
		"identity[T]: theorem (x: T) = true",
		"pub identity: theorem (x: u32) = true",
		"maker: (): ((u32) -> u32) effects { Host.Read } = body",
		"maker: (): ([](u32) -> u32) effects { Host.Read } = body",
		"maker: (): ([*](u32) -> u32) effects { Host.Read } = body",
		"maker: (): ((u32) -> u32 effects { }) effects { Host.Read } = body",
	} {
		t.Run(source, func(t *testing.T) {
			parse := func(src string) *ast.FunctionStatement {
				t.Helper()
				p := New(scanner.New(src))
				tree := p.ParseProgram()
				if len(p.Errors()) != 0 {
					t.Fatalf("%s: %v", src, p.Errors())
				}
				return tree.Statements[0].(*ast.FunctionStatement)
			}
			want := parse(source)
			got := parse(want.String())
			if got.Exported != want.Exported || got.Theorem != want.Theorem || got.Operator != want.Operator || got.ExportSymbol != want.ExportSymbol || len(got.TypeParams) != len(want.TypeParams) || got.EffectsDeclared != want.EffectsDeclared || (got.Forbids == nil) != (want.Forbids == nil) {
				t.Fatalf("lost facts: %s", want.String())
			}
			if wantType, ok := want.ReturnType.(*ast.FunctionTypeExpression); ok {
				gotType, ok := got.ReturnType.(*ast.FunctionTypeExpression)
				if !ok || gotType.EffectsDeclared != wantType.EffectsDeclared {
					t.Fatalf("effect row moved across callable boundary: %s", want.String())
				}
			}
			if got.String() != want.String() {
				t.Fatalf("unstable print: %s -> %s", want.String(), got.String())
			}
		})
	}
}

func TestCompatibilityClauseWordsRemainBareBodies(t *testing.T) {
	for _, name := range []string{"effects", "forbids", "laws", "dispatch"} {
		source := "fn f(" + name + ": u32): u32 " + name
		p := New(scanner.New(source))
		tree := p.ParseProgram()
		if len(p.Errors()) != 0 {
			t.Fatalf("%s: %v", source, p.Errors())
		}
		fn := tree.Statements[0].(*ast.FunctionStatement)
		if fn.Body == nil || fn.EffectsDeclared || fn.Forbids != nil || len(fn.Laws) != 0 || len(fn.Dispatch) != 0 {
			t.Fatalf("body mistaken for clause: %#v", fn)
		}
	}
}
