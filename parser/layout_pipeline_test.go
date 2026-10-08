package parser_test

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/compiler"
)

// Exercise the public front end, including its layout normalizer, rather than
// bypassing it with parser.New(scanner.New(...)). Interface signatures are
// definition-less; function literals in initializers own their own bodies.
func TestLayoutCallableBoundaryPublicPipeline(t *testing.T) {
	for name, test := range map[string]struct {
		source string
		count  int
	}{
		"canonical interface followed by declaration": {
			"Reader: interface = fn (self) read(buf: [*]u8) -> u32\nmain: (): i32 = 42", 2,
		},
		"interface signature followed by declaration": {
			"interface Reader: interface = fn (self) read(buf: [*]u8) -> u32\nmain: (): i32 = 42", 2,
		},
		"interface signature across comments": {
			"interface Reader: interface /* kind */ = // signature\n  fn (self) read(buf: [*]u8) -> u32\nmain: (): i32 = 42", 2,
		},
		"typed initializer block literal": {
			"main: (): i32 { f: (i32) -> i32 = fn (x: i32): i32 { x }\nf(42) }", 1,
		},
		"inferred initializer expression literal": {
			"main: (): i32 { f := fn (x: i32): i32 = x\nf(42) }", 1,
		},
		"typed initializer expression literal": {
			"main: (): i32 { f: (i32) -> i32 = fn (x: i32): i32 = x\nf(42) }", 1,
		},
		"initializer layout literal": {
			"main: (): i32\n  f := fn (x: i32): i32\n    x\n  f(42)\n", 1,
		},
	} {
		t.Run(name, func(t *testing.T) {
			tree, err := compiler.New().WithSource("layout-boundary.oak", test.source).Parse().Get()
			if err != nil {
				t.Fatal(err)
			}
			if len(tree.Root.Statements) != test.count {
				t.Fatalf("got %d top-level statements, want %d", len(tree.Root.Statements), test.count)
			}
			if test.count == 1 {
				fn := tree.Root.Statements[0].(*ast.FunctionStatement)
				body := fn.Body.(*ast.BlockExpression)
				if len(body.Block.Statements) != 2 {
					t.Fatalf("initializer or subsequent call escaped main: %s", tree.Root.String())
				}
			}
		})
	}
}
