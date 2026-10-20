package typechecker

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func TestInterfaceContractRejectsUnsupportedFacts(t *testing.T) {
	cases := []struct{ name, source, diagnostic string }{
		{"generic", "I[T]: interface = fn (self) m(x: T) -> T", "generic interface contracts are not supported yet"},
		{"generic_unused", "I[T: Missing]: interface = fn (self) m(x: i32) -> i32", "generic interface contracts are not supported yet"},
		{"typed_receiver", "I: interface = fn (self: i32) m(x: i32) -> i32", "typed interface receivers are not supported yet"},
		{"variadic", "I: interface = fn (self) m(xs: ...i32) -> i32", "variadic interface methods are not supported yet"},
	}
	for _, tt := range cases {
		t.Run(tt.name, func(t *testing.T) {
			p := parser.New(scanner.New(tt.source))
			program := p.ParseProgram()
			if len(p.Errors()) != 0 {
				t.Fatalf("parser must retain unsupported contract: %v", p.Errors())
			}
			tc := setupTypeChecker(tt.source)
			tc.CheckProgram(program)
			if !strings.Contains(strings.Join(tc.Errors(), "\n"), tt.diagnostic) {
				t.Fatalf("want %q, got %v", tt.diagnostic, tc.Errors())
			}
			if _, ok := tc.env.GetType("I"); ok {
				t.Fatal("unsupported interface registered with weakened contract")
			}
		})
	}
}
