package parser

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
	"strings"
	"testing"
)

func TestKernelDeclarationClause(t *testing.T) {
	for _, source := range []string{
		"touch: (gid: u32): () (kernel) = {}",
		"touch[R]: (gid: u32, xs: Tensor[R]): () (kernel) = {}",
		"touch[R, S]: (gid: u32, xs: Tensor[R, S], ys: []u32, zs: [* align 16]u32, a: [4]u32): () (kernel) = {}",
		"touch: (gid: u32): () (kernel) effects { } forbids { Memory.Allocate } = {}",
		"pub touch: (gid: u32): () (kernel) = {}",
		"touch: (gid: u32): () (kernel)",
	} {
		t.Run(source, func(t *testing.T) {
			p := New(scanner.New(source))
			tree := p.ParseProgram()
			if len(p.Errors()) != 0 {
				t.Fatalf("parse: %v", p.Errors())
			}
			fn, ok := tree.Statements[0].(*ast.FunctionStatement)
			if !ok || !fn.Kernel {
				t.Fatalf("want kernel, got %#v", tree.Statements[0])
			}
			printed := fn.String()
			if !strings.Contains(printed, " (kernel)") || strings.HasPrefix(printed, "kernel ") {
				t.Fatalf("printer: %s", printed)
			}
			q := New(scanner.New(printed))
			round := q.ParseProgram()
			if len(q.Errors()) != 0 {
				t.Fatalf("reparse %s: %v", printed, q.Errors())
			}
			got := round.Statements[0].(*ast.FunctionStatement)
			if got.Exported != fn.Exported || got.Opaque != fn.Opaque || !got.Kernel || len(got.TypeParams) != len(fn.TypeParams) || got.EffectsDeclared != fn.EffectsDeclared || len(got.Forbids) != len(fn.Forbids) {
				t.Fatalf("lost callable metadata: %s", printed)
			}
			if got.String() != printed {
				t.Fatalf("unstable print: %s -> %s", printed, got.String())
			}
		})
	}
}

func TestKernelDeclarationClauseRejectsInvalidForms(t *testing.T) {
	for _, test := range []struct{ source, want string }{
		{"kernel touch: (gid: u32): () = {}", "move kernel after the signature"},
		{"touch: (gid: u32): () (kernel) (kernel) = {}", "one (kernel) clause"},
		{"touch: (gid: u32): () (device) = {}", "clause after a callable signature is (kernel)"},
		{"touch: (gid: u32): () (kernel, kernel) = {}", "expected"},
		{"touch: (gid: u32): () (kernel", "expected"},
		{"value: u32 (kernel) = 0", "clause after a declaration's type"},
	} {
		t.Run(test.source, func(t *testing.T) {
			p := New(scanner.New(test.source))
			p.ParseProgram()
			if !strings.Contains(strings.Join(p.Errors(), "\n"), test.want) {
				t.Fatalf("want %q, got %v", test.want, p.Errors())
			}
		})
	}
}

func TestKernelStaysContextual(t *testing.T) {
	p := New(scanner.New("kernel: u32 = 1\nother := kernel\nkernel_fn: (kernel: u32): u32 = kernel"))
	p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatalf("kernel is an ordinary identifier: %v", p.Errors())
	}
}
