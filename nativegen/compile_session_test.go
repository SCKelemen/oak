package nativegen

import (
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

func TestCompileSessionMatchesStandaloneAcrossLatePasses(t *testing.T) {
	p := parser.New(layout.New(scanner.New("calc: (x: u32, y: u32, z: u32): u32 { a: u32 = x * y a + z }")))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	tc := typechecker.New(object.NewEnvironment())
	tc.CheckProgram(program)
	if errs := tc.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	fn := program.Statements[0].(*ast.FunctionStatement)
	functions := map[string]*ast.FunctionStatement{"calc": fn}
	for _, arch := range []string{asm.ArchArm64, asm.ArchRV64} {
		t.Run(arch, func(t *testing.T) {
			var session CompileSession
			plain := Lane{Arch: arch, NoReductions: true, Reallocate: true}
			scheduled, fused, carried := plain, plain, plain
			scheduled.Schedule = true
			fused.Fuse, fused.Schedule = true, true
			carried.CarryLoopIndices, carried.ElideRedundantGuards = true, true
			for i, lane := range []Lane{plain, scheduled, fused, carried, plain} {
				want, err := CompileFor(lane, fn, functions, nil, nil, nil, tc)
				if err != nil {
					t.Fatal(err)
				}
				got, err := session.CompileFor(lane, fn, functions, nil, nil, nil, tc)
				if err != nil {
					t.Fatal(err)
				}
				if !reflect.DeepEqual(got, want) || Reallocated(got) != Reallocated(want) || PromotedSlots(got) != PromotedSlots(want) || Scheduled(got) != Scheduled(want) || Fused(got) != Fused(want) {
					t.Fatalf("lane %d changed body or lowering counters\nwant %s\ngot %s", i, Describe(want), Describe(got))
				}
				if findings := asm.Check(got, fn, map[string]bool{"calc": true}); len(findings) != 0 {
					t.Fatalf("lane %d seam refused: %v", i, findings)
				}
				if verdict := asm.Verify(got, fn, fn.Body); verdict.Kind != asm.VerdictProven {
					t.Fatalf("lane %d did not prove: %s", i, verdict.Message)
				}
			}
			if stats := session.ReallocationStats(); stats.Requests != 5 || stats.Hits != 4 || stats.Entries != 1 {
				t.Fatalf("late passes did not share exactly one allocation input: %+v", stats)
			}
			var independent CompileSession
			if _, err := independent.CompileFor(plain, fn, functions, nil, nil, nil, tc); err != nil {
				t.Fatal(err)
			}
			if stats := independent.ReallocationStats(); stats.Hits != 0 || stats.Requests != 1 {
				t.Fatalf("allocation results leaked between sessions: %+v", stats)
			}
		})
	}
}
