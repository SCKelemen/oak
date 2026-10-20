package main

import (
	"bytes"
	"context"
	"debug/elf"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/target"
)

func TestLRATNativeGuards(t *testing.T) {
	t.Setenv("OAK_VERIFY_ONLY", "")
	p := parser.New(layout.New(scanner.New(oakLRATSource)))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	specs := map[string]*ast.FunctionStatement{}
	for _, stmt := range program.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok {
			specs[fn.Name.Value] = fn
		}
	}
	for lane, source := range map[string]string{"arm64": oakLRATArm64Source, "rv64": oakLRATRV64Source} {
		t.Run(lane, func(t *testing.T) {
			path := "prove/solver/lrat." + lane + ".oakasm"
			unit, errs := asm.ParseUnit(path, source)
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			if len(unit.Functions) != 2 {
				t.Fatal("expected both scalar guards")
			}
			for _, fn := range unit.Functions {
				spec := specs[fn.Name]
				if spec == nil {
					t.Fatalf("no production definition: %s", fn.Name)
				}
				if findings := asm.Check(fn, spec, nil); len(findings) != 0 {
					t.Fatal(findings)
				}
				v := asm.Verify(fn, spec, spec.Body)
				if v.Kind != asm.VerdictProven {
					t.Fatalf("%s: %s: %s", fn.Name, v.Kind, v.Message)
				}
				t.Logf("%s: %s", fn.Name, v.Message)
			}
			// Wrong inclusive endpoint and wrong allocation threshold must
			// produce counterexamples, never merely an unproved verdict.
			mutations := [][2]string{{"cset w0, ls", "cset w0, lo"}, {"#1073741823", "#1073741824"}}
			if lane == "rv64" {
				mutations = [][2]string{{"sltu a0, t1, a1", "sltu a0, a1, t1"}, {"li t0, 1073741823", "li t0, 1073741824"}}
			}
			for _, mutation := range mutations {
				if !strings.Contains(source, mutation[0]) {
					t.Fatal("mutation site lost")
				}
				bad, errs := asm.ParseUnit(path, strings.Replace(source, mutation[0], mutation[1], 1))
				if len(errs) != 0 {
					t.Fatal(errs)
				}
				rejected := false
				for _, fn := range bad.Functions {
					spec := specs[fn.Name]
					if findings := asm.Check(fn, spec, nil); len(findings) != 0 {
						t.Fatal(findings)
					}
					v := asm.Verify(fn, spec, spec.Body)
					if v.Kind == asm.VerdictMismatch {
						rejected = true
					}
				}
				if !rejected {
					t.Fatalf("incorrect unit admitted: %v", mutation)
				}
			}

			if _, err := asm.EncodeFunctions(unit.Functions, func(s string) string { return s }); err != nil {
				t.Fatal(err)
			}
		})
	}
}

// Compile the complete production checker with both units and inspect each
// target's emitted C and real ELF companion object; no cross compiler needed.
func TestLRATNativeTargetSelection(t *testing.T) {
	t.Setenv("OAK_VERIFY_ONLY", "")
	for _, arch := range []string{target.ArchArm64, target.ArchRiscv64, target.ArchAmd64} {
		t.Run(string(arch), func(t *testing.T) {
			comp := compiler.New().WithSource("lrat.oak", oakLRATSource+"\nmain: (): i32 { lrat_alloc_fits(u32(0)) ? i32(0) | i32(1) }\n").
				WithAsmUnit("lrat.arm64.oakasm", oakLRATArm64Source).
				WithAsmUnit("lrat.rv64.oakasm", oakLRATRV64Source).
				WithTarget(target.Target{OS: target.OSLinux, Arch: arch})
			code, err := comp.EmitC().Get()
			if err != nil {
				t.Fatal(err)
			}
			if arch == target.ArchAmd64 {
				if strings.Contains(code, "cset w0") || strings.Contains(code, "sltu a0") {
					t.Fatal("foreign native lane leaked")
				}
				return
			}
			want, unwanted := "cset w0", "sltu a0"
			machine := elf.EM_AARCH64
			if arch == target.ArchRiscv64 {
				want, unwanted = unwanted, want
				machine = elf.EM_RISCV
			}
			if !strings.Contains(code, want) || strings.Contains(code, unwanted) {
				t.Fatal("wrong native lane selected")
			}
			object, err := comp.EmitAsmObject(asm.ELF).Get()
			if err != nil {
				t.Fatal(err)
			}
			f, err := elf.NewFile(bytes.NewReader(object))
			if err != nil {
				t.Fatal(err)
			}
			defer f.Close()
			if f.Machine != machine {
				t.Fatalf("wrong ELF machine: %v", f.Machine)
			}
			symbols, err := f.Symbols()
			if err != nil {
				t.Fatal(err)
			}
			for _, name := range []string{"oak_lrat_fits", "oak_lrat_alloc_fits"} {
				found := false
				for _, s := range symbols {
					if s.Name == name && s.Size > 0 {
						found = true
					}
				}
				if !found {
					t.Fatalf("missing encoded guard %s", name)
				}
			}
		})
	}
}

func TestLRATNativeLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_LRAT_BINDING_LEAN") != "" {
			t.Fatal("lake required for native guard proof")
		}
		t.Skip("lake unavailable")
	}
	contract := `import Oak.LRATNativeGuards
import Oak.LRATRV64Bytes
import Oak.LRATRV64Compressed
import Oak.LRATARM64Bytes
import Oak.LRATNativeRefinement
import Oak.LRATRV64GuardCalls
import Oak.LRATARM64GuardCalls
import Oak.LRATARM64RecordLoads
import Oak.LRATARM64HeaderLoads
import Oak.LRATRV64HeaderLoads
set_option pp.fullNames true
open Oak.LRATNativeGuards
example (a c l : UInt32) (fuel : Nat) :
    Oak.LRATBounds.lrat_fits a c l fuel = some (armFits a.toBitVec c.toBitVec l.toBitVec) := arm_fits_extracted a c l fuel
example (c : UInt32) (fuel : Nat) :
    Oak.LRATBounds.lrat_alloc_fits c fuel = some (armAlloc c.toBitVec) := arm_alloc_extracted c fuel
example (c : BitVec 64) (h : rvAlloc c = true) :
    ((c.truncate 32).toNat + 1) * 4 < 4294967296 := rv_alloc_sound c h
example (a c l : BitVec 64) (h : rvFits a c l = true) :
    (a.truncate 32).toNat + (c.truncate 32).toNat ≤ (l.truncate 32).toNat := rv_fits_sound a c l h
#print axioms Oak.LRATNativeGuards.arm_fits_extracted
#print axioms Oak.LRATNativeGuards.rv_fits_width
#print axioms Oak.LRATNativeGuards.arm_alloc_extracted
#print axioms Oak.LRATNativeGuards.rv_alloc_width
#print axioms Oak.LRATNativeGuards.arm_fits_sound
#print axioms Oak.LRATNativeGuards.rv_fits_sound
#print axioms Oak.LRATNativeGuards.arm_alloc_sound
#print axioms Oak.LRATNativeGuards.rv_alloc_sound
`
	contract += lratRV64ByteContract(t)
	contract += lratARM64ByteContract(t)
	contract += lratRV64CallContract(t)
	contract += lratARM64CallContract(t)
	for _, lane := range []string{"ARM64", "RV64", "RV64Compressed"} {
		for _, theorem := range []string{"fits_refines", "alloc_refines", "fits_accepted_iff", "alloc_accepted_iff", "fits_index", "allocation_safe"} {
			contract += "\n#print axioms Oak.LRATNativeRefinement." + lane + "." + theorem + "\n"
		}
	}
	path := filepath.Join(t.TempDir(), "NativeContract.lean")
	if err := os.WriteFile(path, []byte(contract), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 3*time.Minute)
	defer cancel()
	for _, args := range [][]string{{"build", "Oak.LRATNativeGuards", "Oak.LRATRV64Bytes", "Oak.LRATRV64Compressed", "Oak.LRATARM64Bytes", "Oak.LRATNativeRefinement", "Oak.LRATRV64GuardCalls", "Oak.LRATARM64GuardCalls", "Oak.LRATARM64RecordLoads", "Oak.LRATARM64HeaderLoads", "Oak.LRATRV64HeaderLoads"}, {"env", "lean", path}} {
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = filepath.Join("spec", "lean")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("native guard proof: %v\n%s", err, out)
		}
		if err := lratAuditNativeAxioms(string(out)); err != nil {
			t.Fatal(err)
		}
	}
}
