package borrowchecker

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

// TestBorrowChecker_AdvancedTypesSyntaxLockdown tests the entire types_advanced_positive.oak file
// through parse → typecheck → borrowcheck to lock down the syntax and ensure design intent
// is preserved. This test serves as a syntax regression test - any syntax changes that break
// the design intent will fail this test.
//
// This test covers:
// - Generics (fn replicate4[T], fn as_view4[T], etc.)
// - Fixed arrays ([4]T), views ([]T), and spans ([*]T)
// - Phantom types (Id[T], Slice[T, Tag])
// - Constraints/interfaces (Readable, Writable, fn id_readable[T: Readable])
// - Subtyping (Employee <: Person <: Named via intersection)
// - Sum/intersection lattice types (Color, PrimaryColor, NamedColored, etc.)
// - Pattern matching on ADTs (Option, Result)
func TestBorrowChecker_AdvancedTypesSyntaxLockdown(t *testing.T) {
	// Read the test file from typechecker/testdata (shared location)
	wd, _ := os.Getwd()
	testFile := filepath.Join(wd, "..", "typechecker", "testdata", "types_advanced_positive.oak")
	if _, err := os.Stat(testFile); os.IsNotExist(err) {
		// Try alternative paths
		testFile = filepath.Join(wd, "typechecker", "testdata", "types_advanced_positive.oak")
		if _, err := os.Stat(testFile); os.IsNotExist(err) {
			testFile = filepath.Join("typechecker", "testdata", "types_advanced_positive.oak")
		}
	}

	content, err := os.ReadFile(testFile)
	if err != nil {
		t.Fatalf("Failed to read test file %s: %v (cwd: %s)", testFile, err, wd)
	}

	code := strings.TrimSpace(string(content))
	if code == "" {
		t.Fatalf("Test file %s is empty", testFile)
	}

	t.Logf("Testing syntax lockdown with %d bytes from %s", len(code), testFile)

	// Phase 1: Parse
	t.Run("parse", func(t *testing.T) {
		l := scanner.New(code)
		p := parser.New(l)
		program := p.ParseProgram()

		if len(p.Errors()) > 0 {
			t.Errorf("Parse errors (syntax broken):\n%s", strings.Join(p.Errors(), "\n"))
			return
		}

		if program == nil {
			t.Fatal("Parser returned nil program without errors")
		}

		t.Logf("Parse: ✓ (%d statements)", len(program.Statements))
	})

	// Phase 2: Typecheck
	t.Run("typecheck", func(t *testing.T) {
		l := scanner.New(code)
		p := parser.New(l)
		program := p.ParseProgram()

		if len(p.Errors()) > 0 {
			t.Fatalf("Parse errors: %v", p.Errors())
		}

		objEnv := object.NewEnvironment()
		tc := typechecker.New(objEnv)
		tc.CheckProgram(program)

		errors := tc.Errors()
		if len(errors) > 0 {
			t.Errorf("Typecheck errors (type system broken):\n%s", strings.Join(errors, "\n"))
			return
		}

		t.Logf("Typecheck: ✓")
	})

	// Phase 3: Borrow check
	t.Run("borrowcheck", func(t *testing.T) {
		l := scanner.New(code)
		p := parser.New(l)
		program := p.ParseProgram()

		if len(p.Errors()) > 0 {
			t.Fatalf("Parse errors: %v", p.Errors())
		}

		objEnv := object.NewEnvironment()
		tc := typechecker.New(objEnv)
		tc.CheckProgram(program)

		if len(tc.Errors()) > 0 {
			t.Fatalf("Typecheck errors: %v", tc.Errors())
		}

		bc := New()
		bc.CheckProgram(program, tc.Env())

		errors := bc.Errors()
		if len(errors) > 0 {
			t.Errorf("Borrow check errors (borrow semantics broken):\n%s", strings.Join(errors, "\n"))
			return
		}

		t.Logf("Borrowcheck: ✓")
	})

	// Combined test: all phases together
	t.Run("full_pipeline", func(t *testing.T) {
		// Parse
		l := scanner.New(code)
		p := parser.New(l)
		program := p.ParseProgram()

		if len(p.Errors()) > 0 {
			t.Fatalf("Parse errors: %v", p.Errors())
		}

		if program == nil {
			t.Fatal("Parser returned nil program")
		}

		// Typecheck
		objEnv := object.NewEnvironment()
		tc := typechecker.New(objEnv)
		tc.CheckProgram(program)

		if len(tc.Errors()) > 0 {
			t.Fatalf("Typecheck errors: %v", tc.Errors())
		}

		// Borrow check
		bc := New()
		bc.CheckProgram(program, tc.Env())

		if len(bc.Errors()) > 0 {
			t.Fatalf("Borrow check errors: %v", bc.Errors())
		}

		t.Logf("Full pipeline (parse → typecheck → borrowcheck): ✓")
	})
}
