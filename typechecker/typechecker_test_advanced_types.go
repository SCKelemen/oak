package typechecker

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// TestTypeChecker_AdvancedTypesSyntaxLockdown tests the entire types_advanced_positive.oak file
// through parse → typecheck to lock down the syntax and ensure design intent is preserved.
// This test serves as a syntax regression test for the type system - any syntax changes that
// break the design intent will fail this test.
//
// For the full pipeline test (parse → typecheck → borrowcheck), see:
// borrowchecker.TestBorrowChecker_AdvancedTypesSyntaxLockdown
//
// This test covers:
// - Generics (fn replicate4[T], fn as_view4[T], etc.)
// - Fixed arrays ([4]T), views ([]T), and spans ([*]T)
// - Phantom types (Id[T], Slice[T, Tag])
// - Constraints/interfaces (Readable, Writable, fn id_readable[T: Readable])
// - Subtyping (Employee <: Person <: Named via intersection)
// - Sum/intersection lattice types (Color, PrimaryColor, NamedColored, etc.)
// - Pattern matching on ADTs (Option, Result)
func TestTypeChecker_AdvancedTypesSyntaxLockdown(t *testing.T) {
	// Read the test file
	wd, _ := os.Getwd()
	testFile := filepath.Join(wd, "testdata", "types_advanced_positive.oak")
	if _, err := os.Stat(testFile); os.IsNotExist(err) {
		// Try relative to package
		testFile = filepath.Join("typechecker", "testdata", "types_advanced_positive.oak")
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
		program := parseProgram(code)

		if program == nil {
			t.Fatal("Parser returned nil program")
		}

		t.Logf("Parse: ✓ (%d statements)", len(program.Statements))
	})

	// Phase 2: Typecheck
	t.Run("typecheck", func(t *testing.T) {
		program := parseProgram(code)
		if program == nil {
			t.Fatal("Parser returned nil program")
		}

		typeChecker := setupTypeChecker(code)
		typeChecker.CheckProgram(program)

		errors := typeChecker.Errors()
		if len(errors) > 0 {
			t.Errorf("Typecheck errors (type system broken):\n%s", strings.Join(errors, "\n"))
			return
		}

		t.Logf("Typecheck: ✓")
	})

	// Combined test: parse + typecheck together
	t.Run("parse_and_typecheck", func(t *testing.T) {
		program := parseProgram(code)
		if program == nil {
			t.Fatal("Parser returned nil program")
		}

		typeChecker := setupTypeChecker(code)
		typeChecker.CheckProgram(program)

		errors := typeChecker.Errors()
		if len(errors) > 0 {
			t.Fatalf("Typecheck errors: %v", errors)
		}

		t.Logf("Parse + Typecheck: ✓")
	})
}
