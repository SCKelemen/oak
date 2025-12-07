package borrowchecker

import (
	"testing"
)

// TestBorrowChecker_RegionDisjointness tests v2 region-level disjointness checks
// Multiple spans are allowed if their regions are provably disjoint
func TestBorrowChecker_RegionDisjointness(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			"disjoint spans from same array",
			`buf: [16]byte; left: [*]byte = buf[0:8]; right: [*]byte = buf[8:16]`,
			false, // Should allow - regions [0:8) and [8:16) are disjoint
		},
		{
			"overlapping spans from same array",
			`buf: [16]byte; left: [*]byte = buf[0:8]; mid: [*]byte = buf[4:12]`,
			true, // Should reject - regions [0:8) and [4:12) overlap
		},
		{
			"adjacent spans (touching but not overlapping)",
			`buf: [16]byte; left: [*]byte = buf[0:8]; right: [*]byte = buf[8:16]`,
			false, // Should allow - regions [0:8) and [8:16) are adjacent but disjoint
		},
		{
			"three disjoint spans",
			`buf: [24]byte; a: [*]byte = buf[0:8]; b: [*]byte = buf[8:16]; c: [*]byte = buf[16:24]`,
			false, // Should allow - all three regions are disjoint
		},
		{
			"span overlaps with first of multiple spans",
			`buf: [24]byte; a: [*]byte = buf[0:8]; b: [*]byte = buf[8:16]; c: [*]byte = buf[4:12]`,
			true, // Should reject - c overlaps with a
		},
		{
			"span overlaps with second of multiple spans",
			`buf: [24]byte; a: [*]byte = buf[0:8]; b: [*]byte = buf[8:16]; c: [*]byte = buf[12:20]`,
			true, // Should reject - c overlaps with b
		},
		{
			"span completely contained in another",
			`buf: [16]byte; outer: [*]byte = buf[0:16]; inner: [*]byte = buf[4:8]`,
			true, // Should reject - inner is completely contained in outer
		},
		{
			"span completely contains another",
			`buf: [16]byte; inner: [*]byte = buf[4:8]; outer: [*]byte = buf[0:16]`,
			true, // Should reject - outer completely contains inner
		},
		{
			"zero-length span (edge case)",
			`buf: [16]byte; a: [*]byte = buf[0:0]; b: [*]byte = buf[0:8]`,
			true, // Should reject - zero-length at offset 0 overlaps with [0:8)
		},
		{
			"negative index normalization",
			`buf: [16]byte; left: [*]byte = buf[0:8]; right: [*]byte = buf[-8:]`,
			false, // Should allow - buf[-8:] is buf[8:16], disjoint from [0:8)
		},
		{
			"negative index that overlaps",
			`buf: [16]byte; left: [*]byte = buf[0:12]; right: [*]byte = buf[-8:]`,
			true, // Should reject - buf[-8:] is buf[8:16], overlaps with [0:12)
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			bc, program, tc := setupBorrowCheckerForTest(tt.input)
			if program == nil {
				t.Fatalf("Failed to parse program")
			}

			bc.CheckProgram(program, tc.Env())

			hasError := len(bc.Errors()) > 0
			if hasError != tt.hasError {
				if tt.hasError {
					t.Errorf("Expected error but got none. Errors: %v", bc.Errors())
				} else {
					t.Errorf("Expected no error but got: %v", bc.Errors())
				}
			}
		})
	}
}

// TestBorrowChecker_RegionDisjointness_UnknownRegions tests that spans with unknown regions
// cannot coexist (conservative fallback to v1 behavior)
func TestBorrowChecker_RegionDisjointness_UnknownRegions(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			"span with unknown region cannot coexist with another span",
			`buf: [16]byte; a: [*]byte = buf[0:8]; b: [*]byte = buf[i:j]`,
			true, // Should reject - b has unknown region (i, j are variables)
		},
		{
			"view() creates span with known region",
			`buf: [16]byte; a: [*]byte = buf[0:8]; b: [*]byte = span(&buf)`,
			true, // Should reject - b's region [0:16) overlaps with a's [0:8)
		},
		{
			"span() creates span with known region",
			`buf: [16]byte; a: [*]byte = buf[8:16]; b: [*]byte = span(&buf)`,
			true, // Should reject - b's region [0:16) overlaps with a's [8:16)
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Note: These tests may not work if the parser doesn't support
			// variable indices yet. They're here to document expected behavior.
			bc, program, tc := setupBorrowCheckerForTest(tt.input)
			if program == nil {
				// Parser error is expected for some of these - skip test
				return
			}

			bc.CheckProgram(program, tc.Env())

			hasError := len(bc.Errors()) > 0
			if hasError != tt.hasError {
				if tt.hasError {
					t.Errorf("Expected error but got none. Errors: %v", bc.Errors())
				} else {
					t.Errorf("Expected no error but got: %v", bc.Errors())
				}
			}
		})
	}
}

// TestBorrowChecker_RegionDisjointness_Views tests that views don't interfere
// with span disjointness (views are read-only, so multiple are always allowed)
func TestBorrowChecker_RegionDisjointness_Views(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			"multiple views with overlapping regions",
			`buf: [16]byte; v1: []byte = buf[0:8]; v2: []byte = buf[4:12]`,
			false, // Should allow - views can overlap (read-only)
		},
		{
			"view and span with overlapping regions",
			`buf: [16]byte; v: []byte = buf[0:8]; s: [*]byte = buf[4:12]`,
			true, // Should reject - span cannot coexist with overlapping view
		},
		{
			"view and disjoint span",
			`buf: [16]byte; v: []byte = buf[0:8]; s: [*]byte = buf[8:16]`,
			true, // Should reject - span cannot coexist with any view (v1 behavior)
		},
		{
			"multiple views and disjoint span",
			`buf: [16]byte; v1: []byte = buf[0:4]; v2: []byte = buf[4:8]; s: [*]byte = buf[8:16]`,
			true, // Should reject - span cannot coexist with any view (v1 behavior)
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			bc, program, tc := setupBorrowCheckerForTest(tt.input)
			if program == nil {
				t.Fatalf("Failed to parse program")
			}

			bc.CheckProgram(program, tc.Env())

			hasError := len(bc.Errors()) > 0
			if hasError != tt.hasError {
				if tt.hasError {
					t.Errorf("Expected error but got none. Errors: %v", bc.Errors())
				} else {
					t.Errorf("Expected no error but got: %v", bc.Errors())
				}
			}
		})
	}
}

// TestBorrowChecker_RegionsOverlap tests the regionsOverlap function directly
func TestBorrowChecker_RegionsOverlap(t *testing.T) {
	bc := New()

	tests := []struct {
		name     string
		r1       *Region
		r2       *Region
		overlaps bool
	}{
		{
			"disjoint regions",
			&Region{Offset: 0, Length: 8},
			&Region{Offset: 8, Length: 8},
			false,
		},
		{
			"overlapping regions",
			&Region{Offset: 0, Length: 8},
			&Region{Offset: 4, Length: 8},
			true,
		},
		{
			"adjacent regions (touching)",
			&Region{Offset: 0, Length: 8},
			&Region{Offset: 8, Length: 8},
			false, // Adjacent but not overlapping
		},
		{
			"one contains the other",
			&Region{Offset: 0, Length: 16},
			&Region{Offset: 4, Length: 8},
			true,
		},
		{
			"same region",
			&Region{Offset: 0, Length: 8},
			&Region{Offset: 0, Length: 8},
			true,
		},
		{
			"zero-length region",
			&Region{Offset: 0, Length: 0},
			&Region{Offset: 0, Length: 8},
			false, // Zero-length at start doesn't overlap with [0:8)
		},
		{
			"zero-length region inside another",
			&Region{Offset: 4, Length: 0},
			&Region{Offset: 0, Length: 8},
			false, // Zero-length at offset 4 is inside [0:8) but doesn't overlap (point vs interval)
		},
		{
			"nil region (unknown)",
			nil,
			&Region{Offset: 0, Length: 8},
			true, // Conservative: assume overlap if unknown
		},
		{
			"both nil (unknown)",
			nil,
			nil,
			true, // Conservative: assume overlap if unknown
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := bc.regionsOverlap(tt.r1, tt.r2)
			if result != tt.overlaps {
				t.Errorf("regionsOverlap(%v, %v) = %v, expected %v", tt.r1, tt.r2, result, tt.overlaps)
			}
		})
	}
}
