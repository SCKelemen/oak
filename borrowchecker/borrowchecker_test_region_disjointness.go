package borrowchecker

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// TestRegionDisjointness_DisjointSpans tests that multiple spans with disjoint regions are allowed
func TestRegionDisjointness_DisjointSpans(t *testing.T) {
	// Test the region overlap logic directly
	bc := New()
	env := typechecker.NewTypeEnvironment()
	
	// Register the owner
	ownerScheme := &typechecker.TypeScheme{
		Type: &typechecker.ArrayType{
			ElementType: &typechecker.PrimitiveType{Name: "u8"},
			Length:      16,
			IsSlice:     false,
			IsSpan:      false,
		},
	}
	env.Set("buf", ownerScheme)
	
	// Create first span with region [0, 8)
	region1 := &Region{Offset: 0, Length: 8}
	bc.createSpanBorrowWithRegion("buf", "left", region1)
	
	// Create second span with region [8, 16) - should be allowed (disjoint)
	region2 := &Region{Offset: 8, Length: 8}
	bc.createSpanBorrowWithRegion("buf", "right", region2)
	
	if len(bc.Errors()) > 0 {
		t.Errorf("Expected no errors for disjoint spans, got: %v", bc.Errors())
	}
}

// TestRegionDisjointness_OverlappingSpans tests that overlapping spans are rejected
func TestRegionDisjointness_OverlappingSpans(t *testing.T) {
	bc := New()
	env := typechecker.NewTypeEnvironment()
	
	// Register the owner
	ownerScheme := &typechecker.TypeScheme{
		Type: &typechecker.ArrayType{
			ElementType: &typechecker.PrimitiveType{Name: "u8"},
			Length:      16,
			IsSlice:     false,
			IsSpan:      false,
		},
	}
	env.Set("buf", ownerScheme)
	
	// Create first span with region [0, 8)
	region1 := &Region{Offset: 0, Length: 8}
	bc.createSpanBorrowWithRegion("buf", "left", region1)
	
	// Create second span with region [4, 12) - should be rejected (overlaps)
	region2 := &Region{Offset: 4, Length: 8}
	bc.createSpanBorrowWithRegion("buf", "mid", region2)
	
	if len(bc.Errors()) == 0 {
		t.Error("Expected error for overlapping spans, got none")
	}
}

// TestRegionDisjointness_AdjacentSpans tests that adjacent (touching) spans are allowed
func TestRegionDisjointness_AdjacentSpans(t *testing.T) {
	bc := New()
	env := typechecker.NewTypeEnvironment()
	
	// Register the owner
	ownerScheme := &typechecker.TypeScheme{
		Type: &typechecker.ArrayType{
			ElementType: &typechecker.PrimitiveType{Name: "u8"},
			Length:      16,
			IsSlice:     false,
			IsSpan:      false,
		},
	}
	env.Set("buf", ownerScheme)
	
	// Create first span with region [0, 8)
	region1 := &Region{Offset: 0, Length: 8}
	bc.createSpanBorrowWithRegion("buf", "left", region1)
	
	// Create second span with region [8, 16) - adjacent, should be allowed
	region2 := &Region{Offset: 8, Length: 8}
	bc.createSpanBorrowWithRegion("buf", "right", region2)
	
	if len(bc.Errors()) > 0 {
		t.Errorf("Expected no errors for adjacent spans, got: %v", bc.Errors())
	}
}

// TestRegionDisjointness_UnknownRegion tests that spans with unknown regions fall back to v1 behavior
func TestRegionDisjointness_UnknownRegion(t *testing.T) {
	bc := New()
	env := typechecker.NewTypeEnvironment()
	
	// Register the owner
	ownerScheme := &typechecker.TypeScheme{
		Type: &typechecker.ArrayType{
			ElementType: &typechecker.PrimitiveType{Name: "u8"},
			Length:      16,
			IsSlice:     false,
			IsSpan:      false,
		},
	}
	env.Set("buf", ownerScheme)
	
	// Create first span with known region [0, 8)
	region1 := &Region{Offset: 0, Length: 8}
	bc.createSpanBorrowWithRegion("buf", "left", region1)
	
	// Create second span with unknown region (nil) - should be rejected (v1 behavior)
	bc.createSpanBorrowWithRegion("buf", "right", nil)
	
	if len(bc.Errors()) == 0 {
		t.Error("Expected error for second span with unknown region, got none")
	}
}

// TestRegionsOverlap tests the region overlap detection logic
func TestRegionsOverlap(t *testing.T) {
	tests := []struct {
		name     string
		r1       *Region
		r2       *Region
		overlaps bool
	}{
		{"disjoint: [0,8) and [8,16)", &Region{0, 8}, &Region{8, 8}, false},
		{"disjoint: [0,4) and [8,12)", &Region{0, 4}, &Region{8, 4}, false},
		{"overlapping: [0,8) and [4,12)", &Region{0, 8}, &Region{4, 8}, true},
		{"overlapping: [4,12) and [0,8)", &Region{4, 8}, &Region{0, 8}, true},
		{"contained: [0,16) contains [4,8)", &Region{0, 16}, &Region{4, 4}, true},
		{"adjacent: [0,8) and [8,16)", &Region{0, 8}, &Region{8, 8}, false},
		{"same: [0,8) and [0,8)", &Region{0, 8}, &Region{0, 8}, true},
		{"unknown r1", nil, &Region{8, 8}, true}, // Conservative: assume overlap
		{"unknown r2", &Region{0, 8}, nil, true}, // Conservative: assume overlap
		{"both unknown", nil, nil, true},          // Conservative: assume overlap
	}
	
	bc := New()
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := bc.regionsOverlap(tt.r1, tt.r2)
			if result != tt.overlaps {
				t.Errorf("regionsOverlap(%v, %v) = %v, expected %v", tt.r1, tt.r2, result, tt.overlaps)
			}
		})
	}
}

// TestExtractSliceRegion tests region extraction from slice expressions
func TestExtractSliceRegion(t *testing.T) {
	tests := []struct {
		name        string
		low         ast.Expression
		high        ast.Expression
		ownerLength int64
		wantRegion  *Region
		wantOk      bool
	}{
		{
			"constant bounds: [0:8]",
			&ast.IntegerLiteral{Value: 0},
			&ast.IntegerLiteral{Value: 8},
			16,
			&Region{Offset: 0, Length: 8},
			true,
		},
		{
			"default low: [:8]",
			nil,
			&ast.IntegerLiteral{Value: 8},
			16,
			&Region{Offset: 0, Length: 8},
			true,
		},
		{
			"default high: [8:]",
			&ast.IntegerLiteral{Value: 8},
			nil,
			16,
			&Region{Offset: 8, Length: 8},
			true,
		},
		{
			"negative index: [-8:]",
			&ast.IntegerLiteral{Value: -8},
			nil,
			16,
			&Region{Offset: 8, Length: 8},
			true,
		},
		{
			"negative both: [-16:-8]",
			&ast.IntegerLiteral{Value: -16},
			&ast.IntegerLiteral{Value: -8},
			16,
			&Region{Offset: 0, Length: 8},
			true,
		},
		{
			"non-constant low",
			&ast.Identifier{Value: "i"},
			&ast.IntegerLiteral{Value: 8},
			16,
			nil,
			false,
		},
		{
			"non-constant high",
			&ast.IntegerLiteral{Value: 0},
			&ast.Identifier{Value: "j"},
			16,
			nil,
			false,
		},
	}
	
	bc := New()
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			slice := &ast.SliceExpression{
				Seq:  &ast.Identifier{Value: "arr"},
				Low:  tt.low,
				High: tt.high,
			}
			gotRegion, gotOk := bc.extractSliceRegion(slice, tt.ownerLength)
			if gotOk != tt.wantOk {
				t.Errorf("extractSliceRegion() ok = %v, want %v", gotOk, tt.wantOk)
				return
			}
			if gotOk && (gotRegion == nil || gotRegion.Offset != tt.wantRegion.Offset || gotRegion.Length != tt.wantRegion.Length) {
				t.Errorf("extractSliceRegion() region = %v, want %v", gotRegion, tt.wantRegion)
			}
		})
	}
}
