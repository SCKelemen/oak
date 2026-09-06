package borrowchecker

import "testing"

func TestRegionsOverlapHalfOpenSemantics(t *testing.T) {
	bc := New()
	tests := []struct {
		name    string
		left    *Region
		right   *Region
		overlap bool
	}{
		{
			name:    "same region overlaps",
			left:    &Region{Offset: 0, Length: 8},
			right:   &Region{Offset: 0, Length: 8},
			overlap: true,
		},
		{
			name:    "partial overlap",
			left:    &Region{Offset: 0, Length: 8},
			right:   &Region{Offset: 4, Length: 8},
			overlap: true,
		},
		{
			name:    "containment overlaps",
			left:    &Region{Offset: 2, Length: 2},
			right:   &Region{Offset: 0, Length: 8},
			overlap: true,
		},
		{
			name:    "adjacent regions are disjoint",
			left:    &Region{Offset: 0, Length: 8},
			right:   &Region{Offset: 8, Length: 8},
			overlap: false,
		},
		{
			name:    "separated regions are disjoint",
			left:    &Region{Offset: 0, Length: 4},
			right:   &Region{Offset: 8, Length: 4},
			overlap: false,
		},
		{
			name:    "empty region inside another is disjoint",
			left:    &Region{Offset: 4, Length: 0},
			right:   &Region{Offset: 0, Length: 8},
			overlap: false,
		},
		{
			name:    "empty region at boundary is disjoint",
			left:    &Region{Offset: 8, Length: 0},
			right:   &Region{Offset: 0, Length: 8},
			overlap: false,
		},
		{
			name:    "two empty regions are disjoint",
			left:    &Region{Offset: 4, Length: 0},
			right:   &Region{Offset: 4, Length: 0},
			overlap: false,
		},
		{
			name:    "negative offsets still use interval arithmetic",
			left:    &Region{Offset: -8, Length: 4},
			right:   &Region{Offset: -6, Length: 4},
			overlap: true,
		},
		{
			name:    "unknown left fails closed",
			left:    nil,
			right:   &Region{Offset: 0, Length: 8},
			overlap: true,
		},
		{
			name:    "unknown right fails closed",
			left:    &Region{Offset: 0, Length: 8},
			right:   nil,
			overlap: true,
		},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if got := bc.regionsOverlap(test.left, test.right); got != test.overlap {
				t.Fatalf("regionsOverlap(%#v, %#v) = %v, want %v", test.left, test.right, got, test.overlap)
			}
			if got := bc.regionsOverlap(test.right, test.left); got != test.overlap {
				t.Fatalf("regionsOverlap symmetry failed: reverse = %v, want %v", got, test.overlap)
			}
		})
	}
}
