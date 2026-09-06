package source

import "testing"

func TestRefReturnsCanonicalSourceLocation(t *testing.T) {
	file := NewFile(7, "example.oak", "a😀b\n")
	span, err := file.Span(1, 5)
	if err != nil {
		t.Fatalf("Span: %v", err)
	}
	loc, err := file.Ref(span)
	if err != nil {
		t.Fatalf("Ref: %v", err)
	}
	if loc.Source != 7 || loc.Span != span {
		t.Fatalf("unexpected location: %#v", loc)
	}
}

func TestRefRejectsInvalidByteSpan(t *testing.T) {
	file := NewFile(1, "example.oak", "😀")
	if _, err := file.Ref(Span{Start: 1, End: 4}); err == nil {
		t.Fatal("expected intra-rune byte span to be rejected")
	}
}
