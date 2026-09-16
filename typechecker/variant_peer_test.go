package typechecker

import (
	"strings"
	"testing"
)

// A bare variant compared with a typed operand takes that operand's ADT
// (docs/spec/10-syntax.md, variant expressions): a variant name two ADTs
// of one package share is not ambiguous when the peer fixes it, in
// either order. Without a typed peer it stays ambiguous.
func TestBareVariantTakesThePeersADTInComparisons(t *testing.T) {
	input := `
Door: type =
  | Open
  | Closed
Session: type =
  | New
  | Closed
door_closed: (d: Door): Bool = d == .Closed
session_open: (s: Session): Bool = .Closed != s
`
	if errs := checkGenericShapeSource(t, input); len(errs) != 0 {
		t.Fatalf("unexpected errors: %v", errs)
	}
	ambiguous := `
Door: type =
  | Open
  | Closed
Session: type =
  | New
  | Closed
both: (): Bool = .Closed == .Closed
`
	errs := checkGenericShapeSource(t, ambiguous)
	if len(errs) == 0 || !strings.Contains(strings.Join(errs, "\n"), "ambiguous variant") {
		t.Fatalf("two bare variants must stay ambiguous; got %v", errs)
	}
}
