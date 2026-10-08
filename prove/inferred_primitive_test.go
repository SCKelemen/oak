package prove

import "testing"

func TestInferredPrimitiveTheoremsRetainDeciderAuthority(t *testing.T) {
	model := check(t, `
combine: (a, b: u32): u32 { x := a | b; x }
correct: theorem (a, b: u32) { x := a | b; x == combine(a, b) }
incorrect: theorem (a, b: u32) { x := a & b; x == combine(a, b) }
main: (): i32 = 0
`)
	results, err := Theorems(model, 0)
	if err != nil {
		t.Fatal(err)
	}
	want := map[string]Status{"correct": Decided, "incorrect": Refuted}
	for _, result := range results {
		if result.Status != want[result.Name] {
			t.Fatalf("%s: %s %s", result.Name, result.Status, result.Detail)
		}
		if _, ok := GoSyntax(model, result.Name); ok {
			t.Fatalf("inferred syntax acquired unsupported authority for %s", result.Name)
		}
		delete(want, result.Name)
	}
	if len(want) != 0 {
		t.Fatalf("missing results: %v", want)
	}
}
