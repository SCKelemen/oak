package evaluator

import "testing"

func TestPipelineAndFieldAccessorEvaluation(t *testing.T) {
	got := testEval(`person := { name: 42, age: 7 }
person |> .name`)
	testIntegerObj(t, got, 42)
}

func TestFieldAccessorAsHigherOrderValue(t *testing.T) {
	got := testEval(`apply := fn(selector, value) { selector(value) }
person := { name: 42, age: 7 }
apply(.name, person)`)
	testIntegerObj(t, got, 42)
}
