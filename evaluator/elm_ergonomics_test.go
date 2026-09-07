package evaluator

import "testing"

func TestPipelineAndFieldAccessorEvaluation(t *testing.T) {
	got := testEval(`person := { name: 42, age: 7 }
person |> .name`)
	testIntegerObj(t, got, 42)
}
