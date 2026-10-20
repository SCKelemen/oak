package typechecker

import (
	"fmt"
	"testing"
)

func TestTypeVariableWalkSmallSetAndStackSpill(t *testing.T) {
	for _, depth := range []int{0, 1, 14, 15, 16, 17, 31, 32, 33, 64} {
		t.Run(fmt.Sprint(depth), func(t *testing.T) {
			if variables := typeVarsIn(variableCoverageDAG(depth)); len(variables) != 1 {
				t.Fatalf("depth %d: got %d binders, want one", depth, len(variables))
			}
		})
	}
	parameters := make([]Type, 0, 192)
	for i := 0; i < 96; i++ {
		variable := &TypeVar{Name: "T"}
		parameters = append(parameters, variable, variable)
	}
	variables := typeVarsIn(&FunctionType{Parameters: parameters, ReturnType: &PrimitiveType{Name: "u32"}})
	if len(variables) != 96 {
		t.Fatalf("wide signature: got %d binders, want 96", len(variables))
	}
	for i, variable := range variables {
		if variable != parameters[2*i] {
			t.Fatal("spill changed first-appearance order or binder identity")
		}
	}
}

func TestTypeVariableWalkNilConstructors(t *testing.T) {
	for _, typ := range []Type{
		nil, (*TypeVar)(nil), (*RecordType)(nil), (*FunctionType)(nil),
		(*ArrayType)(nil), (*GenericType)(nil), (*UnionType)(nil),
		(*IntersectionType)(nil), (*NarrowedADTVariantType)(nil),
		(*BufferType)(nil), (*AtomicType)(nil), (*CFnType)(nil),
	} {
		if walkTypeVariables(typ, func(*TypeVar) bool { t.Fatal("visited nil"); return true }) {
			t.Fatal("nil constructor reported a match")
		}
	}
}

func variableCoverageTree(depth int) Type {
	if depth == 0 {
		return &TypeVar{Name: "T"}
	}
	return &FunctionType{
		Parameters: []Type{variableCoverageTree(depth - 1)},
		ReturnType: variableCoverageTree(depth - 1),
	}
}

// Non-shared shapes deliberately accompany the DAG benchmarks: the visited
// set has a cost, and a shared-graph win is not a whole-checker speedup.
func BenchmarkTypeVariableCollectionShapes(b *testing.B) {
	cases := []struct {
		name string
		typ  Type
		want int
	}{
		{"leaf", &TypeVar{Name: "T"}, 1},
		{"simple", &FunctionType{Parameters: []Type{&TypeVar{Name: "T"}}, ReturnType: &PrimitiveType{Name: "u32"}}, 1},
		{"ground", &FunctionType{Parameters: []Type{&PrimitiveType{Name: "u32"}}, ReturnType: &PrimitiveType{Name: "u32"}}, 0},
		{"tree8", variableCoverageTree(8), 256},
	}
	for _, c := range cases {
		b.Run(c.name, func(b *testing.B) {
			b.ReportAllocs()
			b.ResetTimer()
			for i := 0; i < b.N; i++ {
				if got := len(typeVarsIn(c.typ)); got != c.want {
					b.Fatalf("got %d binders, want %d", got, c.want)
				}
			}
		})
	}
}
