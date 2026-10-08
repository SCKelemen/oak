package typechecker

import (
	"fmt"
	"reflect"
	"testing"
)

func variableCoverageConstructors() []struct {
	name string
	wrap func(Type) Type
} {
	return []struct {
		name string
		wrap func(Type) Type
	}{
		{"record", func(t Type) Type { return &RecordType{Fields: map[string]Type{"value": t}} }},
		{"function", func(t Type) Type { return &FunctionType{Parameters: []Type{t}, ReturnType: t} }},
		{"array", func(t Type) Type { return &ArrayType{Length: 4, ElementType: t} }},
		{"generic", func(t Type) Type { return &GenericType{Name: "Box", TypeArgs: []Type{t}} }},
		{"union", func(t Type) Type { return &UnionType{Types: []Type{t, &BoolType{}}} }},
		{"intersection", func(t Type) Type { return &IntersectionType{Types: []Type{t, &BoolType{}}} }},
		{"narrowed", func(t Type) Type {
			return &NarrowedADTVariantType{ADTName: "Option", VariantName: "Some", TypeArgs: []Type{t}}
		}},
		{"buffer", func(t Type) Type { return &BufferType{Element: t, Custody: "Device"} }},
		{"atomic", func(t Type) Type { return &AtomicType{Element: t} }},
		{"foreign_parameter", func(t Type) Type { return &CFnType{Parameters: []Type{t}, ReturnType: &UnitType{}} }},
		{"foreign_result", func(t Type) Type { return &CFnType{ReturnType: t} }},
	}
}

func TestTypeVariableConstructorCoverage(t *testing.T) {
	for _, c := range variableCoverageConstructors() {
		t.Run(c.name, func(t *testing.T) {
			tv := &TypeVar{Name: "T"}
			input := c.wrap(tv)
			u := NewUnifier()
			if !u.occursIn(tv, input) {
				t.Error("occurs check missed the nested binder")
			}
			if u.occursIn(&TypeVar{Name: "T"}, input) {
				t.Error("occurs check confused distinct binders with the same name")
			}
			if sub := u.Unify(tv, input); sub != nil {
				t.Error("accepted an infinite type")
			}
			if got := typeVarsIn(input); len(got) != 1 || got[0] != tv {
				t.Errorf("typeVarsIn = %v; want the original binder", got)
			}
			if got := collectTypeVars(input); !reflect.DeepEqual(got, []string{"T"}) {
				t.Errorf("collectTypeVars = %v", got)
			}

			concrete := &PrimitiveType{Name: "u32"}
			if got := (Substitution{tv: concrete}).Apply(input); !reflect.DeepEqual(got, c.wrap(concrete)) {
				t.Errorf("substitution left an unresolved binder or changed metadata: %#v", got)
			}
			if !reflect.DeepEqual(input, c.wrap(tv)) {
				t.Error("substitution mutated its input")
			}
			provided := quantifiedSubstitution(input, []string{"T"}, map[string]Type{"T": concrete}, NewUnifier())
			if provided[tv] != concrete {
				t.Error("explicit instantiation missed the nested binder")
			}
			scheme := &TypeScheme{TypeVars: []string{"T"}, Type: input}
			first := typeVarsIn(Instantiate(scheme, NewUnifier()))
			second := typeVarsIn(Instantiate(scheme, NewUnifier()))
			if len(first) != 1 || len(second) != 1 || first[0] == tv || first[0] == second[0] {
				t.Error("independent instantiations did not freshen the nested binder")
			}

			persistent := make(Substitution)
			group := &monomorphicGroup{}
			markMonomorphicTypeVars(input, persistent, group)
			if tv.Monomorphic == nil || tv.monomorphicGroup != group {
				t.Error("monomorphic marking missed the nested binder")
			}
			if findMonomorphicSubstitution(input) == nil || findMonomorphicGroup(input) != group {
				t.Error("monomorphic lookup missed the nested binder")
			}
			blocked := Generalize(input, nil)
			if blocked.Monomorphic == nil || len(blocked.TypeVars) != 0 {
				t.Error("a blocked nested binder was reopened polymorphically")
			}
			persistent[tv] = concrete
			if got := (Substitution{}).Apply(input); !reflect.DeepEqual(got, c.wrap(concrete)) {
				t.Error("empty local substitution lost the persistent solution")
			}
		})
	}
}

func TestTypeVariableNestedComposition(t *testing.T) {
	for _, outer := range variableCoverageConstructors() {
		for _, inner := range variableCoverageConstructors() {
			t.Run(outer.name+"/"+inner.name, func(t *testing.T) {
				a, b := &TypeVar{Name: "T"}, &TypeVar{Name: "T"}
				input := outer.wrap(inner.wrap(a))
				first := Substitution{a: b}
				second := Substitution{b: &PrimitiveType{Name: "u16"}}
				got := first.Compose(second).Apply(input)
				want := second.Apply(first.Apply(input))
				if !reflect.DeepEqual(got, want) || len(typeVarsIn(got)) != 0 {
					t.Error("substitution composition law or binder elimination failed")
				}
				if !NewUnifier().occursIn(a, input) {
					t.Error("mixed nesting hid an occurs-check cycle")
				}
			})
		}
	}
}

func TestTypeVariablePersistentDependencyThroughConstructors(t *testing.T) {
	for _, c := range variableCoverageConstructors() {
		t.Run(c.name, func(t *testing.T) {
			root, dependency := &TypeVar{Name: "Root"}, &TypeVar{Name: "T"}
			scheme := makeMonomorphicScheme(root, nil)
			commitMonomorphicBindings(Substitution{root: c.wrap(dependency)})
			if dependency.Monomorphic == nil || dependency.monomorphicGroup != root.monomorphicGroup {
				t.Fatal("a nested escaping variable lost persistent group membership")
			}
			concrete := &PrimitiveType{Name: "u8"}
			commitMonomorphicBindings(Substitution{dependency: concrete})
			if got := Instantiate(scheme, NewUnifier()); !reflect.DeepEqual(got, c.wrap(concrete)) {
				t.Error("later use did not see the committed nested solution")
			}
		})
	}
}

func variableCoverageDAG(depth int) Type {
	var typ Type = &TypeVar{Name: "T"}
	for i := 0; i < depth; i++ {
		typ = &FunctionType{Parameters: []Type{typ}, ReturnType: typ}
	}
	return typ
}

func BenchmarkTypeVariableCollectionDAG(b *testing.B) {
	for _, depth := range []int{8, 12, 16} {
		b.Run(fmt.Sprint(depth), func(b *testing.B) {
			typ := variableCoverageDAG(depth)
			b.ReportAllocs()
			b.ResetTimer()
			for i := 0; i < b.N; i++ {
				if len(typeVarsIn(typ)) != 1 {
					b.Fatal("lost binder")
				}
			}
		})
	}
}

func BenchmarkTypeVariableOccursDAG(b *testing.B) {
	typ := variableCoverageDAG(16)
	missing := &TypeVar{Name: "missing"}
	u := NewUnifier()
	b.ReportAllocs()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		if u.occursIn(missing, typ) {
			b.Fatal("invented occurrence")
		}
	}
}
