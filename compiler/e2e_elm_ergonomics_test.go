package compiler

import "testing"

func TestE2EElmPipelineAndFieldAccessor(t *testing.T) {
	code, abnormal := buildAndRun(t, "elm_record_ergonomics", `
Person: type = struct { name: i32, age: u8 }

add: (delta, value: i32): i32 = delta + value

main: (): i32 {
  person: Person = Person { name: 39, age: 7 }
  selected: i32 = person |> .name
  .name(person) |> add(selected)
}

func TestE2EFirstClassFieldAccessor(t *testing.T) {
	code, abnormal := buildAndRun(t, "elm_first_class_field_accessor", `
Person: type = struct { name: i32, age: u8 }

fn apply(selector: (Person) -> i32, value: Person) -> i32 { selector(value) }

main: (): i32 {
  person: Person = Person { name: 21, age: 7 }
  getter: (Person) -> i32 = .name
  apply(.name, person) + getter(person)
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2EGenericFieldAccessorInference(t *testing.T) {
	code, abnormal := buildAndRun(t, "elm_generic_field_accessor", `
Person: type = struct { name: i32, age: u8 }

fn [T, U] project(selector: (T) -> U, value: T) -> U { selector(value) }

main: (): i32 {
  person: Person = Person { name: 42, age: 7 }
  project(.name, person)
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
`)
	if abnormal || code != 78 {
		t.Fatalf("exit = (%d, abnormal=%v), want 78", code, abnormal)
	}
}
