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
`)
	if abnormal || code != 78 {
		t.Fatalf("exit = (%d, abnormal=%v), want 78", code, abnormal)
	}
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

func TestE2EExtensibleRecordFunctionSpecializesPerLayout(t *testing.T) {
	code, abnormal := buildAndRun(t, "elm_extensible_record_specialization", `
AB: type = struct { a: i32, b: u8 }
BA: type = struct { b: u8, a: i32 }

getA: (value: { r | a: i32 }): i32 = value.a

main: (): i32 {
  ab: AB = AB { a: 20, b: 1 }
  ba: BA = BA { b: 2, a: 22 }
  getA(ab) + getA(ba)
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
