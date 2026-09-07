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
