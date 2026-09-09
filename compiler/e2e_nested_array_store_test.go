package compiler

import "testing"

// Array fields reached through span indexing must remain attached to their
// owner when written. Rvalue record indexing returns a copy in the C backend.
func TestE2ENestedArrayFieldStores(t *testing.T) {
	source := `package main
Leaf: type = struct { values: [3]u32 }
Root: type = struct { ready: [3]u32, leaves: [2]Leaf }

store: (roots: [*]Root, row: u32, slot: u32, value: u32): () {
  roots[row].ready[slot] = value
  roots[row].leaves[u32(1)].values[slot] = value + u32(1)
}

main: (): i32 = {
  storage: [2]Root
  roots: [*]Root = span(&storage)
  store(roots, u32(1), u32(2), u32(20))
  assert(roots[1].ready[2] == u32(20))
  assert(roots[1].leaves[1].values[2] == u32(21))
  assert(roots[0].ready[2] == u32(0))
  assert(roots[1].leaves[0].values[2] == u32(0))
  storage[0].leaves[0].values[1] = u32(42)
  assert(roots[0].leaves[0].values[1] == u32(42))
  42
}
`
	code, abnormal := buildAndRun(t, "nested_array_field_store", source)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
