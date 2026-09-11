package compiler

import "testing"

// A template that calls another template with an explicit type argument
// (`inner[T](..)`) must still generalize: the `T` in the call is a type,
// not a captured value. Before the fix the outer template was blocked and
// its second instantiation failed with "cannot reuse authority at
// incompatible type".
func TestE2EGenericNestedTemplateTwoInstantiations(t *testing.T) {
	src := `import(std)

inner[T]: (items: [*]T, i: u32): () {
  held: T = items[i]
  items[i] = items[0]
  items[0] = held
}

outer[T]: (items: [*]T): () {
  n: u32 = len(items)
  n > u32(1) ? { inner[T](items, n - u32(1)) }
}

main: (): i32 {
  big: [4]i32
  true ? {
    b: [*]i32 = span(&big)
    b[0] = i32(3); b[1] = i32(0) - i32(2); b[2] = i32(9); b[3] = i32(1)
    outer[i32](b)
  }
  data: [4]u32
  true ? {
    s: [*]u32 = span(&data)
    s[0] = u32(3); s[1] = u32(2); s[2] = u32(9); s[3] = u32(1)
    outer[u32](s)
  }
  assert(data[0] == u32(1) && data[3] == u32(3) && big[0] == i32(1) && big[3] == i32(3))
  42
}
`
	code, abnormal := buildAndRun(t, "generic_nested_template", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
