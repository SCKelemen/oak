package compiler

import "testing"

// F20 (oak #149): slicing an inline borrow construction lowers through the
// checked slice helpers, not the `core_slice` macro, so the compound literal
// no longer splits a macro argument list.
func TestE2EInlineViewSlice(t *testing.T) {
	src := `
import(std)
sum: (items: []u8): u32 {
  total: u32 = u32(0)
  i: u32 = u32(0)
  while i < len(items) {
    total = total + u32(items[i])
    i = i + u32(1)
  }
  total
}
main: (): i32 {
  buffer: [6]u8 = [6]u8{ 1, 2, 3, 4, 5, 6 }
  part: []u8 = view(&buffer)[u32(1):u32(4)]
  assert(len(part) == u32(3) && part[0] == u8(2) && part[2] == u8(4))
  assert(sum(view(&buffer)[u32(4):u32(6)]) == u32(11))
  assert(len(view(&buffer)) == u32(6))
  true ? {
    tail: [*]u8 = span(&buffer)[u32(3):u32(6)]
    tail[0] = u8(40)
    assert(len(tail) == u32(3))
  }
  assert(buffer[3] == u8(40))
  i32_bits_u32(sum(view(&buffer)[u32(0):u32(3)]) + sum(view(&buffer)[u32(3):u32(4)]) - u32(4))
}
`
	code, abnormal := buildAndRun(t, "inline_view_slice", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
