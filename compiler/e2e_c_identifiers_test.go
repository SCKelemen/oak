package compiler

import "testing"

// Oak identifiers that are C keywords, leading-underscore names, or spelled
// in the emitter's oak_ namespace mangle to oak_id_<name> at every C
// emission site (codegen/identifiers.go): locals, parameters, globals,
// record fields (declarators, access, designators), and match binders.
func TestE2ECReservedIdentifiersMangle(t *testing.T) {
	code, abnormal := buildAndRun(t, "cidents", `
Frame: type = struct {
  short: u32
  register: u32
}

Slot: type = Some: u32 | None

default: u32 = 40
_hidden: u32 = 1

signed: (int_like: u32, volatile: u32): u32 = int_like + volatile

main: (): i32 {
  oak_assert: u32 = 1
  f: Frame = Frame { short: default, register: oak_assert }
  f.register = f.register + _hidden
  auto: Slot = .Some(u32(0))
  extra: u32 = auto ?
    | .Some(unsigned) => unsigned
    | .None => u32(9)
  assert(signed(f.short, f.register) + extra == u32(42))
  assert(offset_of[Frame](register) == u32(4))
  42
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
