package compiler

import (
	"strings"
	"testing"
)

// The source inliner runs before the type checker, so an argument it
// substitutes directly for a parameter is never compared with the
// parameter's type at a call. It substitutes only a name declared with
// the parameter's own type spelling; every other argument binds through
// a typed temporary the checker types (docs/spec/90-backend.md section 9).
// Phantom-parameterized records and aliases (docs/spec/20-types.md) are
// the property at stake: Buffer[Device] must not pass for Buffer[Staging]
// through a helper small enough to inline.
func TestInlinerKeepsTheCallSeamTyped(t *testing.T) {
	compile := func(src string) error {
		_, err := New().WithSource("seam.oak", src).EmitC().Get()
		return err
	}
	const regions = "Staging: type = struct { id: u64 }\nDevice: type = struct { id: u64 }\n"
	record := regions + `
Buffer[R]: type = struct { off: u32, len: u32 }
use_staging: (b: Buffer[Staging]): u32 { b.len }
mix: (d: Buffer[Device]): u32 { use_staging(d) }
`
	err := compile(record)
	if err == nil {
		t.Fatal("Buffer[Device] passed where Buffer[Staging] is declared")
	}
	if !strings.Contains(err.Error(), "argument 1") {
		t.Fatalf("the mismatch must be reported at the argument: %v", err)
	}
	alias := regions + `
Id[T]: type = u64
use_staging: (x: Id[Staging]): u64 { x }
mix: (t: Id[Device]): u64 { use_staging(t) }
`
	err = compile(alias)
	if err == nil {
		t.Fatal("Id[Device] passed where Id[Staging] is declared")
	}
	if !strings.Contains(err.Error(), "expected Id[Staging], got Id[Device]") {
		t.Fatalf("the alias mismatch must name both instantiations at the argument: %v", err)
	}
	// The same instantiation on both sides inlines as before.
	if err := compile(regions + "Buffer[R]: type = struct { off: u32, len: u32 }\nuse_staging: (b: Buffer[Staging]): u32 { b.len }\nsame: (d: Buffer[Staging]): u32 { use_staging(d) }\n"); err != nil {
		t.Fatalf("matching instantiations must compile: %v", err)
	}
}

// A name declared with the parameter's type substitutes directly, so the
// caller's guard still proves the helper's element access. A global's
// declaration the inliner knows too, so it substitutes as before (its
// guard proves nothing about a global the extents checker does not track,
// on this branch as on the one before it).
func TestInlinerSubstitutesSameTypedNames(t *testing.T) {
	const program = `
limit: u32 = u32(4)
at: (v: []u8, i: u32): u8 { v[i] }
first: (b: []u8, o: u32): u8 {
  ok: Bool = o < len(b)
  r: u8 = 0
  ok ? { r = at(b, o) }
  r
}
fourth: (b: []u8): u8 {
  ok: Bool = limit < len(b)
  r: u8 = 0
  ok ? { r = at(b, limit) }
  r
}
`
	emitted, err := New().WithSource("seam_elide.oak", program).EmitC().Get()
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	for _, fn := range []string{"oak_first"} {
		start := strings.LastIndex(emitted, "u8 "+fn+"(")
		start = strings.Index(emitted[start:], "{") + start
		body := emitted[start : start+strings.Index(emitted[start:], "\n}")]
		if strings.Contains(body, "oak_view_index_u8") {
			t.Fatalf("%s: the guard must prove the inlined helper's read:\n%s", fn, body)
		}
		if !strings.Contains(body, ").base[") {
			t.Fatalf("%s: the inlined read must be a raw element read:\n%s", fn, body)
		}
	}
	if strings.Contains(emitted, "__inl") && strings.Contains(emitted, "_arg1     = limit") {
		t.Fatalf("a global declared with the parameter's type substitutes directly, not through a temporary")
	}
}
