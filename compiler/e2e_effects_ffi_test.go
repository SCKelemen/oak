package compiler

import (
	"fmt"
	"strings"
	"testing"
)

// F33: borrowing an existing foreign buffer constructs a view or span;
// it does not make the function's effects unknown. The unsafe assumption
// must still be recorded, including when a strict module admits it.
func TestForeignBorrowUnderForbids(t *testing.T) {
	for _, borrow := range []struct{ member, typ string }{
		{"borrow", "[]u32"}, {"borrow_mut", "[*]u32"},
	} {
		t.Run(borrow.member, func(t *testing.T) {
			src := fmt.Sprintf(`package main
leaf: (p: c.Ptr): u32 {
  result: u32 = 0
  unsafe {
    data: %s = c.%s[u32](p, u32(1))
    result = data[0]
  }
  result
}
hot: (p: c.Ptr): u32 forbids { Memory.Allocate, Device.Readback } = leaf(p)
main: (): i32 = 0
`, borrow.typ, borrow.member)
			for _, profile := range []string{"default", "strict"} {
				t.Run(profile, func(t *testing.T) {
					root := writeModule(t, map[string]string{
						"oak.mod":  "module example.com/borroweffects\noak 0.1.0\nprofile " + profile + "\nadmit OAK-B0110\n",
						"main.oak": src,
					})
					model, err := New().WithPackageDir(root).Check().Get()
					if err != nil {
						t.Fatal(err)
					}
					for _, d := range model.Diagnostics {
						if string(d.Code) == "OAK-B0110" && strings.Contains(d.Message, "foreign buffer contract") {
							return
						}
					}
					t.Fatal("foreign buffer contract must remain recorded under forbids")
				})
			}
		})
	}
}

// Recognizing the borrow must not hide effects in either operand or in
// the enclosing unsafe block. An unrowed provider remains unknown.
func TestForeignBorrowRetainsOperandEffects(t *testing.T) {
	for _, c := range []struct {
		name, prelude, pointer, count, after, code, want string
	}{
		{
			name:    "pointer effect",
			prelude: `provider: (): c.Ptr effects { Device.Readback } = c.extern("provider")`,
			pointer: "provider()", count: "u32(1)",
			code: CodeEffectForbidden, want: "hot -> provider",
		},
		{
			name:    "count effect",
			prelude: `provider: (): u32 effects { Memory.Allocate } = u32(1)`,
			pointer: "p", count: "provider()",
			code: CodeEffectForbidden, want: "hot -> provider",
		},
		{
			name:    "unknown pointer",
			prelude: `provider: (): c.Ptr = c.extern("provider")`,
			pointer: "provider()", count: "u32(1)",
			code: CodeEffectUnknown, want: "extern provider",
		},
		{
			name:    "unknown count",
			prelude: `provider: (): c.UInt32 = c.extern("provider")`,
			pointer: "p", count: "u32(provider())",
			code: CodeEffectUnknown, want: "extern provider",
		},
		{
			name:    "unknown call in unsafe",
			prelude: `provider: (): () = c.extern("provider")`,
			pointer: "p", count: "u32(1)", after: "provider()",
			code: CodeEffectUnknown, want: "extern provider",
		},
	} {
		for _, borrow := range []struct{ member, typ string }{
			{"borrow", "[]u32"}, {"borrow_mut", "[*]u32"},
		} {
			t.Run(borrow.member+"/"+c.name, func(t *testing.T) {
				src := fmt.Sprintf(`
%s
hot: (p: c.Ptr): u32 forbids { Memory.Allocate, Device.Readback } {
  result: u32 = 0
  unsafe {
    data: %s = c.%s[u32](%s, %s)
    result = data[0]
    %s
  }
  result
}
main: (): i32 = 0
`, c.prelude, borrow.typ, borrow.member, c.pointer, c.count, c.after)
				msg := effectError(t, "borrow_effects", src, c.code)
				if !strings.Contains(msg, c.want) {
					t.Fatalf("expected %q in diagnostic: %s", c.want, msg)
				}
			})
		}
	}
}
