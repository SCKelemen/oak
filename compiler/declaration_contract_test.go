package compiler

import (
	"strings"
	"testing"
)

func TestDeclarationContractCheckRejectsLostBinders(t *testing.T) {
	cases := []struct{ name, decl, diagnostic string }{
		{"value", "x[T]: i32 = 7", "value declarations do not support type parameters"},
		{"tag", "json[T]: tag = { name: string }", "tag declarations do not support type parameters"},
		{"protocol", "P[T]: protocol = { initial A\n tick: A -> A }", "protocol declarations do not support type parameters"},
		{"literals", "L[T]: literals = { \"abc\" }", "literals declarations do not support type parameters"},
		{"dual_adt", "Box[T]: type[U] = | Wrap: U", "but not both"},
	}
	for _, tt := range cases {
		t.Run(tt.name, func(t *testing.T) {
			_, err := New().WithSource(tt.name+".oak", tt.decl+"\nmain: (): i32 = 0").Check().Get()
			if err == nil || !strings.Contains(err.Error(), tt.diagnostic) {
				t.Fatalf("want %q, got %v", tt.diagnostic, err)
			}
		})
	}
}

func TestDeclarationContractCheckPreservesSupportedDeclarations(t *testing.T) {
	cases := map[string]string{
		"value":             "x: i32 = 7\nmain: (): i32 = x",
		"tag":               "json: tag = { name: string }\nmain: (): i32 = 0",
		"protocol":          "P: protocol = { initial A\n tick: A -> A }\nmain: (): i32 = 0",
		"literals":          "L: literals = { \"abc\" }\nmain: (): i32 = 0",
		"outer_adt":         "Box[T]: type = | Wrap: T\nmain: (): i32 = 0",
		"inner_adt":         "Box: type[T] = | Wrap: T\nmain: (): i32 = 0",
		"generic_function":  "id[T]: (x: T): T = x\nmain: (): i32 = id(i32(7))",
		"variadic_function": "f: (xs: ...i32): i32 = 7\nmain: (): i32 = f() + f(i32(1), i32(2))",
	}
	for name, src := range cases {
		t.Run(name, func(t *testing.T) {
			if _, err := New().WithSource(name+".oak", src).Check().Get(); err != nil {
				t.Fatal(err)
			}
		})
	}
}

func TestInterfaceContractCheck(t *testing.T) {
	cases := []struct{ name, iface, param, diagnostic string }{
		{"ordinary_scalar", "I: interface = fn (self) m(x: i32) -> i32", "x: i32", ""},
		{"ordinary_slice", "I: interface = fn (self) m(xs: []i32) -> i32", "xs: []i32", ""},
		{"wrong_parameter", "I: interface = fn (self) m(x: u32) -> i32", "x: i32", "does not satisfy"},
		{"fixed_vs_variadic", "I: interface = fn (self) m(xs: []i32) -> i32", "xs: ...i32", "does not satisfy"},
		{"variadic_vs_scalar", "I: interface = fn (self) m(xs: ...i32) -> i32", "x: i32", "variadic interface methods are not supported yet"},
		{"variadic_vs_variadic", "I: interface = fn (self) m(xs: ...i32) -> i32", "xs: ...i32", "variadic interface methods are not supported yet"},
		{"generic", "I[U: Missing]: interface = fn (self) m(x: i32) -> i32", "x: i32", "generic interface contracts are not supported yet"},
		{"typed_receiver", "I: interface = fn (self: i32) m(x: i32) -> i32", "x: i32", "typed interface receivers are not supported yet"},
	}
	for _, tt := range cases {
		t.Run(tt.name, func(t *testing.T) {
			source := tt.iface + "\nThing: type = | One | Two\nfn (s: Thing) m(" + tt.param + ") -> i32 { 7 }\nfn [T: I] use(s: T) -> i32 { 7 }\nmain: (): i32 { thing: Thing = .One\n use(thing) }"
			_, err := New().WithSource(tt.name+".oak", source).Check().Get()
			if tt.diagnostic == "" {
				if err != nil {
					t.Fatal(err)
				}
			} else if err == nil || !strings.Contains(err.Error(), tt.diagnostic) {
				t.Fatalf("want %q, got %v", tt.diagnostic, err)
			}
			t.Logf("Check error: %v", err)
		})
	}
}

func TestInterfaceContractPreservesOrdinaryMethodCall(t *testing.T) {
	source := `I: interface = fn (self) m(x: i32) -> i32
Thing: type = | One | Two
fn (s: Thing) m(x: i32) -> i32 { 7 }
fn [T: I] use(s: T) -> i32 { 7 }
main: (): i32 { thing: Thing = .One
 use(thing) + thing.m(i32(1)) }`
	if _, err := New().WithSource("ordinary_method.oak", source).Check().Get(); err != nil {
		t.Fatal(err)
	}
}

func TestInterfaceContractAPISnapshot(t *testing.T) {
	snapshot, err := New().WithPackageName("example/interface").WithSource("interface.oak", "pub I: interface = fn (self) m(x: i32) -> i32").APISnapshot("1.0.0").Get()
	if err != nil {
		t.Fatal(err)
	}
	if got := snapshot.Exports["I"].Type; got != "interface{m(i32)->i32}" {
		t.Fatalf("ordinary interface identity changed: %q", got)
	}
	for _, source := range []string{
		"pub I[T]: interface = fn (self) m(x: T) -> T",
		"pub I: interface = fn (self: i32) m(x: i32) -> i32",
		"pub I: interface = fn (self) m(xs: ...i32) -> i32",
	} {
		if _, err := New().WithPackageName("example/interface").WithSource("unsupported.oak", source).APISnapshot("1.0.0").Get(); err == nil {
			t.Fatalf("snapshot published weakened interface: %s", source)
		}
	}
}
