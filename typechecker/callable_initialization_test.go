package typechecker

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func TestCallableStorageRequiresInitializer(t *testing.T) {
	const prefix = `Holder: type = struct { callback: (i32) -> i32 }
HolderAlias: type = Holder
Box[T]: type = struct { value: T }
id: (x: i32): i32 = x
`
	tests := []struct {
		name, source string
		reject       bool
	}{
		{"direct local", `main: (): i32 { f: (i32) -> i32; f(42) }`, true},
		{"direct global", `f: (i32) -> i32`, true},
		{"record alias", `main: (): i32 { h: HolderAlias; h.callback(42) }`, true},
		{"record", `main: (): i32 { h: Holder; h.callback(42) }`, true},
		{"anonymous record", `main: (): i32 { h: { callback: (i32) -> i32 }; 0 }`, true},
		{"owned array", `main: (): i32 { a: [2](i32) -> i32; 0 }`, true},
		{"nested array record", `Nested: type = struct { holders: [2]Holder }
main: (): i32 { n: Nested; 0 }`, true},
		{"generic record", `main: (): i32 { b: Box[Holder]; 0 }`, true},
		{"generic nested", `main: (): i32 { b: Box[Box[Holder]]; 0 }`, true},
		{"generic function", `default_value[T]: (x: T): T { value: T; value }
main: (): i32 { h: Holder = default_value[Holder](Holder { callback: id }); 0 }`, true},
		{"sum payload", `Action: type = Run: Holder | Stop
main: (): i32 { action: Action; 0 }`, true},
		{"generic sum payload", `Choice[T]: type = Some: T | None
main: (): i32 { choice: Choice[Holder]; 0 }`, true},
		{"wrong missing record field", `main: (): i32 { h: Holder = Holder {}; 0 }`, true},
		{"wrong empty array initializer", `main: (): i32 { a: [1]Holder = []; 0 }`, true},
		{"wrong numeric initializer", `main: (): i32 { f: (i32) -> i32 = 0; 0 }`, true},
		{"wrong inferred initializer", `main: (): i32 { f := 0; f(42) }`, true},
		{"declaration only", `Other: type = struct { callback: (i32) -> i32 }`, false},
		{"direct initialized", `main: (): i32 { f: (i32) -> i32 = id; f(42) }`, false},

		{"record initialized", `main: (): i32 { h: Holder = Holder { callback: id }; f := h.callback; f(42) }`, false},
		{"inferred function", `main: (): i32 { f := id; f(42) }`, false},
		{"empty array", `main: (): i32 { a: [0](i32) -> i32; 0 }`, false},
		{"borrowed view", `main: (): i32 { a: [](i32) -> i32; 0 }`, false},
		{"borrowed span", `main: (): i32 { a: [*](i32) -> i32; 0 }`, false},
		{"scalar", `main: (): i32 { x: i32; x }`, false},
		{"scalar aggregate", `main: (): i32 { b: Box[i32]; b.value }`, false},
		{"generic scalar default", `default_value[T]: (x: T): T { value: T; value }
main: (): i32 = default_value[i32](42)`, false},
		{"forward function", `main: (): i32 = later(42)
later: (x: i32): i32 = x`, false},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			source := prefix + tt.source
			p := parser.New(scanner.New(source))
			program := p.ParseProgram()
			if len(p.Errors()) != 0 {
				t.Fatalf("parse: %v", p.Errors())
			}
			tc := setupTypeChecker(source)
			tc.CheckProgram(program)
			if got := len(tc.Errors()) > 0; got != tt.reject {
				t.Fatalf("reject=%v, errors=%v", tt.reject, tc.Errors())
			}
			if tt.reject && !strings.HasPrefix(tt.name, "wrong ") {
				found := false
				for _, d := range tc.Diagnostics() {
					if d.Code == CodeCallableInitializer {
						found = true
					}
				}
				if !found {
					t.Fatalf("missing %s: %v", CodeCallableInitializer, tc.Errors())
				}
			}
		})
	}
}

// Source aliases currently admit identifier spellings only. Test the
// semantic alias boundary directly without pretending callable alias syntax
// is accepted by the parser.
func TestCallableInitializationResolvedAlias(t *testing.T) {
	tc := setupTypeChecker("")
	callback := &FunctionType{Parameters: []Type{&PrimitiveType{Name: "i32"}}, ReturnType: &PrimitiveType{Name: "i32"}}
	tc.env.SetType("Callback", callback)
	source := `main: (): i32 { f: Callback; 0 }`
	p := parser.New(scanner.New(source))
	program := p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatal(p.Errors())
	}
	tc.CheckProgram(program)
	for _, d := range tc.Diagnostics() {
		if d.Code == CodeCallableInitializer {
			return
		}
	}
	t.Fatalf("resolved callable alias escaped initialization check: %v", tc.Errors())
}

func TestCallableInitializationRecursiveStorage(t *testing.T) {
	tc := setupTypeChecker("")
	callback := &FunctionType{ReturnType: &UnitType{}}
	record := &RecordType{Fields: map[string]Type{}, Order: []string{"cycle", "callback"}}
	record.Fields["cycle"] = record
	record.Fields["callback"] = callback
	for _, typ := range []Type{record, &UnionType{Types: []Type{&PrimitiveType{Name: "i32"}, record}}, &IntersectionType{Types: []Type{record}}} {
		if _, found := tc.zeroContainsCallable(typ); !found {
			t.Fatalf("missed callable in %T", typ)
		}
	}
}
