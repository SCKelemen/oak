package compiler

import "testing"

// Compile the actual generated translation unit and execute the indirect
// call. Text matches cannot catch a scalar fallback or invalid declarator.
func TestInferredCallableCExecution(t *testing.T) {
	const identity = `identity: (x: i32): i32 = x
`
	tests := map[string]string{
		"named function":    `main: (): i32 { f := identity; f(42) }`,
		"value alias":       `main: (): i32 { f := identity; g := f; g(42) }`,
		"typed value alias": `main: (): i32 { f: (i32) -> i32 = identity; g := f; g(42) }`,
		"field projection": `Holder: type = struct { callback: (i32) -> i32 }
main: (): i32 { h: Holder = Holder { callback: identity }; f := h.callback; f(42) }`,
		"generic body": `Holder: type = struct { callback: (i32) -> i32 }
invoke[T]: (h: T): i32 { f := h.callback; f(42) }
main: (): i32 = invoke[Holder](Holder { callback: identity })`,
		"higher order": `apply: (f: (i32) -> i32): i32 = f(42)
main: (): i32 { g := apply; g(identity) }`,
		"unit return": `noop: (): () = {}
main: (): i32 { f := noop; f(); 42 }`,
	}
	for name, source := range tests {
		t.Run(name, func(t *testing.T) {
			code, signal := buildPackageAndRun(t, New().WithSource("inferred_callable.oak", identity+source))
			if signal || code != 42 {
				t.Fatalf("exit=%d signal=%v, want 42", code, signal)
			}
		})
	}
}
