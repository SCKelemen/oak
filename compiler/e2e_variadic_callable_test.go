package compiler

import "testing"

func TestVariadicCallableCExecution(t *testing.T) {
	const total = `total: (base: i32, rest: ...i32): i32 {
 result: i32 = base
 index: u32 = 0
 while index < len(rest) { result = result + rest[index]; index = index + 1 }
 result
}
`
	tests := map[string]string{
		"empty tail":    `main: (): i32 { f := total; f(42) }`,
		"multiple tail": `main: (): i32 { f := total; f(39, 1, 2) }`,
		"no fixed parameters": `forty_two: (rest: ...i32): i32 = 42
main: (): i32 { f := forty_two; f() }`,
		"value alias": `main: (): i32 { f := total; g := f; g(39, 1, 2) }`,
		"generic body": `invoke[T]: (x: T): i32 { f := total; f(39, 1, 2) }
main: (): i32 = invoke[i32](0)`,
		"effectful tail order": `tick: (state: [*]i32): i32 { value: i32 = state[0]; state[0] = value + 1; value }
ordered: (base: i32, rest: ...i32): i32 = base + rest[0] * 10 + rest[1]
main: (): i32 { state: [1]i32 = [1]; borrowed: [*]i32 = span(&state); f := ordered; result: i32 = f(30, tick(borrowed), tick(borrowed)); assert(borrowed[0] == 3); result }`,
	}
	for name, source := range tests {
		t.Run(name, func(t *testing.T) {
			code, signal := buildPackageAndRun(t, New().WithSource("variadic_callable.oak", total+source))
			if signal || code != 42 {
				t.Fatalf("exit=%d signal=%v, want 42", code, signal)
			}
		})
	}
}
