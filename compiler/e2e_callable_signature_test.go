package compiler

import "testing"

// Reconstructing inferred aliases must retain every supported concrete
// signature, while typed literals keep their original source annotations.
func TestCallableSignatureCExecution(t *testing.T) {
	tests := map[string]string{
		"generic sum typed literal": `Choice[T]: type = Some: T | None
main: (): i32 { f := fn(x: Choice[i32]): i32 = 42; c: Choice[i32] = .None; f(c) }`,
		"generic sum literal alias and result": `Choice[T]: type = Some: T | None
main: (): i32 { f := fn(x: Choice[i32]): Choice[i32] = x; g := f; c: Choice[i32] = .Some(42); result: Choice[i32] = g(c); result ? | .Some(value) => value | .None => 0 }`,
		"generic sum named function": `Choice[T]: type = Some: T | None
keep: (x: Choice[i32]): Choice[i32] = x
main: (): i32 { f := keep; c: Choice[i32] = .Some(42); result: Choice[i32] = f(c); result ? | .Some(value) => value | .None => 0 }`,
		"generic record parameter and result": `Box[T]: type = struct { value: T }
keep: (x: Box[i32]): Box[i32] = x
main: (): i32 { f := keep; result: Box[i32] = f(Box { value: 42 }); result.value }`,
		"named record literal alias": `Point: type = struct { value: i32 }
main: (): i32 { f := fn(x: Point): Point = x; g := f; result: Point = g(Point { value: 42 }); result.value }`,
		"borrowed view literal alias": `main: (): i32 { f := fn(x: []i32): i32 = x[0]; g := f; data: [1]i32 = [42]; g(data[0:1]) }`,
		"borrowed span literal":       `main: (): i32 { f := fn(x: [*]i32): i32 { x[0] = 42; x[0] }; data: [1]i32; borrowed: [*]i32 = span(&data); f(borrowed) }`,
		"borrowed view named alias": `read: (x: []i32): i32 = x[0]
main: (): i32 { f := read; g := f; data: [1]i32 = [42]; g(data[0:1]) }`,
		"nested generic view": `Choice[T]: type = Some: T | None
count: (x: []Choice[i32]): i32 = 42
main: (): i32 { f := count; data: [0]Choice[i32]; f(data[0:0]) }`,
		"C boundary literal alias": `main: (): i32 { f := fn(x: c.Int): i32 = 42; g := f; g(c.Int(1)) }`,
	}
	for name, source := range tests {
		t.Run(name, func(t *testing.T) {
			code, signal := buildPackageAndRun(t, New().WithSource("callable_signature.oak", source))
			if signal || code != 42 {
				t.Fatalf("exit=%d signal=%v, want 42", code, signal)
			}
		})
	}
}

func TestCallableLiteralViewBoundsTrap(t *testing.T) {
	const source = `main: (): i32 { f := fn(x: []i32): i32 = x[1]; data: [1]i32 = [42]; f(data[0:1]) }`
	_, signal := buildPackageAndRun(t, New().WithSource("literal_view_bounds.oak", source))
	if !signal {
		t.Fatal("out-of-range literal view access did not trap")
	}
}
