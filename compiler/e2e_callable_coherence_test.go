package compiler

import (
	"strings"
	"testing"
)

func TestE2ECallableFormsAgree(t *testing.T) {
	const canonical = `
add: (x, y: i32): i32 effects { } forbids { Memory.Allocate } = x + y
identity[T]: (x: T): T effects { } = x
main: (): i32 = identity(add(20, 22))
`
	legacy := strings.ReplaceAll(canonical, "add: (", "fn add(")
	legacy = strings.ReplaceAll(legacy, "identity[T]: (", "fn [T] identity(")
	for name, source := range map[string]string{"declaration": canonical, "fn": legacy} {
		t.Run(name, func(t *testing.T) {
			code, abnormal := buildAndRun(t, name, source)
			if abnormal || code != 42 {
				t.Fatalf("exit=(%d,%v)", code, abnormal)
			}
		})
	}
}

func TestE2EContextualNamesRemainCallable(t *testing.T) {
	source := `
operator: (x: i32): () = { assert(x == 42) }
export: (name: string): () = { assert(name == "ok") }
main: (): i32 = { operator(42); export("ok"); 42 }
`
	code, abnormal := buildAndRun(t, "contextual_calls", source)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2ELegacyCallableContextualBodies(t *testing.T) {
	source := `fn a(effects: i32): i32 effects
fn b(forbids: i32): i32 forbids
fn c(laws: i32): i32 laws
fn d(dispatch: i32): i32 dispatch
main: (): i32 = a(b(c(d(42))))
`
	code, abnormal := buildAndRun(t, "bare_contextual", source)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
