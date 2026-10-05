package compiler

// Early return (docs/spec/10-syntax.md §2e): the parser lowers `return`
// into the tail-expression shapes — a guard clause nests the rest of the
// body into the arm that did not return; a return inside a loop sets the
// function's value cell and flag and breaks, and the loop's exit re-raises
// it — so the native verifier proves the units as it proves a written
// flag, and the constant-branch fold removes the flag tests it can.

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

const nativeReturnProgram = `Regime: type = struct {
  slots: [8]u8
  count: u32
}

// A guard clause, then a scan that returns from inside the loop.
first_free: (s: [*]Regime, dom: u32): u32 {
  bad: Bool = dom >= u32(1)
  bad ? { return u32(99) }
  i: u32 = u32(0)
  while i < s[dom].count {
    free: Bool = s[dom].slots[i & u32(7)] == u8(0)
    free ? { return i }
    i = i + u32(1)
  }
  u32(64)
}

// Nested loops, return from the inner one.
first_pair: (s: [*]Regime, dom: u32, want: u8): u32 {
  i: u32 = u32(0)
  while i < u32(8) {
    j: u32 = u32(0)
    while j < s[dom].count {
      same: Bool = s[dom].slots[i] == want && s[dom].slots[j & u32(7)] == want && i != j
      same ? { return i * u32(10) + j }
      j = j + u32(1)
    }
    i = i + u32(1)
  }
  u32(255)
}

// A unit function returning early.
mark: (s: [*]Regime, dom: u32, upto: u32): () {
  i: u32 = u32(0)
  while i < u32(8) {
    done: Bool = i >= upto
    done ? { return }
    s[dom].slots[i] = u8(7)
    i = i + u32(1)
  }
}

// Return as the last statement, and a chained guard.
classify: (x: u32): u8 {
  x == u32(0) ? { return u8(0) }
  x < u32(10) ? { return u8(1) }
  return u8(2)
}

main: (): i32 {
  regimes: [1]Regime
  s: [*]Regime = span(&regimes)
  s[0].count = u32(6)
  s[0].slots[0] = u8(1)
  s[0].slots[1] = u8(1)
  a: u32 = first_free(s, u32(0))
  b: u32 = first_free(s, u32(4))
  c: u32 = first_pair(s, u32(0), u8(1))
  mark(s, u32(0), u32(3))
  d: u32 = u32(s[0].slots[2]) * u32(10) + u32(s[0].slots[3])
  e: u32 = u32(classify(u32(0))) + u32(classify(u32(5))) * u32(10) + u32(classify(u32(50))) * u32(100)
  ok: Bool = a == u32(2) && b == u32(99) && c == u32(1) && d == u32(70) && e == u32(210)
  ok ? 42 | 1
}
`

func TestE2ENativeReturnProven(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("ret.oak", nativeReturnProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.SemanticModel().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v\n%s", err, strings.Join(infos, "\n"))
	}
	units := map[string]*asm.Function{}
	for _, fn := range model.AsmFunctions {
		units[fn.Name] = fn
	}
	joined := strings.Join(infos, "\n")
	for _, name := range []string{"first_free", "first_pair", "mark", "classify"} {
		if units[name] == nil {
			t.Fatalf("%s was not lowered natively:\n%s", name, joined)
		}
		if !strings.Contains(joined, "asm unit "+name+": proven") {
			t.Fatalf("%s must be proven with its returns:\n%s", name, joined)
		}
	}
	// A guard clause is a branch, not a flag: classify carries no cell.
	for _, item := range units["classify"].Items {
		if ins, ok := item.(asm.Instruction); ok && strings.HasPrefix(ins.Mnemonic, "st") {
			t.Fatalf("classify: a return outside a loop needs no store:\n%v", ins)
		}
	}
	_, code, abnormal := buildAndRunFrom(t, "ret", comp)
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
}
