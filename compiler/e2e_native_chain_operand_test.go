package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/nativegen"
)

// A computed condition operand in any arm of a chain
// (docs/spec/94-assembler.md §9 "If-conversion";
// nativegen/select.go). The chain's compares are emitted before its
// selects, so an operand the compare cannot take directly is evaluated
// there: for the first arm that is where the source evaluates it too, and
// for a later arm it is speculation, so the operand must be safe to
// evaluate on a path the source would not have taken. Before this, only
// the first arm's operand could be computed, and a later one left the
// whole chain unrecognized — the first arm branched and only the
// remainder was if-converted.
const nativeChainOperandProgram = `
side: (a: u32): u32 = a + u32(1)

// The second arm's left operand is computed.
computed: (a: u32, b: u32, c: u32, d: u32): u32 {
  x: u32 = 0
  a < b ? {
    x = a
  } | c + u32(1) < d ? {
    x = c
  } | {
    x = d
  }
  x
}

// A call in a later arm's condition is not safe to evaluate ahead of the
// chain: the branch stands.
called: (a: u32, b: u32, c: u32): u32 {
  x: u32 = 0
  a < b ? {
    x = a
  } | side(c) < b ? {
    x = b
  } | {
    x = a
  }
  x
}

// In a loop body: the body is one block, the loop's own test aside.
buckets: (v: []u32, lo: u32, hi: u32): u32 {
  total: u32 = 0
  i: u32 = 0
  while i < len(v) {
    x: u32 = v[i]
    a: u32 = 0
    x < lo ? {
      a = x
    } | x + u32(1) < hi ? {
      a = hi
    } | {
      a = lo
    }
    total = total + a
    i = i + u32(1)
  }
  total
}

// A later group assigns a variable the first group's arm does not. The
// groups are applied outward, so without a guard the second comparison
// set n even where the first arm matched — a fall-through the source
// does not have, which the verifier refuses.
fall_through: (a: u32, b: u32, c: u32, d: u32): u32 {
  m: u32 = 1
  n: u32 = 2
  a < b ? {
    m = a
  } | c < d ? {
    n = c
  } | {
    n = 9
  }
  m * u32(1000) + n
}

reach: (v: []u32): u32 = len(v) > u32(3) ? fall_through(v[0], v[1], v[2], v[3]) | u32(0)

main: (): i32 {
  xs: [4]u32 = [4]u32{ 1, 50, 200, 9 }
  ys: [4]u32 = [4]u32{ 5, 9, 1, 0 }
  // computed(7,3,4,9) = 4 (5 < 9), called(7,3,1) = 3 (side(1) = 2 < 3),
  // buckets = 1 + 100 + 10 + 9 = 120, reach(5,9,1,0) = 5 * 1000 + 2 = 5002;
  // 4 + 3 + 120 + 5002 = 5129, 9 modulo 256, plus 118 is 127.
  i32_bits_u32(((computed(u32(7), u32(3), u32(4), u32(9)) + called(u32(7), u32(3), u32(1)) +
    buckets(view(&xs), u32(10), u32(100)) + reach(view(&ys))) & u32(255)) + u32(118))
}
`

func TestE2ENativeChainComputedOperands(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("chain_operand.oak", nativeChainOperandProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
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
	counts := func(name string) map[string]int {
		fn := units[name]
		if fn == nil {
			t.Fatalf("%s was not lowered natively:\n%s", name, joined)
		}
		out := map[string]int{}
		for _, item := range fn.Items {
			if ins, isIns := item.(asm.Instruction); isIns {
				out[ins.Mnemonic]++
			}
		}
		return out
	}
	// Both compares and both selects, and no branch at all.
	if got := counts("computed"); got["cmp"] != 2 || got["csel"] < 2 || got["b."] != 0 || got["b"] != 0 {
		t.Errorf("computed must be two compares and selects with no branch, got %v:\n%s", got, nativegen.Describe(units["computed"]))
	}
	if !strings.Contains(joined, "asm unit computed: proven equal to its Oak body") {
		t.Errorf("computed must be proven; diagnostics:\n%s", joined)
	}
	// The call keeps the branch.
	if got := counts("called"); got["b."] == 0 {
		t.Errorf("called must keep its branch: a call in a later arm's condition cannot run ahead of the chain, got %v:\n%s", got, nativegen.Describe(units["called"]))
	}
	// The loop body holds the selects and no branch but the loop's own.
	body := loopBody(units["buckets"])
	branches, selects := 0, 0
	for _, ins := range body {
		switch ins.Mnemonic {
		case "b.", "b", "cbz", "cbnz":
			branches++
		case "csel", "csinc":
			selects++
		}
	}
	if selects < 2 || branches > 1 {
		t.Errorf("buckets' loop body must select and keep at most the loop's own branch, got %d select(s) and %d branch(es):\n%s", selects, branches, nativegen.Describe(units["buckets"]))
	}
	// The fall-through shape builds and is proven: before the guard the
	// verifier refused it, which fails the native build.
	if !strings.Contains(joined, "asm unit reach: proven equal to its Oak body") {
		t.Errorf("reach must be proven: a later group must not assign past an earlier arm; diagnostics:\n%s", joined)
	}
	if strings.Contains(joined, "disagrees") {
		t.Errorf("a refused body:\n%s", joined)
	}
	_, code, abnormal := buildAndRunFrom(t, "native_chain_operand", comp)
	if abnormal || code != 127 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 127\n%s", code, abnormal, joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_chain_operand_c", New().WithSource("chain_operand.oak", nativeChainOperandProgram)); abnormal || code != 127 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 127", code, abnormal)
	}
}
