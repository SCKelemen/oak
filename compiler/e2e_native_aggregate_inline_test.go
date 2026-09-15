package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

// Aggregate helpers inlined on the native lane (docs/spec/94-assembler.md
// §9): a small helper taking or returning a record is expanded at its
// call, a field-path argument to a parameter the callee only reads
// standing for the parameter without a copy. The C backend's realization
// of the same program is the oracle; the verifier compares the lowering
// against the body as written, the callees taken at their Oak bodies.
const nativeAggregateInlineProgram = `
State: type = struct {
  a: u64
  b: u64
  c: u64
  d: u64
}

Acc: type = struct {
  h: State
  n: u32
}

// A record in, a record out: the copies at the call and return go with
// the call.
step: (s: State, k: u64): State {
  out: State = s
  out.a = out.a + k
  out.b = out.b ^ out.a
  out.d = out.c + out.d
  out
}

// A record in, a scalar out.
fold: (s: State): u64 = s.a + s.b + s.c + s.d

// The chain a loop drives: the helpers fold into the loop body.
absorb: (src: []u8): u64 {
  acc: Acc
  acc.h.c = u64(1)
  acc.n = u32(0)
  i: u32 = 0
  while i < len(src) {
    acc.h = step(acc.h, u64(src[i]))
    acc.n = acc.n + u32(1)
    i = i + u32(1)
  }
  fold(acc.h) + u64(acc.n)
}

main: (): i32 {
  buf: [16]u8
  j: u32 = 0
  while j < len(buf) {
    buf[j] = u8_trunc_u32(j + u32(1))
    j = j + u32(1)
  }
  s: State
  s.c = u64(1)
  s = step(s, u64(3))
  assert(s.a == u64(3) && s.b == u64(3) && s.d == u64(1))
  assert(absorb(view(&buf)) == u64(136 + 248 + 1 + 16 + 16))
  42
}
`

func TestE2ENativeAggregateInline(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("agg_inline.oak", nativeAggregateInlineProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_aggregate_inline", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native aggregate inlining: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"step", "fold", "absorb"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_aggregate_inline_c", New().WithSource("agg_inline.oak", nativeAggregateInlineProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestNativeShapesAggregateInline(t *testing.T) {
	model, err := New().WithSource("agg_inline.oak", nativeAggregateInlineProgram).WithNativeBodies().WithNativeAsm().SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	var absorb *asm.Function
	for _, fn := range model.AsmFunctions {
		if fn.Name == "absorb" {
			absorb = fn
		}
	}
	if absorb == nil {
		t.Fatal("absorb was not lowered natively")
	}
	for _, item := range absorb.Items {
		if ins, isIns := item.(asm.Instruction); isIns && ins.Mnemonic == "bl" {
			t.Errorf("absorb must fold its helpers into its loop, but calls %s", fmt.Sprint(ins))
		}
	}
}
