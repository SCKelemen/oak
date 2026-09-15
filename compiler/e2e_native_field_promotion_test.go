package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

// Record fields in registers (docs/spec/94-assembler.md §9): the scalar
// fields of a record local that a loop reads or writes live in
// callee-saved registers, written back to the record's memory where the
// record is used whole and reloaded where it is written whole. The byte
// loop of a SHA-256-style absorber then touches no memory for `filled` or
// `blocks`. The C backend's realization of the same program is the oracle.
const nativeFieldPromotionProgram = `
Acc: type = struct {
  filled: u32
  blocks: u32
  total: u64
  block: [64]u8
}

digest: (a: Acc): u64 = u64(a.blocks) * u64(1000) + u64(a.filled) + a.total

feed: (src: []u8): u64 {
  a: Acc
  a.filled = u32(0)
  a.blocks = u32(0)
  a.total = u64(0)
  i: u32 = 0
  while i < len(src) {
    a.filled < u32(64) ? {
      a.block[a.filled] = src[i]
    }
    a.filled = a.filled + u32(1)
    a.total = a.total + u64(src[i])
    a.filled == u32(64) ? {
      a.blocks = a.blocks + u32(1)
      a.filled = u32(0)
    }
    i = i + u32(1)
  }
  digest(a)
}

// A record assigned whole inside the loop: the homes reload after it.
reset_each: (src: []u8, seed: Acc): u32 {
  a: Acc = seed
  i: u32 = 0
  while i < len(src) {
    a.filled = a.filled + u32(src[i])
    a.filled > u32(100) ? {
      a = seed
    }
    i = i + u32(1)
  }
  a.filled
}

main: (): i32 {
  buf: [200]u8
  j: u32 = 0
  while j < len(buf) {
    buf[j] = u8_trunc_u32(j)
    j = j + u32(1)
  }
  assert(feed(view(&buf)) == u64(3 * 1000 + 8 + 19900))
  assert(feed(view(&buf)[u32(0):u32(64)]) == u64(1000 + 2016))
  seed: Acc
  seed.filled = u32(7)
  assert(reset_each(view(&buf)[u32(0):u32(20)], seed) == u32(92))
  42
}
`

func TestE2ENativeFieldPromotion(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("fields.oak", nativeFieldPromotionProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_field_promotion", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native field promotion: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"feed", "reset_each", "digest"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_field_promotion_c", New().WithSource("fields.oak", nativeFieldPromotionProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestNativeShapesFieldPromotion(t *testing.T) {
	model, err := New().WithSource("fields.oak", nativeFieldPromotionProgram).WithNativeBodies().WithNativeAsm().SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	var feed *asm.Function
	for _, fn := range model.AsmFunctions {
		if fn.Name == "feed" {
			feed = fn
		}
	}
	if feed == nil {
		t.Fatal("feed was not lowered natively")
	}
	// The loop, from its label to the label that ends it.
	var body []asm.Instruction
	inLoop := false
	for _, item := range feed.Items {
		switch it := item.(type) {
		case asm.Label:
			if strings.HasPrefix(it.Name, "loop") {
				inLoop = true
			} else if strings.HasPrefix(it.Name, "done") && inLoop {
				inLoop = false
			}
		case asm.Instruction:
			if inLoop {
				body = append(body, it)
			}
		}
	}
	// filled, blocks, and total live in registers: the loop's only memory
	// operations are the byte load from the view and the byte store into
	// the block.
	for _, ins := range body {
		switch ins.Mnemonic {
		case "ldr", "str", "ldrh", "strh", "ldp", "stp":
			t.Errorf("the loop touches memory for a promoted field: %s\n%s", fmt.Sprint(ins), fmt.Sprint(body))
		}
	}
}
