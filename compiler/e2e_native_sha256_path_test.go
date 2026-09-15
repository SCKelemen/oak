package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

// The SHA-256 path's two remaining gaps (docs/spec/94-assembler.md §9): a
// record built in the result area and copied by pairs inside a loop — the
// pair loads through the parked result register are frame memory to the
// verifier, so the body stays verifiable — and a loop's record fields that
// keep their register homes when the loop invariants had reserved the
// callee-saved registers first. The C backend's realization is the oracle.
const nativeSha256PathProgram = `
Acc: type = struct {
  h: [4]u64
  filled: u32
  blocks: u32
}

bump: (h: [4]u64, k: u64): [4]u64 {
  out: [4]u64 = h
  out[0] = out[0] + k
  out[3] = out[3] ^ out[0]
  out
}

step: (v: []u8): u32 {
  s: u32 = 0
  i: u32 = 0
  while i < len(v) {
    s = s + u32(v[i])
    i = i + u32(1)
  }
  s
}

// The accumulator is the result area; its h copies by pairs through the
// parked result register in the loop; its filled and blocks are homes.
absorb: (src: []u8, seed: Acc): Acc {
  acc: Acc = seed
  scale: u32 = len(src) * u32(3) + u32(1)
  i: u32 = 0
  while i < len(src) {
    acc.filled = acc.filled + step(src) * scale
    acc.filled >= u32(64) ? {
      acc.h = bump(acc.h, u64(acc.filled))
      acc.blocks = acc.blocks + u32(1)
      acc.filled = u32(0)
    }
    i = i + u32(1)
  }
  acc
}

main: (): i32 {
  buf: [8]u8
  j: u32 = 0
  while j < len(buf) {
    buf[j] = u8_trunc_u32(j + u32(1))
    j = j + u32(1)
  }
  seed: Acc
  seed.h[3] = u64(7)
  out: Acc = absorb(view(&buf), seed)
  assert(out.blocks == u32(8))
  assert(out.filled == u32(0))
  assert(out.h[0] == u64(8 * 900))
  42
}
`

func TestE2ENativeSha256Path(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("sha_path.oak", nativeSha256PathProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_sha_path", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native SHA-256 path: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit absorb:") {
		t.Fatalf("absorb was not lowered by the native backend; diagnostics:\n%s", joined)
	}
	if strings.Contains(joined, "not a span base") {
		t.Errorf("absorb's pair copies through the result register must be frame memory to the verifier; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_sha_path_c", New().WithSource("sha_path.oak", nativeSha256PathProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestNativeShapesSha256Path(t *testing.T) {
	model, err := New().WithSource("sha_path.oak", nativeSha256PathProgram).WithNativeBodies().WithNativeAsm().SemanticModel().Get()
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
	// filled and blocks stay in registers: no 32-bit load or store
	// through the result register's word offsets inside the loop, only
	// the pair copies of h and the call.
	inLoop := false
	for _, item := range absorb.Items {
		switch it := item.(type) {
		case asm.Label:
			if strings.HasPrefix(it.Name, "loop") {
				inLoop = true
			} else if strings.HasPrefix(it.Name, "done") {
				inLoop = false
			}
		case asm.Instruction:
			if inLoop && (it.Mnemonic == "ldr" || it.Mnemonic == "str") {
				if r, isReg := it.Operands[0].(asm.Register); isReg && r.Class == asm.ClassW {
					if mem, isMem := it.Operands[1].(asm.Memory); isMem && mem.Base.Class != asm.ClassSP {
						t.Errorf("a promoted field is read or written in memory inside the loop: %s\n%s", fmt.Sprint(it), fmt.Sprint(absorb.Items))
					}
				}
			}
		}
	}
}
