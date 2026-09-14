package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

// The shapes the native optimization program pins (docs/spec/94-assembler.md
// §9, arrays in registers; benchmarks/kernels/RESULTS.md): a float
// accumulator lives in its register home and the operation writes it (no
// copy through a scratch register in the loop), a small array local
// indexed by literals is its elements in registers (no frame load or store
// in the loop), and a squared operand is loaded once.
const nativeShapeProgram = `dot: (a: []f32, b: []f32): f32 {
  total: f32 = 0.0
  len(a) == len(b) ? {
    i: u32 = 0
    while i < len(a) {
      total = total + a[i] * b[i]
      i = i + u32(1)
    }
  }
  total
}

tiled: (a: []f32): f32 {
  acc: [4]f32 = [4]f32{ 0.0, 0.0, 0.0, 0.0 }
  i: u32 = 0
  while len(a) >= u32(4) && i <= len(a) - u32(4) {
    acc[0] = acc[0] + a[i] * a[i]
    acc[1] = acc[1] + a[i + u32(1)] * a[i + u32(1)]
    acc[2] = acc[2] + a[i + u32(2)] * a[i + u32(2)]
    acc[3] = acc[3] + a[i + u32(3)] * a[i + u32(3)]
    i = i + u32(4)
  }
  (acc[0] + acc[1]) + (acc[2] + acc[3])
}

word_at: (chunk: []u8, at: u32): u64 {
  len(chunk) >= at + u32(8) ? {
    u64(chunk[at]) | (u64(chunk[at + u32(1)]) << u64(8)) | (u64(chunk[at + u32(2)]) << u64(16)) | (u64(chunk[at + u32(3)]) << u64(24)) |
      (u64(chunk[at + u32(4)]) << u64(32)) | (u64(chunk[at + u32(5)]) << u64(40)) | (u64(chunk[at + u32(6)]) << u64(48)) | (u64(chunk[at + u32(7)]) << u64(56))
  } | { u64(0) }
}

main: (): i32 {
  xs: [8]f32 = [8]f32{ 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0 }
  d: f32 = dot(view(&xs), view(&xs))
  t: f32 = tiled(view(&xs))
  d == t ? 42 | 1
}
`

// loopBody returns the instructions between the first label starting with
// "loop" and the next label of the unit.
func loopBody(fn *asm.Function) []asm.Instruction {
	var body []asm.Instruction
	inLoop := false
	for _, item := range fn.Items {
		switch it := item.(type) {
		case asm.Label:
			if inLoop {
				return body
			}
			inLoop = strings.HasPrefix(it.Name, "loop")
		case asm.Instruction:
			if inLoop {
				body = append(body, it)
			}
		}
	}
	return body
}

func TestNativeShapesRegistersInLoops(t *testing.T) {
	model, err := New().WithSource("shape.oak", nativeShapeProgram).WithNativeBodies().WithNativeAsm().SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	units := map[string]*asm.Function{}
	for _, fn := range model.AsmFunctions {
		units[fn.Name] = fn
	}
	dot, ok := units["dot"]
	if !ok {
		t.Fatal("dot was not lowered natively")
	}
	fadds := 0
	for _, ins := range loopBody(dot) {
		if ins.Mnemonic == "fmov" {
			t.Errorf("dot's loop copies through a scratch register: %s", fmt.Sprint(ins))
		}
		if ins.Mnemonic == "fadd" {
			fadds++
			if dst, isReg := ins.Operands[0].(asm.Register); !isReg || dst.Text != "s8" {
				t.Errorf("dot's fadd must write the accumulator's home s8: %s", fmt.Sprint(ins))
			}
		}
	}
	if fadds != 1 {
		t.Errorf("dot's loop must hold one fadd, got %d", fadds)
	}
	tiled, ok := units["tiled"]
	if !ok {
		t.Fatal("tiled was not lowered natively")
	}
	fmuls := 0
	for _, ins := range loopBody(tiled) {
		if ins.Mnemonic == "ldr" || ins.Mnemonic == "str" {
			if mem, isMem := ins.Operands[len(ins.Operands)-1].(asm.Memory); isMem && mem.Base.Class == asm.ClassSP {
				t.Errorf("tiled's accumulators must live in registers, not frame slots: %s", fmt.Sprint(ins))
			}
		}
		if ins.Mnemonic == "fmul" {
			fmuls++
			l, r := ins.Operands[1].(asm.Register), ins.Operands[2].(asm.Register)
			if l.Text != r.Text {
				t.Errorf("a square must be loaded once and multiplied by itself: %s", fmt.Sprint(ins))
			}
		}
	}
	if fmuls != 4 {
		t.Errorf("tiled's loop must hold four multiplications, got %d", fmuls)
	}
	// The little-endian word assembly is one wide load (nativegen/word_fusion.go).
	word, ok := units["word_at"]
	if !ok {
		t.Fatal("word_at was not lowered natively")
	}
	loads, wide := 0, 0
	for _, item := range word.Items {
		ins, isIns := item.(asm.Instruction)
		if !isIns {
			continue
		}
		switch ins.Mnemonic {
		case "ldrb":
			loads++
		case "ldr":
			if dst, isReg := ins.Operands[0].(asm.Register); isReg && dst.Class == asm.ClassX {
				wide++
			}
		}
	}
	if loads != 0 || wide != 1 {
		t.Errorf("word_at must load its word once (%d byte loads, %d wide loads)", loads, wide)
	}
	if !strings.Contains(model.NativeVerdicts["word_at"].Message, "proven") {
		t.Errorf("word_at's fused load must stay proven: %s", model.NativeVerdicts["word_at"].Message)
	}
}
