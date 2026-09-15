package asm

import (
	"strconv"
	"strings"
	"testing"
)

// The two paths of a forward fork meet at the fork's immediate
// post-dominator (joinPoints); the executor parks each side's state there
// and merges them into one continuation (mergeStates), so a chain of
// diamonds unfolds linearly rather than as 2^n paths. Twelve diamonds
// exceeded the path budget of 256 before; now the body is proven, and a
// wrong arm is still refuted.
func TestVerifyJoinsMergeDiamonds(t *testing.T) {
	const n = 12
	var asmBody, oakBody strings.Builder
	asmBody.WriteString("  bind w0 = a\n  clobber x9, x10\n  mov w9, #0\n")
	oakBody.WriteString("{\n  acc: u32 = u32(0)\n")
	for k := 0; k < n; k++ {
		asmBody.WriteString("  and w10, w0, #" + strconv.Itoa(1<<uint(k)) + "\n  cbz w10, skip_" + strconv.Itoa(k) + "\n  add w9, w9, #" + strconv.Itoa(k+1) + "\nskip_" + strconv.Itoa(k) + ":\n")
		oakBody.WriteString("  (a & u32(" + strconv.Itoa(1<<uint(k)) + ")) != u32(0) ? { acc = acc + u32(" + strconv.Itoa(k+1) + ") } | { }\n")
	}
	asmBody.WriteString("  mov w0, w9\n  ret")
	oakBody.WriteString("  acc\n}")
	proven := verifyCase(t, "bit_weights: (a: u32) -> u32", oakBody.String(), asmBody.String())
	if proven.Kind != VerdictProven {
		t.Fatalf("twelve diamonds must be proven through their joins, got %s: %s", proven.Kind, proven.Message)
	}
	wrongAsm := strings.Replace(asmBody.String(), "add w9, w9, #7\n", "add w9, w9, #8\n", 1)
	wrong := verifyCase(t, "bit_weights: (a: u32) -> u32", oakBody.String(), wrongAsm)
	if wrong.Kind != VerdictMismatch {
		t.Fatalf("a wrong arm among twelve diamonds must be refuted, got %s: %s", wrong.Kind, wrong.Message)
	}
}
