package compiler

import (
	"bytes"
	"context"
	"fmt"
	"math"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/stdlib"
	"github.com/SCKelemen/oak/wasm/encoding"
)

// Keep the proof definitions mechanically tied to the assembler compiled by
// TestE2ESelfHostedWasmAssembler. No hand-maintained copy of its loops or guards.
func TestLeanWasmAssemblerExtract(t *testing.T) {
	source, err := os.ReadFile(filepath.Join("..", "asm", "selfhost", "wasm.oak"))
	if err != nil {
		t.Fatal(err)
	}
	extracted, err := New().WithSource("wasm.oak", stdlib.Prelude+"\n"+string(source)).
		EmitLeanRoots("Oak.WasmAssembler", topLevelNames(t, string(source))).Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(extracted, "sorry") {
		t.Fatal("extraction contains sorry")
	}
	path := filepath.Join("..", "spec", "lean", "Oak", "WasmAssemblerExtracted.lean")
	if os.Getenv("OAK_LEAN_EXTRACT_UPDATE") == "1" {
		if err := os.WriteFile(path, []byte(extracted), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	committed, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	if string(committed) != extracted {
		t.Fatal("WasmAssemblerExtracted.lean is stale; regenerate with OAK_LEAN_EXTRACT_UPDATE=1")
	}
}

// These claims evaluate the generated definitions in Lean's kernel (decide +kernel,
// never native_decide). The compiled-Oak tests consume the identical corpora.
// Every expected result includes all destination bytes, not only the encoding.
func TestLeanWasmAssemblerFaithful(t *testing.T) {
	lake := findLake()
	if lake == "" {
		if os.Getenv("OAK_REQUIRE_WASM_LEAN") == "1" {
			t.Fatal("OAK_REQUIRE_WASM_LEAN=1 requires lake")
		}
		t.Skip("lake unavailable; formal CI requires the extraction oracle")
	}
	root, err := filepath.Abs(filepath.Join("..", "spec", "lean"))
	if err != nil {
		t.Fatal(err)
	}
	run := func(args ...string) {
		t.Helper()
		ctx, cancel := context.WithTimeout(t.Context(), 4*time.Minute)
		defer cancel()
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = root
		if out, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("lake %v: %v\n%s", args, err, out)
		}
	}
	run("build", "Oak.WasmAssemblerLaws")
	var source strings.Builder
	const preamble = "import Oak.WasmAssemblerLaws\nopen Oak.WasmAssembler\nset_option maxRecDepth 8192\n"
	claims := 0
	pin := func(call string, want uint32, buffer []byte) {
		fmt.Fprintf(&source, "example : %s = some (%d, %s) := by decide +kernel\n", call, want, wasmLeanArray(buffer))
		claims++
	}
	for _, tc := range selfhostWasmInstructionCases() {
		var encoded []byte
		if tc.opcode <= 255 {
			encoded, _ = encoding.Assemble([]encoding.Instruction{{Opcode: byte(tc.opcode), Immediate: tc.immediate}})
		}
		ins := fmt.Sprintf("({ opcode := %d, immediate := (%d) } : WasmInstruction)", tc.opcode, tc.immediate)
		fmt.Fprintf(&source, "example : wasm_instruction_size %s 16 = some %d := by decide +kernel\n", ins, len(encoded))
		claims++
		offsets := []uint32{2, math.MaxUint32}
		if len(encoded) != 0 {
			offsets = append(offsets, uint32(17-len(encoded)))
		}
		for _, offset := range offsets {
			dst := bytes.Repeat([]byte{165}, 16)
			written := uint32(0)
			if uint64(offset)+uint64(len(encoded)) <= uint64(len(dst)) {
				copy(dst[offset:], encoded)
				written = uint32(len(encoded))
			}
			pin(fmt.Sprintf("wasm_write_instruction (Array.replicate 16 165) %d %s 16", offset, ins), written, dst)
		}
	}
	for _, v := range selfhostWasmLEBValues() {
		for _, signed := range []bool{false, true} {
			kind, value, encoded := "uleb", fmt.Sprint(v), encoding.AppendUnsigned(nil, v)
			if signed {
				kind, value, encoded = "sleb", fmt.Sprintf("(%d)", int64(v)), encoding.AppendSigned(nil, int64(v))
			}
			fmt.Fprintf(&source, "example : wasm_%s_size %s 16 = some %d := by decide +kernel\n", kind, value, len(encoded))
			claims++
			for _, offset := range []uint32{2, uint32(25 - len(encoded)), math.MaxUint32} {
				dst := bytes.Repeat([]byte{165}, 24)
				written := uint32(0)
				if uint64(offset)+uint64(len(encoded)) <= uint64(len(dst)) {
					copy(dst[offset:], encoded)
					written = uint32(len(encoded))
				}
				pin(fmt.Sprintf("wasm_write_%s (Array.replicate 24 165) %d %s 16", kind, offset, value), written, dst)
			}
		}
	}
	for _, tc := range selfhostWasmPlanCases() {
		status, size, dst := tc.expected()
		fmt.Fprintf(&source, "example : wasm_assemble (Array.replicate %d 165) %d %s 16 = some (⟨%d, %d⟩, %s) := by decide +kernel\n", tc.capacity, tc.offset, tc.leanPlan(), status, size, wasmLeanArray(dst))
		claims++
	}
	// Fuel exhaustion is distinct from an ordinary, buffer-preserving refusal.
	source.WriteString("example : wasm_assemble #[165] 0 #[] 0 = none := by decide +kernel\n")
	// Bound the kernel process's memory and timeout per batch. Each claim is
	// independent; this retains kernel checking of the complete shared corpus.
	lines := strings.Split(strings.TrimSuffix(source.String(), "\n"), "\n")
	dir := t.TempDir()
	for start := 0; start < len(lines); start += 256 {
		end := min(start+256, len(lines))
		file := filepath.Join(dir, fmt.Sprintf("WasmAssemblerFaithful%d.lean", start/256))
		if err := os.WriteFile(file, []byte(preamble+strings.Join(lines[start:end], "\n")+"\n"), 0o644); err != nil {
			t.Fatal(err)
		}
		run("env", "lean", file)
		t.Logf("kernel checked claims %d–%d of %d", start+1, end, len(lines))
	}
	t.Logf("kernel checked %d shared-corpus size, write, and transaction claims", claims+1)
}

func wasmLeanArray(b []byte) string {
	items := make([]string, len(b))
	for i, v := range b {
		items[i] = fmt.Sprint(v)
	}
	return "#[" + strings.Join(items, ",") + "]"
}
