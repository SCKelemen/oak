package encoding_test

import (
	"context"
	"fmt"
	"math"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/wasm/check"
	"github.com/SCKelemen/oak/wasm/encoding"
)

// Kernel-checked finite production/model correspondence, separate from the
// universal Lean operand-family and prefix theorems. No native_decide is used.
func TestWasmEncodingMatchesLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_WASM_LEAN") == "1" {
			t.Fatal("OAK_REQUIRE_WASM_LEAN=1 requires lake")
		}
		t.Skip("lake unavailable; formal CI requires this oracle")
	}
	root, err := filepath.Abs(filepath.Join("..", "..", "spec", "lean"))
	if err != nil {
		t.Fatal(err)
	}
	run := func(args ...string) {
		t.Helper()
		ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
		defer cancel()
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = root
		if out, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("lake %v: %v\n%s", args, err, out)
		}
	}
	run("build", "Oak.WasmInstruction", "Oak.Target")
	list := func(data []byte) string {
		items := make([]string, len(data))
		for i, b := range data {
			items[i] = fmt.Sprint(b)
		}
		return "[" + strings.Join(items, ",") + "]"
	}
	var s strings.Builder
	s.WriteString("import Oak.WasmInstruction\nimport Oak.Target\nset_option maxRecDepth 4096\n")
	claims := 0
	pin := func(ins encoding.Instruction) {
		b, err := encoding.Assemble([]encoding.Instruction{ins})
		fmt.Fprintf(&s, "example : Oak.WasmInstruction.encode %d (%d) = ", ins.Opcode, ins.Immediate)
		if err != nil {
			s.WriteString("none := by decide\n")
		} else {
			fmt.Fprintf(&s, "some %s := by simp [Oak.WasmInstruction.encode, Oak.WasmInstruction.kind, Oak.WasmInstruction.blockType, Oak.WasmEncoding.encode, Oak.WasmEncoding.terminal, Oak.WasmLEB.inRange]\n", list(b))
			// Decode actual production bytes with an adversarial suffix.
			data := append(append([]byte{}, b...), 255, 66)
			decoded, n, err := check.DecodeInstruction(data)
			if err != nil {
				t.Fatal(err)
			}
			fmt.Fprintf(&s, "example : Oak.WasmInstruction.decode %s = some ((%d, (%d)), %s) := by decide\n", list(data), decoded.Opcode, decoded.Immediate, list(data[n:]))
			claims++
		}
		claims++
	}
	for op := 0; op < 256; op++ {
		for _, v := range []int64{-1, 0, 64, 127, 128} {
			pin(encoding.Instruction{Opcode: byte(op), Immediate: v})
		}
	}
	for _, op := range []byte{0x0c, 0x0d, 0x10, 0x20, 0x21, 0x22, 0x41, 0x42} {
		for _, v := range []int64{math.MinInt64, math.MinInt32 - 1, math.MinInt32, -8193, -8192, -65, -64, 63, 8191, 8192, math.MaxInt32, math.MaxInt32 + 1, math.MaxUint32, math.MaxUint32 + 1, math.MaxInt64} {
			pin(encoding.Instruction{Opcode: op, Immediate: v})
		}
	}
	// Every 7-bit transition and both full-width signed/unsigned endpoints.
	for shift := uint(0); shift < 64; shift++ {
		for _, v := range []uint64{1<<shift - 1, 1 << shift, ^uint64(0) - (1<<shift - 1)} {
			fmt.Fprintf(&s, "example : Oak.WasmEncoding.encode 64 false %d = %s := by simp [Oak.WasmEncoding.encode, Oak.WasmEncoding.terminal]\n", v, list(encoding.AppendUnsigned(nil, v)))
			fmt.Fprintf(&s, "example : Oak.WasmEncoding.encode 64 true (%d) = %s := by simp [Oak.WasmEncoding.encode, Oak.WasmEncoding.terminal]\n", int64(v), list(encoding.AppendSigned(nil, int64(v))))
			claims += 2
		}
	}
	for _, data := range [][]byte{
		nil, {0xff}, {0x04, 0}, {0x41, 0xff, 0x7f, 0x42}, {0x20, 0x80, 0, 0xff},
		{0x41, 0xff, 0xff, 0xff, 0xff, 0x0f}, {0x20, 0xff, 0xff, 0xff, 0xff, 0x10},
		{0x42, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 1},
	} {
		i, n, err := check.DecodeInstruction(data)
		fmt.Fprintf(&s, "example : Oak.WasmInstruction.decode %s = ", list(data))
		if err != nil {
			s.WriteString("none := by decide\n")
		} else {
			fmt.Fprintf(&s, "some ((%d, (%d)), %s) := by decide\n", i.Opcode, i.Immediate, list(data[n:]))
		}
		claims++
	}
	// Exhaust the target universe, including unsupported cross-pairings.
	for _, osName := range []string{"linux", "darwin", "freestanding", "core"} {
		for _, arch := range []string{"arm64", "amd64", "riscv64", "arm", "riscv32", "wasm32"} {
			targetValue := target.Target{OS: osName, Arch: arch}
			_, ptr := targetValue.DataModel()
			fmt.Fprintf(&s, "example : Oak.Target.supported ⟨.%s, .%s⟩ = %t := by decide\n", osName, arch, targetValue.Supported())
			fmt.Fprintf(&s, "example : (Oak.Target.dataModel ⟨.%s, .%s⟩).ptrBits = %d := by decide\n", osName, arch, ptr)
			lane := "none"
			if targetValue.AsmArch() != "" {
				lane = "some ." + targetValue.AsmArch()
			}
			fmt.Fprintf(&s, "example : Oak.Target.lane ⟨.%s, .%s⟩ = %s := by decide\n", osName, arch, lane)
			claims += 3
		}
	}

	path := filepath.Join(t.TempDir(), "WasmEncodingProduction.lean")
	if err := os.WriteFile(path, []byte(s.String()), 0600); err != nil {
		t.Fatal(err)
	}
	run("env", "lean", path)
	t.Logf("kernel checked %d production encoder/decoder claims", claims)
}
