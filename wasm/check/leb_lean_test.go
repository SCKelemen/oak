package check

import (
	"bytes"
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// These are finite production-to-model pins, not a universal refinement of
// Go's uint64 accumulator or mutable reader. Lean checks ordinary `by decide`
// proofs in its kernel, including the actual success cursor and signed word.
func TestWasmLEBMatchesLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_WASM_LEAN") == "1" {
			t.Fatal("OAK_REQUIRE_WASM_LEAN=1 requires lake on PATH")
		}
		t.Skip("lake unavailable; formal CI requires this oracle")
	}
	leanRoot, err := filepath.Abs(filepath.Join("..", "..", "spec", "lean"))
	if err != nil {
		t.Fatal(err)
	}
	run := func(args ...string) {
		t.Helper()
		ctx, cancel := context.WithTimeout(t.Context(), 2*time.Minute)
		defer cancel()
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = leanRoot
		if output, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("lake %v: %v\n%s", args, err, output)
		}
	}
	run("build", "Oak.WasmLEB")

	var source strings.Builder
	source.WriteString("import Oak.WasmLEB\nopen Oak.WasmLEB\n")
	cases, accepted, refused := 0, 0, 0
	pin := func(width uint, signed bool, data []byte) {
		r := reader{data: data}
		word := r.integer(width, signed)
		fmt.Fprintf(&source, "example : decodeWord %d %t [", width, signed)
		for i, b := range data {
			if i > 0 {
				source.WriteString(", ")
			}
			fmt.Fprintf(&source, "%d", b)
		}
		if r.err != nil {
			// Error offsets/partial values are intentionally not modeled.
			source.WriteString("] = none := by decide\n")
			refused++
		} else {
			if r.pos < 1 || r.pos > int((width+6)/7) || r.pos > len(data) {
				t.Fatalf("invalid success cursor for %x: %d", data, r.pos)
			}
			fmt.Fprintf(&source, "] = some (%d, %d) := by decide\n", word, r.pos)
			accepted++
		}
		cases++
	}
	for _, mode := range []struct {
		width  uint
		signed bool
	}{{32, false}, {32, true}, {64, true}} {
		maxBytes := int((mode.width + 6) / 7)
		for b := 0; b < 256; b++ {
			pin(mode.width, mode.signed, []byte{byte(b)})
			// Every final byte at the maximum-width boundary, with zero and
			// all-one preceding payloads. A trailing valid integer must not
			// repair an overlong encoding or be consumed after a legal one.
			for _, fill := range []byte{0x80, 0xff} {
				data := bytes.Repeat([]byte{fill}, maxBytes-1)
				data = append(data, byte(b), 0x42, 0xff)
				pin(mode.width, mode.signed, data)
			}
		}
		for n := 0; n <= maxBytes; n++ {
			pin(mode.width, mode.signed, bytes.Repeat([]byte{0x80}, n))
			for _, last := range []byte{0, 0x3f, 0x40, 0x7f} {
				data := bytes.Repeat([]byte{0x81}, n)
				data = append(data, last, 0x42)
				pin(mode.width, mode.signed, data)
			}
		}
		for _, data := range [][]byte{
			{0xe5, 0x8e, 0x26}, // 624485
			{0x9b, 0xf1, 0x59}, // -624485 (signed)
			{0xff, 0xff, 0xff, 0xff, 0x07},
			{0x80, 0x80, 0x80, 0x80, 0x78},
			{0xfe, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x00},
		} {
			pin(mode.width, mode.signed, data)
		}
	}
	if cases == 0 || accepted == 0 || refused == 0 {
		t.Fatal("oracle must cover successes and refusals")
	}
	path := filepath.Join(t.TempDir(), "WasmLEBProductionPins.lean")
	if err := os.WriteFile(path, []byte(source.String()), 0o600); err != nil {
		t.Fatal(err)
	}
	run("env", "lean", path)
	t.Logf("kernel checked %d production LEB outcomes (%d accepted, %d refused)", cases, accepted, refused)
}
