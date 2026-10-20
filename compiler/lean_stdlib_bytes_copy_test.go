package compiler

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// A shared corpus relates the extracted copy functions to compiled and
// interpreted Oak through an independent Go copy oracle. It is evidence for
// compiler/extractor correspondence, not an implementation-refinement proof.
// Every case checks the entire destination and the unchanged source. Empty
// logical arrays use a one-byte backing allocation, also checked unchanged.
type bytesCopyCase struct {
	at     bool
	dst    []byte
	src    []byte
	offset uint32
}

func bytesCopyCases() []bytesCopyCase {
	var cases []bytesCopyCase
	for _, dstLen := range []int{0, 1, 2, 4, 8} {
		for _, srcLen := range []int{0, 1, 2, 3, 8, 9} {
			dst, src := make([]byte, dstLen), make([]byte, srcLen)
			for i := range dst {
				dst[i] = byte(101 + i*17)
			}
			for i := range src {
				src[i] = byte(255 - i*31)
			}
			cases = append(cases, bytesCopyCase{dst: dst, src: src})
			seen := map[uint32]bool{}
			for _, offset := range []uint32{0, 1, uint32(dstLen / 2), uint32(dstLen), uint32(dstLen + 1), ^uint32(0)} {
				if !seen[offset] {
					cases = append(cases, bytesCopyCase{at: true, dst: dst, src: src, offset: offset})
					seen[offset] = true
				}
			}
		}
	}
	return cases
}

func (c bytesCopyCase) expected() ([]byte, bool) {
	out := append([]byte(nil), c.dst...)
	// Widen before adding: this reference must reject wrapped offsets.
	fits := uint64(c.offset)+uint64(len(c.src)) <= uint64(len(c.dst))
	if fits {
		copy(out[int(c.offset):], c.src)
	}
	return out, fits
}

func bytesCopyOakProgram(cases []bytesCopyCase) string {
	var b strings.Builder
	b.WriteString("package main\nimport(\"bytes\")\n")
	for i, c := range cases {
		dst, src := c.dst, c.src
		if len(dst) == 0 {
			dst = []byte{173}
		}
		if len(src) == 0 {
			src = []byte{219}
		}
		fmt.Fprintf(&b, "check_%d: (): () {\n  dst: [%d]u8 = %s\n  src: [%d]u8 = %s\n", i, len(dst), oakU8Array(dst), len(src), oakU8Array(src))
		operation, errorType, args := "copy_into", "CopyError", ""
		if c.at {
			operation, errorType, args = "copy_at", "RangeError", fmt.Sprintf("u32(%d), ", c.offset)
		}
		fmt.Fprintf(&b, "  result: Result[u32, bytes.%s] = bytes.%s(span(&dst)[u32(0):u32(%d)], %sview(&src)[u32(0):u32(%d)])\n", errorType, operation, len(c.dst), args, len(c.src))
		expected, fits := c.expected()
		want := uint32(len(c.src))
		if !fits {
			want = ^uint32(0)
		}
		fmt.Fprintf(&b, "  count: u32 = result ? | .Ok(n) => n | .Err(e) => u32(4294967295)\n  assert(count == u32(%d))\n", want)
		if len(expected) == 0 {
			expected = []byte{173}
		}
		for j, v := range expected {
			fmt.Fprintf(&b, "  assert(dst[%d] == u8(%d))\n", j, v)
		}
		for j, v := range src {
			fmt.Fprintf(&b, "  assert(src[%d] == u8(%d))\n", j, v)
		}
		b.WriteString("}\n")
	}
	b.WriteString("main: (): i32 {\n")
	for i := range cases {
		fmt.Fprintf(&b, "  check_%d()\n", i)
	}
	b.WriteString("  42\n}\n")
	return b.String()
}

func bytesCopyLeanProgram(cases []bytesCopyCase) string {
	var b strings.Builder
	b.WriteString("import Oak.Stdlib.BytesLaws\nopen Oak.Stdlib.Bytes\n")
	for i, c := range cases {
		operation, args, failure := "copy_into", "", ".DestinationTooSmall"
		if c.at {
			operation, args, failure = "copy_at", fmt.Sprintf("(%d : UInt32) ", c.offset), ".OutOfBounds"
		}
		expected, fits := c.expected()
		result := fmt.Sprintf(".Err %s", failure)
		if fits {
			result = fmt.Sprintf(".Ok %d", len(c.src))
		}
		fmt.Fprintf(&b, "-- Case %d: full result and destination, at minimum and surplus fuel.\n", i)
		for _, fuel := range []int{len(c.src) + 1, len(c.src) + 5} {
			fmt.Fprintf(&b, "example : %s %s %s%s %d = some (%s, %s) := by decide +kernel\n", operation, leanU8Array(c.dst), args, leanU8Array(c.src), fuel, result, leanU8Array(expected))
		}
		if fits {
			// Even empty successful copies need the final guard step.
			fmt.Fprintf(&b, "example : %s %s %s%s %d = none := by decide +kernel\n", operation, leanU8Array(c.dst), args, leanU8Array(c.src), len(c.src))
		} else {
			fmt.Fprintf(&b, "example : %s %s %s%s 0 = some (%s, %s) := by decide +kernel\n", operation, leanU8Array(c.dst), args, leanU8Array(c.src), result, leanU8Array(expected))
		}
	}
	return b.String()
}

func TestE2EStdlibBytesCopyFrames(t *testing.T) {
	cases := bytesCopyCases()
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/bytes-copy-frames\noak 0.1.0\n",
		"main.oak": bytesCopyOakProgram(cases),
	})
	comp := New().WithPackageDir(root)
	code, abnormal := buildPackageAndRun(t, comp)
	if abnormal || code != 42 {
		t.Fatalf("compiled copy corpus exited (%d, abnormal=%v)", code, abnormal)
	}
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	env := object.NewEnvironment()
	env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
	if result := evaluator.Eval(model.Tree.Root, env); result != nil {
		if evalErr, ok := result.(*object.Error); ok {
			t.Fatalf("interpreter setup: %s", evalErr.Message)
		}
	}
	call := parser.New(layout.New(scanner.New("main()"))).ParseProgram()
	result := evaluator.Eval(call, env)
	integer, ok := result.(*object.Integer)
	if !ok || integer.Value != 42 {
		t.Fatalf("interpreted copy corpus returned %v", result)
	}
	t.Logf("%d copy cases passed in compiled and interpreted Oak", len(cases))
}

func TestLeanStdlibBytesCopyCorrespondence(t *testing.T) {
	lake := findLake()
	if lake == "" {
		if os.Getenv("OAK_REQUIRE_BYTES_COPY_LEAN") == "1" {
			t.Fatal("lake not found, but OAK_REQUIRE_BYTES_COPY_LEAN=1 requires extracted-copy correspondence")
		}
		t.Skip("lake not found; extracted-copy correspondence needs the pinned Lean toolchain")
	}
	root, err := filepath.Abs(filepath.Join("..", "spec", "lean"))
	if err != nil {
		t.Fatal(err)
	}
	// Build only this proof family and its extracted dependency, never the
	// entire specification library for this focused correspondence check.
	build := exec.Command(lake, "build", "Oak.Stdlib.BytesLaws")
	build.Dir = root
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("focused Lean build: %v\n%s", err, out)
	}
	cases := bytesCopyCases()
	driver := filepath.Join(t.TempDir(), "BytesCopyCorrespondence.lean")
	if err := os.WriteFile(driver, []byte(bytesCopyLeanProgram(cases)), 0o644); err != nil {
		t.Fatal(err)
	}
	run := exec.Command(lake, "env", "lean", driver)
	run.Dir = root
	if out, err := run.CombinedOutput(); err != nil {
		t.Fatalf("extracted copy corpus: %v\n%s", err, out)
	}
	t.Logf("%d copy cases passed in the Lean kernel at three fuel boundaries", len(cases))
}
