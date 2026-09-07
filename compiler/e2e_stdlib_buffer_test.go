package compiler

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"
)

func TestE2EStdlibByteMoves(t *testing.T) {
	// Exhaust every valid source/destination/count, including both overlap
	// directions, identity and zero-length ranges. Go copy is the oracle.
	for _, size := range []int{1, 5} {
		var src strings.Builder
		src.WriteString("import(std)\nmain: (): i32 {\ndata: [5]u8\ns: [*]u8 = span(&data)\n")
		for from := 0; from <= size; from++ {
			for to := 0; to <= size; to++ {
				for n := 0; n <= size-from && n <= size-to; n++ {
					model := []byte{1, 2, 3, 4, 5}
					src.WriteString("true ? {\n")
					for i, b := range model {
						fmt.Fprintf(&src, "s[%d] = u8(%d)\n", i, b)
					}
					copy(model[to:to+n], model[from:from+n])
					fmt.Fprintf(&src, "r: Result[u32, ByteRangeError] = bytes_move_within(s, u32(%d), u32(%d), u32(%d))\nok: Bool = r ? | .Ok(v) => v == u32(%d) | .Err(e) => false\nassert(ok)\n", to, from, n, n)
					for i, b := range model {
						fmt.Fprintf(&src, "assert(s[%d] == u8(%d))\n", i, b)
					}
					src.WriteString("}\n")
				}
			}
		}
		for _, bounds := range [][3]uint32{{5, 0, 1}, {0, 5, 1}, {6, 0, 0}, {0, 6, 0}, {0, 0, ^uint32(0)}, {^uint32(0), 0, 1}} {
			fmt.Fprintf(&src, "true ? {\nbytes_fill(s, u8(91))\nr: Result[u32, ByteRangeError] = bytes_move_within(s, u32(%d), u32(%d), u32(%d))\nok: Bool = r ? | .Ok(v) => false | .Err(e) => true\nassert(ok)\n", bounds[0], bounds[1], bounds[2])
			for i := 0; i < 5; i++ {
				fmt.Fprintf(&src, "assert(s[%d] == u8(91))\n", i)
			}
			src.WriteString("}\n")
		}
		src.WriteString("42\n}\n")
		code, abnormal := buildAndRun(t, "bytemoves", src.String())
		if abnormal || code != 42 {
			t.Fatalf("exit=(%d,%v)", code, abnormal)
		}
	}
}

func TestE2EStdlibByteCopyCompare(t *testing.T) {
	src := `
import(std)
main: (): i32 {
 input: [2]u8
 input[0] = u8(128)
 input[1] = u8(255)
 longer: [3]u8
 longer[0] = u8(128)
 longer[1] = u8(255)
 lower: [2]u8
 lower[0] = u8(127)
 v: []u8 = view(&input)
 w: []u8 = view(&longer)
 low: []u8 = view(&lower)
 assert(bytes_compare(v, v) == 0)
 assert(bytes_compare(v, w) == -1)
 assert(bytes_compare(w, v) == 1)
 assert(bytes_compare(v, low) == 1)
 assert(bytes_compare(low, v) == -1)
 output: [4]u8
 s: [*]u8 = span(&output)
 bytes_fill(s, u8(77))
 r: Result[u32, ByteRangeError] = bytes_copy_at(s, u32(2), v)
 ok: Bool = r ? | .Ok(n) => n == u32(2) | .Err(e) => false
 assert(ok && s[0] == u8(77) && s[1] == u8(77) && s[2] == u8(128) && s[3] == u8(255))
 bad: Result[u32, ByteRangeError] = bytes_copy_at(s, u32(3), v)
 rejected: Bool = bad ? | .Ok(n) => false | .Err(e) => true
 assert(rejected && s[3] == u8(255))
 overflow: Result[u32, ByteRangeError] = bytes_copy_at(s, u32(4294967295), v)
 rejected2: Bool = overflow ? | .Ok(n) => false | .Err(e) => true
 assert(rejected2 && s[0] == u8(77) && s[1] == u8(77) && s[2] == u8(128) && s[3] == u8(255))
 42
}
`
	code, abnormal := buildAndRun(t, "copycompare", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EStdlibBufferTrace(t *testing.T) {
	for _, capacity := range []int{1, 4, 9} {
		t.Run(fmt.Sprint(capacity), func(t *testing.T) {
			var src strings.Builder
			fmt.Fprintf(&src, "import(std)\nmain: (): i32 {\ndata: [%d]u8\nstate: [1]ByteBufferCursor\nq: [*]ByteBufferCursor = span(&state)\n", capacity)
			model := make([]byte, capacity)
			start, end := 0, 0
			seed := uint32(100)
			for step := 0; step < 120; step++ {
				seed = seed*1664525 + 1013904223
				op := seed >> 28
				n := int((seed >> 8) % 4) + 1
				src.WriteString("true ? {\n")
				switch {
				case op < 7:
					fmt.Fprintf(&src, "input: [%d]u8\n", n)
					value := byte(seed >> 16)
					for i := 0; i < n; i++ {
						fmt.Fprintf(&src, "input[%d] = u8(%d)\n", i, value)
					}
					src.WriteString("v: []u8 = view(&input)\ns: [*]u8 = span(&data)\n")
					fmt.Fprintf(&src, "r: Result[u32, BufferError] = buffer_append(q, s, v)\nok: Bool = r ? | .Ok(v) => true | .Err(e) => false\nassert(ok == %t)\n", n <= capacity-end)
					if n <= capacity-end {
						for i := 0; i < n; i++ {
							model[end+i] = value
						}
						end += n
					}
				case op < 11:
					fmt.Fprintf(&src, "out: [%d]u8\nd: [*]u8 = span(&out)\nbytes_fill(d, u8(231))\nv: []u8 = view(&data)\n", n)
					name := "buffer_read_into"
					if op == 10 {
						name = "buffer_peek_into"
					}
					fmt.Fprintf(&src, "r: Result[u32, BufferError] = %s(q, v, d)\nok: Bool = r ? | .Ok(v) => v == u32(%d) | .Err(e) => false\nassert(ok == %t)\n", name, n, n <= end-start)
					for i := 0; i < n; i++ {
						expected := byte(231)
						if n <= end-start {
							expected = model[start+i]
						}
						fmt.Fprintf(&src, "assert(d[%d] == u8(%d))\n", i, expected)
					}
					if n <= end-start && name == "buffer_read_into" {
						start += n
						if start == end {
							start, end = 0, 0
						}
					}
				case op < 13:
					fmt.Fprintf(&src, "r: Result[u32, BufferError] = buffer_consume(q, u32(%d), u32(%d))\nok: Bool = r ? | .Ok(v) => true | .Err(e) => false\nassert(ok == %t)\n", capacity, n, n <= end-start)
					if n <= end-start {
						start += n
						if start == end {
							start, end = 0, 0
						}
					}
				case op < 15:
					src.WriteString("s: [*]u8 = span(&data)\n")
					fmt.Fprintf(&src, "assert(buffer_compact(q, s) == u32(%d))\n", end-start)
					copy(model, model[start:end])
					end -= start
					start = 0
				default:
					src.WriteString("buffer_reset(q)\n")
					start, end = 0, 0
				}
				src.WriteString("}\n")
				fmt.Fprintf(&src, "assert(q[0].start == u32(%d) && q[0].end == u32(%d))\nassert(buffer_len(q, u32(%d)) == u32(%d))\nassert(buffer_tail_space(q, u32(%d)) == u32(%d))\n", start, end, capacity, end-start, capacity, capacity-end)
				for i, b := range model {
					fmt.Fprintf(&src, "assert(data[%d] == u8(%d))\n", i, b)
				}
			}
			src.WriteString("42\n}\n")
			code, abnormal := buildAndRun(t, "buffertrace", src.String())
			if abnormal || code != 42 {
				t.Fatalf("exit=(%d,%v)", code, abnormal)
			}
		})
	}
}

func TestE2EStdlibBufferRejectsInvalidCursor(t *testing.T) {
	for _, state := range []string{"q[0].start = u32(1)", "q[0].end = u32(3)"} {
		src := "import(std)\nmain: (): i32 {\nstate: [1]ByteBufferCursor\nq: [*]ByteBufferCursor = span(&state)\n" + state + "\nbuffer_len(q, u32(2))\n0\n}"
		_, abnormal := buildAndRun(t, "bufferinvalid", src)
		if !abnormal {
			t.Fatal("invalid buffer cursor must trap")
		}
	}
}

func TestE2EStdlibFluentBuilder(t *testing.T) {
	src := `
import(std)
main: (): i32 {
 data: [4]u8
 input: [2]u8
 input[0] = u8(20)
 input[1] = u8(30)
 s: [*]u8 = span(&data)
 v: []u8 = view(&input)
 built: ByteBuilder = byte_builder().append_byte(s, u8(10)).append_bytes(s, v).append_byte(s, u8(40))
 done: Result[u32, BufferError] = built.finish_bytes()
 count: u32 = done ? | .Ok(n) => n | .Err(e) => u32(99)
 assert(count == u32(4))
 assert(s[0] == u8(10) && s[1] == u8(20) && s[2] == u8(30) && s[3] == u8(40))
 failed: ByteBuilder = built.append_byte(s, u8(90)).append_bytes(s, v)
 bad: Result[u32, BufferError] = failed.finish_bytes()
 rejected: Bool = bad ? | .Ok(n) => false | .Err(e) => true
 assert(rejected && failed.length == u32(4))
 assert(s[0] == u8(10) && s[1] == u8(20) && s[2] == u8(30) && s[3] == u8(40))
 other: [2]u8
 t: [*]u8 = span(&other)
 prefix: ByteBuilder = byte_builder().append_byte(t, u8(7))
 sticky: ByteBuilder = prefix.append_bytes(t, v).append_byte(t, u8(8))
 assert(sticky.failed && sticky.length == u32(1) && t[0] == u8(7) && t[1] == u8(0))
 assert(!prefix.failed && prefix.length == u32(1))
 direct: ByteBuilder = append_byte(byte_builder(), t, u8(9))
 assert(!direct.failed && t[0] == u8(9))
 42
}
`
	output, err := New().WithSource("builder.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "OAK_UNSUPPORTED"} {
		if strings.Contains(output, forbidden) {
			t.Fatalf("unexpected %s in builder C", forbidden)
		}
	}
	code, abnormal := buildAndRun(t, "builder", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	for _, bad := range []string{
		"import(std)\nmain: (): i32 {\nr: Result[u32, BufferError] = u32(3).finish_bytes()\n0\n}",
		"import(std)\nmain: (): i32 {\ndata: [1]u8\ns: [*]u8 = span(&data)\nb: ByteBuilder = byte_builder().append_byte(s, u32(3))\n0\n}",
	} {
		if _, err := New().WithSource("badbuilder.oak", bad).EmitC().Get(); err == nil {
			t.Fatal("fluent sugar must retain ordinary type checking")
		}
	}
}

func TestStdlibBuilderOptimizesToConstant(t *testing.T) {
	if runtime.GOOS != "linux" || runtime.GOARCH != "amd64" {
		t.Skip("assembly comparison currently targets the Linux amd64 CI toolchain")
	}
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler")
	}
	src := `
import(std)
main: (): i32 {
 data: [1]u8
 s: [*]u8 = span(&data)
 b: ByteBuilder = byte_builder().append_byte(s, u8(42))
 result: Result[u32, BufferError] = b.finish_bytes()
 ok: Bool = result ? | .Ok(n) => n == u32(1) | .Err(e) => false
 assert(ok)
 i32(s[0])
}
`
	generated, err := New().WithSource("optimizedbuilder.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	instructions := func(name, source string) string {
		t.Helper()
		dir := t.TempDir()
		input, output := filepath.Join(dir, name+".c"), filepath.Join(dir, name+".s")
		if err := os.WriteFile(input, []byte(source), 0600); err != nil {
			t.Fatal(err)
		}
		if out, err := exec.Command(cc, "-std=c99", "-O3", "-S", input, "-o", output).CombinedOutput(); err != nil {
			t.Fatalf("assembly build: %v\n%s", err, out)
		}
		assembly, err := os.ReadFile(output)
		if err != nil {
			t.Fatal(err)
		}
		text := string(assembly)
		start := strings.Index(text, "\noak_main:\n")
		if start < 0 {
			t.Fatal("missing oak_main assembly")
		}
		var body []string
		for _, line := range strings.Split(text[start+len("\noak_main:\n"):], "\n") {
			line = strings.TrimSpace(line)
			if strings.HasPrefix(line, ".size") {
				break
			}
			if line == "" || strings.HasPrefix(line, ".") || strings.HasSuffix(line, ":") || strings.HasPrefix(line, "#") {
				continue
			}
			body = append(body, strings.Join(strings.Fields(line), " "))
		}
		return strings.Join(body, "\n")
	}
	actual := instructions("builder", generated)
	want := instructions("constant", "int oak_main(void) { return 42; }\n")
	if actual != want {
		t.Fatalf("builder did not optimize to a direct constant return:\n%s\nwant:\n%s", actual, want)
	}
}
