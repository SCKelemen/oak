package compiler

import (
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// TestLeanStdlibFaithful runs the committed Lean extractions and the
// compiled Oak programs on one fixed corpus and compares their output byte
// for byte (docs/spec/95-extraction.md section 6). The drift test only
// checks that the committed text is current; this is the executable check
// that the text means what the compiled code does — it is what would have
// caught oak #186, where the heap sort's heapify loop lost its array. It
// needs the Lean toolchain (`lake` on PATH or under ~/.elan/bin) and the
// `spec/lean` library built; the Formal Verification workflow runs it.
func TestLeanStdlibFaithful(t *testing.T) {
	lake := findLake()
	if lake == "" {
		t.Skip("lake not found (PATH or ~/.elan/bin); the faithfulness check needs the Lean toolchain")
	}
	root, err := filepath.Abs(filepath.Join("..", "spec", "lean"))
	if err != nil {
		t.Fatal(err)
	}
	corpus := newFaithfulCorpus(20260911)

	// Oak: one module with qualified imports, printing one line per case.
	oakRoot := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/faithful\noak 0.1.0\n",
		"main.oak": "package main\n" + corpus.oakProgram(),
	})
	if dump := os.Getenv("OAK_FAITHFUL_DUMP"); dump != "" {
		// Keep both drivers for inspection.
		_ = os.MkdirAll(dump, 0o755)
		_ = os.WriteFile(filepath.Join(dump, "main.oak"), []byte("package main\n"+corpus.oakProgram()), 0o644)
		_ = os.WriteFile(filepath.Join(dump, "oak.mod"), []byte("module example.com/faithful\noak 0.1.0\n"), 0o644)
		_ = os.WriteFile(filepath.Join(dump, "faithful.lean"), []byte(corpus.leanProgram()), 0o644)
	}
	stdout, code, abnormal := buildAndRunFrom(t, "faithful", New().WithPackageDir(oakRoot))
	if abnormal || code != 0 {
		t.Fatalf("faithfulness program exited (%d, abnormal=%v):\n%s", code, abnormal, stdout)
	}

	// Lean: a driver over the extracted modules, run in the interpreter.
	build := exec.Command(lake, "build")
	build.Dir = root
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("lake build: %v\n%s", err, out)
	}
	driver := filepath.Join(t.TempDir(), "faithful.lean")
	if err := os.WriteFile(driver, []byte(corpus.leanProgram()), 0o644); err != nil {
		t.Fatal(err)
	}
	run := exec.Command(lake, "env", "lean", "--run", driver)
	run.Dir = root
	leanOut, err := run.CombinedOutput()
	if err != nil {
		t.Fatalf("lake env lean --run: %v\n%s", err, leanOut)
	}

	oakLines := strings.Split(strings.TrimRight(stdout, "\n"), "\n")
	leanLines := strings.Split(strings.TrimRight(string(leanOut), "\n"), "\n")
	if len(oakLines) != corpus.lines || len(leanLines) != corpus.lines {
		t.Fatalf("line counts: oak %d, lean %d, want %d\n--- oak\n%s\n--- lean\n%s", len(oakLines), len(leanLines), corpus.lines, stdout, leanOut)
	}
	mismatches := 0
	for i := range oakLines {
		if oakLines[i] != leanLines[i] {
			mismatches++
			if mismatches <= 10 {
				t.Errorf("line %d differs\n  oak:  %s\n  lean: %s", i+1, oakLines[i], leanLines[i])
			}
		}
	}
	if mismatches > 0 {
		t.Fatalf("%d of %d lines differ between the compiled Oak and the extracted Lean", mismatches, corpus.lines)
	}
}

func findLake() string {
	if path, err := exec.LookPath("lake"); err == nil {
		return path
	}
	home, err := os.UserHomeDir()
	if err != nil {
		return ""
	}
	candidate := filepath.Join(home, ".elan", "bin", "lake")
	if _, err := os.Stat(candidate); err == nil {
		return candidate
	}
	return ""
}

// faithfulCorpus is the shared input set. Every case prints one line of
// decimal numbers separated by single spaces, prefixed by the case name.
type faithfulCorpus struct {
	sortInputs   [][]uint32 // each 1..24 elements
	varintValues []uint64
	bytesInputs  [][]byte // each 1..20 bytes, hex/base64
	seeds        []uint64
	hashInputs   [][]byte // each 1..70 bytes
	lines        int
}

func newFaithfulCorpus(seed int64) *faithfulCorpus {
	rng := rand.New(rand.NewSource(seed))
	c := &faithfulCorpus{}
	for i := 0; i < 30; i++ {
		n := 1 + rng.Intn(24)
		items := make([]uint32, n)
		switch i % 5 {
		case 0: // sorted
			for j := range items {
				items[j] = uint32(j * 3)
			}
		case 1: // reversed
			for j := range items {
				items[j] = uint32((n - j) * 2)
			}
		case 2: // few distinct
			for j := range items {
				items[j] = uint32(rng.Intn(3))
			}
		default:
			for j := range items {
				items[j] = uint32(rng.Intn(100))
			}
		}
		c.sortInputs = append(c.sortInputs, items)
	}
	for i := 0; i < 60; i++ {
		bits := uint(1 + rng.Intn(64))
		v := rng.Uint64()
		if bits < 64 {
			v &= (uint64(1) << bits) - 1
		}
		c.varintValues = append(c.varintValues, v)
	}
	for i := 0; i < 30; i++ {
		b := make([]byte, 1+rng.Intn(20))
		rng.Read(b)
		c.bytesInputs = append(c.bytesInputs, b)
	}
	c.seeds = []uint64{0, 1, 7, rng.Uint64()}
	for i := 0; i < 12; i++ {
		b := make([]byte, 1+rng.Intn(70))
		rng.Read(b)
		c.hashInputs = append(c.hashInputs, b)
	}
	// sorts: 3 per input; varint: encode+decode lines; bytes: hex enc/dec,
	// b64 enc/dec; random: one line per seed; hash: crc and sha per input.
	c.lines = 3*len(c.sortInputs) + 2*len(c.varintValues) + 4*len(c.bytesInputs) + len(c.seeds) + 2*len(c.hashInputs)
	return c
}

func oakU32Array(items []uint32) string {
	parts := make([]string, len(items))
	for i, v := range items {
		parts[i] = fmt.Sprintf("%d", v)
	}
	return fmt.Sprintf("[%d]u32{ %s }", len(items), strings.Join(parts, ", "))
}

func oakU8Array(items []byte) string {
	parts := make([]string, len(items))
	for i, v := range items {
		parts[i] = fmt.Sprintf("%d", v)
	}
	return fmt.Sprintf("[%d]u8{ %s }", len(items), strings.Join(parts, ", "))
}

func leanArray(items []string, typ string) string {
	if len(items) == 0 {
		return fmt.Sprintf("(#[] : Array %s)", typ)
	}
	return fmt.Sprintf("(#[%s] : Array %s)", strings.Join(items, ", "), typ)
}

func leanU32Array(items []uint32) string {
	parts := make([]string, len(items))
	for i, v := range items {
		parts[i] = fmt.Sprintf("(%d : UInt32)", v)
	}
	return leanArray(parts, "UInt32")
}

func leanU8Array(items []byte) string {
	parts := make([]string, len(items))
	for i, v := range items {
		parts[i] = fmt.Sprintf("(%d : UInt8)", v)
	}
	return leanArray(parts, "UInt8")
}

// oakProgram prints, per case, the case name and the outputs as decimal
// numbers; helpers print through putchar so no text package is involved.
func (c *faithfulCorpus) oakProgram() string {
	var b strings.Builder
	b.WriteString(`import(std)
import("sort")
import("varint")
import("encoding")
import("random")
import("hash")

putchar: (ch: c.Int): c.Int = c.extern("putchar")

put: (unit: u8): () {
  _ = putchar(c.Int(i32_bits_u32(u32(unit))))
}
put_text: (text: []u8): () {
  i: u32 = 0
  while i < len(text) { put(text[i])
    i = i + u32(1)
  }
}
put_u64: (value: u64): () {
  digits: [20]u8
  n: u32 = 0
  rest: u64 = value
  more: Bool = true
  while more {
    digits[n] = u8(48) + u8_trunc_u64(rest % u64(10))
    n = n + u32(1)
    rest = rest / u64(10)
    rest == u64(0) ? { more = false }
  }
  while n > u32(0) {
    n = n - u32(1)
    put(digits[n])
  }
}
put_sep: (): () {
  put(u8(32))
}
put_nl: (): () {
  put(u8(10))
}
put_u32s: (items: []u32): () {
  i: u32 = 0
  while i < len(items) { put_sep(); put_u64(u64(items[i]))
    i = i + u32(1)
  }
}
put_u8s: (items: []u8): () {
  i: u32 = 0
  while i < len(items) { put_sep(); put_u64(u64(items[i]))
    i = i + u32(1)
  }
}
`)
	// Sorts.
	for i, items := range c.sortInputs {
		fmt.Fprintf(&b, "sort_case_%d: (): () {\n", i)
		for _, kind := range []string{"heap", "span", "insertion"} {
			fmt.Fprintf(&b, "  %s_%d: [%d]u32 = %s\n", kind, i, len(items), oakU32Array(items))
			fmt.Fprintf(&b, "  true ? { s: [*]u32 = span(&%s_%d)\n    sort.sort_%s[u32](s) }\n", kind, i, kind)
			fmt.Fprintf(&b, "  put_text(text_literal(\"sort_%s %d\")); put_u32s(view(&%s_%d)); put_nl()\n", kind, i, kind, i)
		}
		b.WriteString("}\n")
	}
	// Varint.
	b.WriteString("varint_cases: (): () {\n")
	for i, v := range c.varintValues {
		fmt.Fprintf(&b, "  true ? {\n    buf: [10]u8\n    n: u32 = 0\n    true ? { d: [*]u8 = span(&buf)\n      n = varint.varint_written(varint.varint_encode(d, u32(0), u64(%d))) }\n", v)
		fmt.Fprintf(&b, "    whole: []u8 = view(&buf)\n    encoded: []u8 = whole[u32(0):n]\n")
		fmt.Fprintf(&b, "    put_text(text_literal(\"varint_encode %d\")); put_sep(); put_u64(u64(n)); put_u8s(encoded); put_nl()\n", i)
		fmt.Fprintf(&b, "    back: varint.VarintValue = varint.varint_value(varint.varint_decode(encoded, u32(0)))\n")
		fmt.Fprintf(&b, "    put_text(text_literal(\"varint_decode %d\")); put_sep(); put_u64(back.value); put_sep(); put_u64(u64(back.next)); put_nl()\n  }\n", i)
	}
	b.WriteString("}\n")
	// Hex and base64.
	for i, src := range c.bytesInputs {
		fmt.Fprintf(&b, "bytes_case_%d: (): () {\n  src: [%d]u8 = %s\n", i, len(src), oakU8Array(src))
		b.WriteString("  hex: [64]u8\n  hexn: u32 = 0\n  true ? { d: [*]u8 = span(&hex)\n    hexn = encoding.encoding_value(encoding.hex_encode(d, view(&src), false)) }\n")
		b.WriteString("  hexv: []u8 = view(&hex)\n  hexenc: []u8 = hexv[u32(0):hexn]\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"hex_encode %d\")); put_sep(); put_u64(u64(hexn)); put_u8s(hexenc); put_nl()\n", i)
		b.WriteString("  hexback: [32]u8\n  hexbn: u32 = 0\n  true ? { d: [*]u8 = span(&hexback)\n    hexbn = encoding.encoding_value(encoding.hex_decode(d, hexenc)) }\n")
		b.WriteString("  hexbv: []u8 = view(&hexback)\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"hex_decode %d\")); put_sep(); put_u64(u64(hexbn)); put_u8s(hexbv[u32(0):hexbn]); put_nl()\n", i)
		b.WriteString("  b64: [64]u8\n  b64n: u32 = 0\n  true ? { d: [*]u8 = span(&b64)\n    b64n = encoding.encoding_value(encoding.base64_encode(d, view(&src), false, true)) }\n")
		b.WriteString("  b64v: []u8 = view(&b64)\n  b64enc: []u8 = b64v[u32(0):b64n]\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"base64_encode %d\")); put_sep(); put_u64(u64(b64n)); put_u8s(b64enc); put_nl()\n", i)
		b.WriteString("  b64back: [48]u8\n  b64bn: u32 = 0\n  true ? { d: [*]u8 = span(&b64back)\n    b64bn = encoding.encoding_value(encoding.base64_decode(d, b64enc, false)) }\n")
		b.WriteString("  b64bv: []u8 = view(&b64back)\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"base64_decode %d\")); put_sep(); put_u64(u64(b64bn)); put_u8s(b64bv[u32(0):b64bn]); put_nl()\n}\n", i)
	}
	// Random.
	b.WriteString("random_cases: (): () {\n")
	for i, seed := range c.seeds {
		fmt.Fprintf(&b, "  true ? {\n    states: [1]random.Xoshiro\n    states[0] = random.random_seed(u64(%d))\n    st: [*]random.Xoshiro = span(&states)\n", seed)
		fmt.Fprintf(&b, "    put_text(text_literal(\"random %d\"))\n    k: u32 = 0\n    while k < u32(8) { put_sep(); put_u64(random.random_next(st))\n      k = k + u32(1)\n    }\n    put_nl()\n  }\n", i)
	}
	b.WriteString("}\n")
	// Hash.
	for i, src := range c.hashInputs {
		fmt.Fprintf(&b, "hash_case_%d: (): () {\n  src: [%d]u8 = %s\n", i, len(src), oakU8Array(src))
		fmt.Fprintf(&b, "  put_text(text_literal(\"crc32c %d\")); put_sep(); put_u64(u64(hash.crc32c(view(&src)))); put_nl()\n", i)
		b.WriteString("  out: [32]u8\n  true ? { d: [*]u8 = span(&out)\n    _ = hash.sha256(view(&src), d) }\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"sha256 %d\")); put_u8s(view(&out)); put_nl()\n}\n", i)
	}
	b.WriteString("main: (): i32 {\n")
	for i := range c.sortInputs {
		fmt.Fprintf(&b, "  sort_case_%d()\n", i)
	}
	b.WriteString("  varint_cases()\n")
	for i := range c.bytesInputs {
		fmt.Fprintf(&b, "  bytes_case_%d()\n", i)
	}
	b.WriteString("  random_cases()\n")
	for i := range c.hashInputs {
		fmt.Fprintf(&b, "  hash_case_%d()\n", i)
	}
	b.WriteString("  0\n}\n")
	return b.String()
}

// leanProgram is the driver over the extracted modules producing the same
// lines. Every extracted function is fuel-indexed; the fuel is far above
// any loop bound here, so `none` prints as a visible disagreement.
func (c *faithfulCorpus) leanProgram() string {
	var b strings.Builder
	b.WriteString(`import Oak.Stdlib.SortU32Extracted
import Oak.Stdlib.VarintExtracted
import Oak.Stdlib.EncodingExtracted
import Oak.Stdlib.RandomExtracted
import Oak.Stdlib.HashExtracted

set_option maxRecDepth 65536

def fuel : Nat := 1000000

def showU32s (xs : Array UInt32) : String :=
  String.join (xs.toList.map (fun v => " " ++ toString v.toNat))

def showU8s (xs : Array UInt8) : String :=
  String.join (xs.toList.map (fun v => " " ++ toString v.toNat))

def showSort (name : String) (r : Option (Unit × Array UInt32)) : String :=
  match r with
  | some (_, xs) => name ++ showU32s xs
  | none => name ++ " none"

def varintWritten (r : Oak.Stdlib.Varint.Result_u32_VarintError) : UInt32 :=
  match r with
  | .Ok n => n
  | .Err _ => 0

def varintValue (r : Oak.Stdlib.Varint.Result_VarintValue_VarintError) : Oak.Stdlib.Varint.VarintValue :=
  match r with
  | .Ok v => v
  | .Err _ => { value := 0, next := 0 }

def encodingValue (r : Oak.Stdlib.Encoding.Result_u32_EncodingError) : UInt32 :=
  match r with
  | .Ok n => n
  | .Err _ => 0

def varintLines (i : Nat) (v : UInt64) : IO Unit := do
  match Oak.Stdlib.Varint.varint_encode (Array.replicate 10 (0 : UInt8)) 0 v fuel with
  | none => IO.println s!"varint_encode {i} none"; IO.println s!"varint_decode {i} none"
  | some (r, buf) =>
    let n := varintWritten r
    let encoded := buf.extract 0 n.toNat
    IO.println s!"varint_encode {i} {n.toNat}{showU8s encoded}"
    match Oak.Stdlib.Varint.varint_decode encoded 0 fuel with
    | none => IO.println s!"varint_decode {i} none"
    | some d =>
      let back := varintValue d
      IO.println s!"varint_decode {i} {back.value.toNat} {back.next.toNat}"

def bytesLines (i : Nat) (src : Array UInt8) : IO Unit := do
  match Oak.Stdlib.Encoding.hex_encode (Array.replicate 64 (0 : UInt8)) src false fuel with
  | none => IO.println s!"hex_encode {i} none"; IO.println s!"hex_decode {i} none"
  | some (r, hex) =>
    let n := encodingValue r
    let enc := hex.extract 0 n.toNat
    IO.println s!"hex_encode {i} {n.toNat}{showU8s enc}"
    match Oak.Stdlib.Encoding.hex_decode (Array.replicate 32 (0 : UInt8)) enc fuel with
    | none => IO.println s!"hex_decode {i} none"
    | some (r2, back) =>
      let m := encodingValue r2
      IO.println s!"hex_decode {i} {m.toNat}{showU8s (back.extract 0 m.toNat)}"
  match Oak.Stdlib.Encoding.base64_encode (Array.replicate 64 (0 : UInt8)) src false true fuel with
  | none => IO.println s!"base64_encode {i} none"; IO.println s!"base64_decode {i} none"
  | some (r, b64) =>
    let n := encodingValue r
    let enc := b64.extract 0 n.toNat
    IO.println s!"base64_encode {i} {n.toNat}{showU8s enc}"
    match Oak.Stdlib.Encoding.base64_decode (Array.replicate 48 (0 : UInt8)) enc false fuel with
    | none => IO.println s!"base64_decode {i} none"
    | some (r2, back) =>
      let m := encodingValue r2
      IO.println s!"base64_decode {i} {m.toNat}{showU8s (back.extract 0 m.toNat)}"

def randomLine (i : Nat) (seed : UInt64) : IO Unit := do
  match Oak.Stdlib.Random.random_seed seed fuel with
  | none => IO.println s!"random {i} none"
  | some st =>
    let mut state : Array Oak.Stdlib.Random.Xoshiro := #[st]
    let mut line := s!"random {i}"
    for _ in [0:8] do
      match Oak.Stdlib.Random.random_next state fuel with
      | none => line := line ++ " none"
      | some (v, st') =>
        line := line ++ " " ++ toString v.toNat
        state := st'
    IO.println line

def hashLines (i : Nat) (src : Array UInt8) : IO Unit := do
  match Oak.Stdlib.Hash.crc32c src fuel with
  | none => IO.println s!"crc32c {i} none"
  | some v => IO.println s!"crc32c {i} {v.toNat}"
  match Oak.Stdlib.Hash.sha256 src (Array.replicate 32 (0 : UInt8)) fuel with
  | none => IO.println s!"sha256 {i} none"
  | some (_, out) => IO.println s!"sha256 {i}{showU8s out}"

def main : IO Unit := do
`)
	for i, items := range c.sortInputs {
		arr := leanU32Array(items)
		fmt.Fprintf(&b, "  IO.println (showSort \"sort_heap %d\" (Oak.Stdlib.SortU32.sort_u32_heap %s fuel))\n", i, arr)
		fmt.Fprintf(&b, "  IO.println (showSort \"sort_span %d\" (Oak.Stdlib.SortU32.sort_u32_span %s fuel))\n", i, arr)
		fmt.Fprintf(&b, "  IO.println (showSort \"sort_insertion %d\" (Oak.Stdlib.SortU32.sort_u32_insertion %s fuel))\n", i, arr)
	}
	for i, v := range c.varintValues {
		fmt.Fprintf(&b, "  varintLines %d (%d : UInt64)\n", i, v)
	}
	for i, src := range c.bytesInputs {
		fmt.Fprintf(&b, "  bytesLines %d %s\n", i, leanU8Array(src))
	}
	for i, seed := range c.seeds {
		fmt.Fprintf(&b, "  randomLine %d (%d : UInt64)\n", i, seed)
	}
	for i, src := range c.hashInputs {
		fmt.Fprintf(&b, "  hashLines %d %s\n", i, leanU8Array(src))
	}
	return b.String()
}
