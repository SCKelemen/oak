package compiler

import (
	"fmt"
	"os"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// Freeze the pre-batched update loop and original whole-state absorb helper,
// not transformations of current source. Compression and chunk/stack helpers
// remain shared; update and ordinary-block state transitions are independent.
const blake3OriginalUpdateSource = `
update_test_absorb_original: (state: Blake3State): Blake3State {
  next: Blake3State = state
  out: [16]u32 = blake3_compress(next.cv, blake3_words(next.block), next.chunk_counter, u32(64), blake3_start_flag(next))
  next.cv = blake3_first8(out)
  next.blocks_compressed = next.blocks_compressed + u32(1)
  next.block_len = u32(0)
  next
}

update_test_original: (state: Blake3State, src: []u8): Blake3State {
  next: Blake3State = state
  i: u32 = 0
  while i < len(src) {
    next.block_len == u32(64) && next.blocks_compressed == u32(15) ? {
      next = blake3_push_chunk(next, blake3_chunk_cv(next))
    } | {
      next.block_len == u32(64) ? { next = update_test_absorb_original(next) }
    }
    next.block[next.block_len] = src[i]
    next.block_len = next.block_len + u32(1)
    i = i + u32(1)
  }
  next
}
`

const blake3UpdateStateHelpers = `
// Compare every observable field, including unused block/stack entries.
// There is intentionally no C struct memcmp or comparison of padding.
update_test_same: (left: Blake3State, right: Blake3State): Bool {
  ok: Bool = left.block_len == right.block_len && left.blocks_compressed == right.blocks_compressed && left.chunk_counter == right.chunk_counter && left.stack_len == right.stack_len
  i: u32 = 0
  while ok && i < u32(8) {
    ok = left.cv[i] == right.cv[i]
    i = i + u32(1)
  }
  i = u32(0)
  while ok && i < u32(64) {
    ok = left.block[i] == right.block[i]
    i = i + u32(1)
  }
  i = u32(0)
  while ok && i < u32(432) {
    ok = left.stack[i] == right.stack[i]
    i = i + u32(1)
  }
  ok
}

// Deliberately nonzero inactive storage catches accidental clearing/copying.
// Counter 3 and two stack entries exercise both merges when a chunk closes.
update_test_seed: (offset: u32, blocks: u32): Blake3State {
  state: Blake3State = blake3_init()
  state.block_len = offset
  state.blocks_compressed = blocks
  state.chunk_counter = u64(3)
  state.stack_len = u32(2)
  i: u32 = 0
  while i < u32(8) {
    state.cv[i] = i * u32(2654435761) + u32(123456789)
    i = i + u32(1)
  }
  i = u32(0)
  while i < u32(64) {
    state.block[i] = u8_trunc_u32((i * u32(37) + u32(19)) % u32(256))
    i = i + u32(1)
  }
  i = u32(0)
  while i < u32(432) {
    state.stack[i] = i * u32(2246822519) + u32(987654321)
    i = i + u32(1)
  }
  state
}

update_test_fill: (out: [*]u8, random: Bool): u64 {
  x: u64 = 11400714819323198485
  i: u32 = 0
  while i < len(out) {
    x = x * u64(6364136223846793005) + u64(1442695040888963407)
    out[i] = random ? u8_trunc_u64(x >> u64(56)) | u8_trunc_u32(i % u32(251))
    i = i + u32(1)
  }
  x
}

update_test_offset: (offset: u32, blocks: u32, input: []u8): Bool {
  state: Blake3State = update_test_seed(offset, blocks)
  empty: []u8 = subslice(input, u32(0), u32(0))
  old_empty: Blake3State = update_test_original(state, empty)
  new_empty: Blake3State = blake3_update(state, empty)
  assert(update_test_same(old_empty, state) && update_test_same(new_empty, state))
  // Ending exactly at 64 must leave this block open, including block 15.
  fill: []u8 = subslice(input, u32(0), u32(64) - offset)
  old_full: Blake3State = update_test_original(state, fill)
  new_full: Blake3State = blake3_update(state, fill)
  assert(update_test_same(old_full, new_full))
  assert(new_full.block_len == u32(64) && new_full.blocks_compressed == blocks && new_full.chunk_counter == u64(3))
  old_more: Blake3State = update_test_original(state, input)
  new_more: Blake3State = blake3_update(state, input)
  assert(update_test_same(old_more, new_more))
  // Reconstruct independently: a second alias of state could hide mutation.
  update_test_same(state, update_test_seed(offset, blocks))
}

update_test_empty_malformed: (offset: u32, empty: []u8): Bool {
  state: Blake3State = update_test_seed(offset, u32(15))
  old: Blake3State = update_test_original(state, empty)
  new: Blake3State = blake3_update(state, empty)
  update_test_same(old, update_test_seed(offset, u32(15))) && update_test_same(new, update_test_seed(offset, u32(15))) && update_test_same(state, update_test_seed(offset, u32(15)))
}
`

func blake3UpdateSource(t *testing.T, program string) string {
	t.Helper()
	data, err := os.ReadFile("../stdlib/hash.oak")
	if err != nil {
		t.Fatal(err)
	}
	source := string(data)
	const section = "\nBLAKE3_IV:"
	if strings.Count(source, section) != 1 {
		t.Fatal("hash BLAKE3 section changed; cannot inline private update helpers")
	}
	var rotate string
	for _, line := range strings.Split(source, "\n") {
		if strings.HasPrefix(line, "rotr32:") {
			if rotate != "" {
				t.Fatal("ambiguous rotr32 helper")
			}
			rotate = line
		}
	}
	if rotate == "" {
		t.Fatal("missing BLAKE3 rotate helper")
	}
	// SHA256/CRC32 have unrelated companion-assembly declarations. Inline
	// only BLAKE3 and its shared rotate helper, verbatim from this checkout.
	return "package main\n" + rotate + source[strings.Index(source, section):] + blake3OriginalUpdateSource + blake3UpdateStateHelpers + program
}

func blake3UpdateDifferentialProgram() string {
	var program strings.Builder
	// Valid incremental states are compared after every cut, so exact final
	// blocks/chunks and the first byte after them are independently observed.
	for _, random := range []bool{false, true} {
		name := fmt.Sprintf("update_test_stream_%t", random)
		data := make([]byte, 2050)
		x := uint64(11400714819323198485)
		for i := range data {
			x = x*6364136223846793005 + 1442695040888963407
			if random {
				data[i] = byte(x >> 56)
			} else {
				data[i] = byte(i % 251)
			}
		}
		want := blake3Reference(data)
		fmt.Fprintf(&program, "\n%s: (): Bool {\n  input: [2050]u8\n  _ = update_test_fill(span(&input), %t)\n  bytes: []u8 = view(&input)\n  old: Blake3State = blake3_init()\n  new: Blake3State = blake3_init()\n", name, random)
		previous := 0
		for _, end := range []int{0, 1, 63, 64, 65, 1023, 1024, 1025, 2048, 2049, 2050} {
			fmt.Fprintf(&program, "  old = update_test_original(old, subslice(bytes, u32(%d), u32(%d)))\n  new = blake3_update(new, subslice(bytes, u32(%d), u32(%d)))\n  assert(update_test_same(old, new))\n", previous, end-previous, previous, end-previous)
			if end == 64 || end == 1024 || end == 2048 {
				program.WriteString("  assert(new.block_len == u32(64))\n")
			}
			if end == 1024 {
				program.WriteString("  assert(new.blocks_compressed == u32(15) && new.chunk_counter == u64(0))\n")
			}
			previous = end
		}
		program.WriteString(`  whole_old: Blake3State = update_test_original(blake3_init(), bytes)
  whole_new: Blake3State = blake3_update(blake3_init(), bytes)
  assert(update_test_same(whole_old, old) && update_test_same(whole_new, new))
  old_digest: [32]u8
  new_digest: [32]u8
  assert(blake3_final(old, span(&old_digest)) && blake3_final(new, span(&new_digest)))
`)
		writeBytes(&program, "want", want[:])
		program.WriteString(`  i: u32 = 0
  ok: Bool = true
  while i < u32(32) {
    ok = ok && old_digest[i] == want[i] && new_digest[i] == want[i]
    i = i + u32(1)
  }
  ok
}
`)
	}
	program.WriteString(`
main: (): i32 {
  pattern: [129]u8
  random: [129]u8
  _ = update_test_fill(span(&pattern), false)
  _ = update_test_fill(span(&random), true)
  offset: u32 = 0
  while offset <= u32(64) {
    assert(update_test_offset(offset, u32(0), view(&pattern)))
    assert(update_test_offset(offset, u32(15), view(&random)))
    offset = offset + u32(1)
  }
  pattern_view: []u8 = view(&pattern)
  empty: []u8 = subslice(pattern_view, u32(0), u32(0))
  assert(update_test_empty_malformed(u32(65), empty))
  assert(update_test_empty_malformed(u32(4294967295), empty))
  assert(update_test_stream_false() && update_test_stream_true())
  42
}
`)
	return program.String()
}

// This is source/C/interpreter differential coverage, not a claim that the
// update function has a proven native verdict. Compression proof tests live
// separately and are not replaced by agreement with this frozen loop.
func TestE2EBlake3UpdateDifferential(t *testing.T) {
	source := blake3UpdateSource(t, blake3UpdateDifferentialProgram())
	t.Run("c", func(t *testing.T) {
		if code, abnormal := buildAndRun(t, "blake3_update_diff", source); abnormal || code != 42 {
			t.Fatalf("state/digest differential: code=%d abnormal=%v", code, abnormal)
		}
	})
	t.Run("interpreter", func(t *testing.T) {
		if got := interpretChecked(t, source); got != 42 {
			t.Fatalf("state/digest differential returned %d", got)
		}
	})
}

// The private CV helper must preserve the old transition even for public
// states outside the normal hash history. In particular, a u32 block count
// wraps, while all 64 counter bits, buffered bytes and inactive stack words
// remain unchanged by absorption. The actual update call additionally covers
// chunk-counter wrapping on the distinct block-15 chunk-completion path.
func TestE2EBlake3UpdateAbsorbTransition(t *testing.T) {
	source := blake3UpdateSource(t, `
update_test_absorb_seed: (blocks: u32, counter: u64, random: Bool): Blake3State {
  state: Blake3State = update_test_seed(u32(64), blocks)
  state.chunk_counter = counter
  block: [64]u8
  _ = update_test_fill(span(&block), random)
  state.block = block
  state
}

update_test_absorb_case: (blocks: u32, counter: u64, random: Bool): Bool {
  state: Blake3State = update_test_absorb_seed(blocks, counter, random)
  old: Blake3State = update_test_absorb_original(state)
  next: Blake3State = state
  next.cv = blake3_absorb_cv(next.cv, next.block, next.chunk_counter, blake3_start_flag(next))
  next.blocks_compressed = next.blocks_compressed + u32(1)
  next.block_len = u32(0)
  assert(update_test_same(old, next))
  assert(next.block_len == u32(0) && next.blocks_compressed == blocks + u32(1) && next.chunk_counter == counter)
  // Exercise the production branch, not just a test-side reconstruction.
  input: [1]u8 = [1]u8{ 239 }
  old_update: Blake3State = update_test_original(state, view(&input))
  new_update: Blake3State = blake3_update(state, view(&input))
  assert(update_test_same(old_update, new_update))
  blocks == u32(15) ? {
    assert(new_update.chunk_counter == counter + u64(1) && new_update.blocks_compressed == u32(0))
  } | {
    assert(new_update.chunk_counter == counter && new_update.blocks_compressed == blocks + u32(1))
  }
  assert(new_update.block_len == u32(1))
  // Reconstruct rather than comparing two potentially aliased snapshots.
  update_test_same(state, update_test_absorb_seed(blocks, counter, random))
}

main: (): i32 {
  blocks: [6]u32 = [6]u32{ 0, 1, 14, 15, 16, 4294967295 }
  counters: [5]u64 = [5]u64{ 0, 1, 4294967295, 4294967296, 18446744073709551615 }
  i: u32 = 0
  while i < u32(6) {
    j: u32 = 0
    while j < u32(5) {
      assert(update_test_absorb_case(blocks[i], counters[j], false))
      assert(update_test_absorb_case(blocks[i], counters[j], true))
      j = j + u32(1)
    }
    i = i + u32(1)
  }
  42
}
`)
	t.Run("c", func(t *testing.T) {
		if code, abnormal := buildAndRun(t, "blake3_absorb_diff", source); abnormal || code != 42 {
			t.Fatalf("absorb transition differential: code=%d abnormal=%v", code, abnormal)
		}
	})
	t.Run("interpreter", func(t *testing.T) {
		if got := interpretChecked(t, source); got != 42 {
			t.Fatalf("absorb transition differential returned %d", got)
		}
	})
}

func TestE2EBlake3UpdateMalformedStateTraps(t *testing.T) {
	for _, offset := range []uint32{65, ^uint32(0)} {
		t.Run(fmt.Sprint(offset), func(t *testing.T) {
			var messages []string
			for _, update := range []string{"update_test_original", "blake3_update"} {
				t.Run(update, func(t *testing.T) {
					program := fmt.Sprintf(`
main: (): i32 {
  state: Blake3State = blake3_init()
  state.block_len = u32(%d)
  input: [1]u8 = [1]u8{ 7 }
  next: Blake3State = %s(state, view(&input))
  i32_bits_u32(next.block_len)
}
`, offset, update)
					source := blake3UpdateSource(t, program)
					if code, abnormal := buildAndRun(t, "blake3_update_trap", source); !abnormal {
						t.Fatalf("malformed block_len did not trap: code=%d", code)
					}
					model, err := New().WithSource("blake3_update_trap.oak", source).Check().Get()
					if err != nil {
						t.Fatal(err)
					}
					env := object.NewEnvironment()
					env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
					if result := evaluator.Eval(model.Tree.Root, env); isEvalError(result) {
						t.Fatalf("defining the program failed: %s", result.Inspect())
					}
					call := parser.New(layout.New(scanner.New("main()"))).ParseProgram()
					result := evaluator.Eval(call, env)
					failure, ok := result.(*object.Error)
					want := fmt.Sprintf("array index out of bounds: %d (length: 64)", offset)
					if !ok || !strings.Contains(failure.Message, want) {
						t.Fatalf("interpreter returned %v, want %q", result, want)
					}
					messages = append(messages, failure.Message)
				})
			}
			if len(messages) == 2 && messages[0] != messages[1] {
				t.Fatalf("old/new trap messages differ: %q vs %q", messages[0], messages[1])
			}
		})
	}
}
