package main

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/experiments/verification-poc/internal/lrat"
)

type tableCase struct {
	rangeCase
	Trace []uint32 `json:"trace"`
}
type tableEntry struct {
	start, count uint32
	live         bool
}

// A map of logical clauses is independent of the observed Oak metadata arrays.
// RUP uses the existing Go checker after compacting live IDs and translating hints.
func tableReference(c rangeCase) []uint32 {
	entries := make([]tableEntry, 256)
	db := map[uint32][]int{}
	last := uint32(len(c.Starts))
	refuted := false
	valid := c.Variables > 0 && c.Variables <= 64 && len(c.Pool) <= 4096 && len(c.Refs) <= 4096 && len(c.Starts) == len(c.Sizes) && len(c.Starts) <= 256 && len(c.Commands) <= 256
	for _, n := range c.Pool {
		if n/2 >= c.Variables {
			valid = false
		}
	}
	decode := func(items []uint32) []int {
		out := []int{}
		for _, n := range items {
			out = append(out, rangeLiteral(n))
		}
		return out
	}
	for i, start := range c.Starts {
		if !valid {
			break
		}
		items, ok := rangeSlice(c.Pool, start, c.Sizes[i])
		valid = ok
		if ok {
			entries[i] = tableEntry{start, c.Sizes[i], true}
			db[uint32(i+1)] = decode(items)
			refuted = refuted || len(items) == 0
		}
	}
	out := []uint32{}
	bit := func(b bool) uint32 {
		if b {
			return 1
		}
		return 0
	}
	snapshot := func() {
		out = append(out, last, bit(refuted), bit(valid))
		for _, e := range entries {
			out = append(out, e.start, e.count, bit(e.live))
		}
	}
	snapshot()
	for _, cmd := range c.Commands {
		if !valid {
			break
		}
		refs, ok := rangeSlice(c.Refs, cmd.RefsStart, cmd.RefsCount)
		valid = cmd.ID <= 2147483647 && ok
		if valid && cmd.Addition {
			items, rangeOK := rangeSlice(c.Pool, cmd.Start, cmd.Count)
			valid = cmd.ID > last && cmd.ID <= 256 && rangeOK && cmd.RefsCount <= 256
			clauses := [][]int{}
			mapping := map[uint32]int{}
			for id := uint32(1); id <= 256; id++ {
				if clause, present := db[id]; present {
					clauses = append(clauses, clause)
					mapping[id] = len(clauses)
				}
			}
			hints := []int{}
			for _, id := range refs {
				mapped, present := mapping[id]
				if !present {
					valid = false
				}
				hints = append(hints, mapped)
			}
			if valid {
				valid = lrat.CheckRUPDecoded(int(c.Variables), clauses, decode(items), hints) == nil
			}
			if valid {
				entries[cmd.ID-1] = tableEntry{cmd.Start, cmd.Count, true}
				db[cmd.ID] = decode(items)
				last = cmd.ID
				refuted = refuted || len(items) == 0
			}
		} else if valid {
			valid = cmd.ID >= last
			for _, id := range refs {
				if !valid {
					break
				}
				_, present := db[id]
				valid = present
				if id > 0 && id <= 256 {
					entries[id-1].live = false
				}
				delete(db, id)
			}
		}
		snapshot()
	}
	return out
}

func tableInstrument(t *testing.T, source string) string {
	t.Helper()
	replace := func(old, next string) {
		if strings.Count(source, old) != 1 {
			t.Fatalf("live-table observation seam changed: %q", old)
		}
		source = strings.Replace(source, old, next, 1)
	}
	replace("  variables: u32\n): Bool {", "  variables: u32,\n  expected: []u32,\n  expected_accepted: Bool\n): Bool {")
	observation := "  trace_ok = table_observe(view(&starts), view(&lengths), view(&live), last, refuted, valid, expected, trace_cursor) && trace_ok\n  trace_cursor = trace_cursor + u32(771)\n"
	replace("  c: u32 = 0\n", "  c: u32 = 0\n  trace_ok: Bool = true\n  trace_cursor: u32 = 0\n"+observation)
	replace("    c = c + u32(1)\n", "    c = c + u32(1)\n"+observation)
	replace("  valid && refuted\n}", "  trace_ok && trace_cursor == len(expected) && (valid && refuted) == expected_accepted\n}")
	return source + `
// Test-only observer. It cannot change the checker's table or control flags.
table_observe: (starts: []u32, sizes: []u32, live: []Bool,
  last: u32, refuted: Bool, valid: Bool, expected: []u32, offset: u32): Bool {
  ok: Bool = offset <= len(expected) && u32(771) <= len(expected) - offset
  ok ? {
    ok = expected[offset] == last && (expected[offset + u32(1)] == u32(1)) == refuted && (expected[offset + u32(2)] == u32(1)) == valid
    slot: u32 = 0
    while slot < u32(256) && ok {
      at: u32 = offset + u32(3) + slot * u32(3)
      ok = expected[at] == starts[slot] && expected[at + u32(1)] == sizes[slot] && (expected[at + u32(2)] == u32(1)) == live[slot]
      slot = slot + u32(1)
    }
  }
  ok
}
`
}

func TestSelfHostedLiveTable(t *testing.T) {
	cases := []tableCase{}
	snapshots := 0
	for _, c := range rangeCorpus(t) {
		trace := tableReference(c)
		last := trace[len(trace)-771:]
		if (last[1] == 1 && last[2] == 1) != c.Accepted {
			t.Fatalf("%s: table oracle changed acceptance", c.Name)
		}
		cases = append(cases, tableCase{c, trace})
		snapshots += len(trace) / 771
	}
	var source, main strings.Builder
	kernel, err := os.ReadFile("self_hosted_rup.oak")
	if err != nil {
		t.Fatal(err)
	}
	source.Write(kernel)
	source.WriteByte('\n')
	stream, err := os.ReadFile("self_hosted_stream.oak")
	if err != nil {
		t.Fatal(err)
	}
	source.WriteString(tableInstrument(t, string(stream)))
	main.WriteString("main: (): i32 {\n")
	emit := func(i int, c tableCase, want bool) {
		fmt.Fprintf(&source, "table_case_%d: (): Bool {\n", i)
		for _, a := range []struct {
			name  string
			items []uint32
		}{{"pool", c.Pool}, {"starts", c.Starts}, {"sizes", c.Sizes}, {"refs", c.Refs}, {"expected", c.Trace}} {
			emitBufferArray(&source, a.name, "u32", a.items)
		}
		capacity := len(c.Commands)
		if capacity == 0 {
			capacity = 1
		}
		fmt.Fprintf(&source, "commands: [%d]RUPCommand\n", capacity)
		for j, r := range c.Commands {
			fmt.Fprintf(&source, "commands[%d] = RUPCommand { addition: %t, id: u32(%d), start: u32(%d), count: u32(%d), refs_start: u32(%d), refs_count: u32(%d) }\n", j, r.Addition, r.ID, r.Start, r.Count, r.RefsStart, r.RefsCount)
		}
		fmt.Fprintf(&source, "command_view: []RUPCommand = commands[0:%d]\nrup_stream_check(pool_view, starts_view, sizes_view, refs_view, command_view, u32(%d), expected_view, %t) == %t\n}\n", len(c.Commands), c.Variables, c.Accepted, want)
		fmt.Fprintf(&main, "assert(table_case_%d())\n", i)
	}
	for i, c := range cases {
		emit(i, c, true)
	}
	// Make sure missing snapshots and corrupt metadata/control bits cannot pass the observer.
	for i, field := range []int{0, 1, 2, 3, 4, 5, -1} {
		c := cases[0]
		c.Trace = append([]uint32{}, c.Trace...)
		if field < 0 {
			c.Trace = c.Trace[:len(c.Trace)-771]
		} else {
			c.Trace[field] ^= 1
		}
		emit(len(cases)+i, c, false)
	}
	main.WriteString("42\n}\n")
	source.WriteString(main.String())
	runOakStream(t, source.String())
	if path := os.Getenv("OAK_TABLE_CORPUS_OUT"); path != "" {
		data, err := json.MarshalIndent(cases, "", "  ")
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, append(data, '\n'), 0644); err != nil {
			t.Fatal(err)
		}
	}
	t.Logf("Oak/Go live table: %d layouts, %d complete 256-slot snapshots, 7 observer corruptions rejected", len(cases), snapshots)
}
