package main

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"
	"testing"
)

type rangeCommand struct {
	Addition  bool   `json:"addition"`
	ID        uint32 `json:"id"`
	Start     uint32 `json:"start"`
	Count     uint32 `json:"count"`
	RefsStart uint32 `json:"refsStart"`
	RefsCount uint32 `json:"refsCount"`
}
type rangeCase struct {
	Name      string         `json:"name"`
	Variables uint32         `json:"variables"`
	Pool      []uint32       `json:"pool"`
	Starts    []uint32       `json:"starts"`
	Sizes     []uint32       `json:"sizes"`
	Refs      []uint32       `json:"refs"`
	Commands  []rangeCommand `json:"commands"`
	Decoded   bool           `json:"decoded"`
	Meaning   []int64        `json:"meaning"`
	Accepted  bool           `json:"accepted"`
}

func rangeSlice(pool []uint32, start, count uint32) ([]uint32, bool) {
	// Wide sum is independent of Oak's subtraction-based guard.
	end := uint64(start) + uint64(count)
	if end > uint64(len(pool)) {
		return nil, false
	}
	return pool[start:int(end)], true
}
func rangeLiteral(n uint32) int {
	v := int(n/2) + 1
	if n%2 == 0 {
		v = -v
	}
	return v
}
func rangeDecode(c rangeCase) (streamCase, []int64, bool) {
	s := streamCase{Kind: "proof", Variables: int(c.Variables), Database: [][]int{}, Commands: []streamCommand{}}
	if c.Variables == 0 || c.Variables > 64 || len(c.Pool) > 4096 || len(c.Refs) > 4096 || len(c.Starts) != len(c.Sizes) || len(c.Starts) > 256 || len(c.Commands) > 256 {
		return s, nil, false
	}
	for _, n := range c.Pool {
		if n/2 >= c.Variables {
			return s, nil, false
		}
	}
	meaning := []int64{int64(c.Variables), int64(len(c.Starts))}
	for i, start := range c.Starts {
		items, ok := rangeSlice(c.Pool, start, c.Sizes[i])
		if !ok {
			return s, nil, false
		}
		clause := []int{}
		meaning = append(meaning, int64(len(items)))
		for _, v := range items {
			lit := rangeLiteral(v)
			clause = append(clause, lit)
			meaning = append(meaning, int64(lit))
		}
		s.Database = append(s.Database, clause)
	}
	meaning = append(meaning, int64(len(c.Commands)))
	for _, cmd := range c.Commands {
		if cmd.ID > 2147483647 {
			return s, nil, false
		}
		refs, ok := rangeSlice(c.Refs, cmd.RefsStart, cmd.RefsCount)
		if !ok {
			return s, nil, false
		}
		for _, id := range refs {
			if id == 0 || id > 256 {
				return s, nil, false
			}
		}
		if cmd.Addition {
			if cmd.ID > 256 || cmd.RefsCount > 256 {
				return s, nil, false
			}
			items, ok := rangeSlice(c.Pool, cmd.Start, cmd.Count)
			if !ok {
				return s, nil, false
			}
			clause := []int{}
			hints := []int{}
			meaning = append(meaning, 1, int64(cmd.ID), int64(len(items)))
			for _, v := range items {
				lit := rangeLiteral(v)
				clause = append(clause, lit)
				meaning = append(meaning, int64(lit))
			}
			meaning = append(meaning, int64(len(refs)))
			for _, id := range refs {
				hints = append(hints, int(id))
				meaning = append(meaning, int64(id))
			}
			s.Commands = append(s.Commands, streamAdd(cmd.ID, clause, hints...))
		} else {
			meaning = append(meaning, 0, int64(cmd.ID), int64(len(refs)))
			for _, id := range refs {
				meaning = append(meaning, int64(id))
			}
			s.Commands = append(s.Commands, streamDelete(cmd.ID, refs...))
		}
	}
	return s, meaning, true
}
func rangeFromStream(s streamCase) rangeCase {
	c := rangeCase{Variables: uint32(s.Variables), Pool: []uint32{}, Starts: []uint32{}, Sizes: []uint32{}, Refs: []uint32{}, Commands: []rangeCommand{}}
	for _, clause := range s.Database {
		c.Starts = append(c.Starts, uint32(len(c.Pool)))
		c.Sizes = append(c.Sizes, uint32(len(clause)))
		for _, lit := range clause {
			c.Pool = append(c.Pool, oakLiteral(lit))
		}
	}
	for _, cmd := range s.Commands {
		r := rangeCommand{Addition: cmd.Kind != "delete", ID: cmd.ID, Start: uint32(len(c.Pool)), RefsStart: uint32(len(c.Refs))}
		if r.Addition {
			r.Count = uint32(len(cmd.Clause))
			for _, lit := range cmd.Clause {
				c.Pool = append(c.Pool, oakLiteral(lit))
			}
			for _, id := range cmd.Hints {
				n := uint32(0)
				if id > 0 {
					n = uint32(id)
				}
				c.Refs = append(c.Refs, n)
			}
		} else {
			c.Refs = append(c.Refs, cmd.IDs...)
		}
		r.RefsCount = uint32(len(c.Refs)) - r.RefsStart
		c.Commands = append(c.Commands, r)
	}
	return c
}
func rangeTruthCheck(t *testing.T, s streamCase) {
	t.Helper()
	vars := []int{}
	seen := map[int]bool{}
	for _, clause := range s.Database {
		if len(clause) == 0 {
			return
		}
		for _, lit := range clause {
			if lit < 0 {
				lit = -lit
			}
			if !seen[lit] {
				seen[lit] = true
				vars = append(vars, lit)
			}
		}
	}
	if len(vars) > 12 {
		t.Fatal("accepted corpus case exceeds truth-table budget")
	}
	for mask := 0; mask < 1<<len(vars); mask++ {
		values := map[int]bool{}
		for i, v := range vars {
			values[v] = mask&(1<<i) != 0
		}
		sat := true
		for _, clause := range s.Database {
			holds := false
			for _, lit := range clause {
				v := lit
				if v < 0 {
					v = -v
				}
				holds = holds || values[v] == (lit > 0)
			}
			sat = sat && holds
		}
		if sat {
			t.Fatal("reference accepted a satisfiable initial database")
		}
	}
}
func rangeCorpus(t *testing.T) []rangeCase {
	out := []rangeCase{}
	add := func(name string, c rangeCase) {
		c.Name = name
		c.Pool = append([]uint32{}, c.Pool...)
		c.Starts = append([]uint32{}, c.Starts...)
		c.Sizes = append([]uint32{}, c.Sizes...)
		c.Refs = append([]uint32{}, c.Refs...)
		c.Commands = append([]rangeCommand{}, c.Commands...)
		s, meaning, ok := rangeDecode(c)
		c.Decoded = ok
		c.Meaning = meaning
		if c.Meaning == nil {
			c.Meaning = []int64{}
		}
		c.Accepted = ok && streamReference(s)
		if c.Accepted {
			rangeTruthCheck(t, s)
		}
		out = append(out, c)
	}
	for _, s := range streamCorpus(t) {
		c := rangeFromStream(s)
		add("stream-"+s.Name, c)
		if out[len(out)-1].Accepted != s.Expected {
			t.Fatal("layout changed existing stream semantics", s.Name)
		}
	}
	// Reuse actual decoder-layout cases from the preceding milestone.
	for _, b := range bufferCorpus() {
		if !b.Accepted {
			continue
		}
		f := b.Layout
		c := rangeCase{Variables: f[0]}
		at := 5
		c.Pool = f[at : at+int(f[1])]
		at += int(f[1])
		c.Starts = f[at : at+int(f[2])]
		at += int(f[2])
		c.Sizes = f[at : at+int(f[2])]
		at += int(f[2])
		c.Refs = f[at : at+int(f[3])]
		at += int(f[3])
		for i := uint32(0); i < f[4]; i++ {
			c.Commands = append(c.Commands, rangeCommand{f[at] == 1, f[at+1], f[at+2], f[at+3], f[at+4], f[at+5]})
			at += 6
		}
		add("buffer-"+b.Name, c)
	}
	for n := uint32(0); n < 128; n++ {
		add(fmt.Sprintf("literal-%d", n), rangeCase{Variables: 64, Pool: []uint32{n}, Starts: []uint32{0, 1}, Sizes: []uint32{1, 0}})
	}
	base := func() rangeCase {
		return rangeFromStream(streamCase{Variables: 3, Database: [][]int{{1}, {-1}}, Commands: []streamCommand{streamAdd(3, nil, 1, 2)}})
	}
	mutations := []struct {
		name   string
		change func(*rangeCase)
	}{
		{"reordered", func(c *rangeCase) { c.Starts = []uint32{1, 0} }},
		{"overlap", func(c *rangeCase) { c.Starts = []uint32{0, 0}; c.Sizes = []uint32{2, 2} }},
		{"bad-start", func(c *rangeCase) { c.Starts[0] = 4294967295 }},
		{"bad-count", func(c *rangeCase) { c.Sizes[0] = 4294967295 }},
		{"missing-size", func(c *rangeCase) { c.Sizes = c.Sizes[:1] }},
		{"bad-command-start", func(c *rangeCase) { c.Commands[0].Start = 3 }},
		{"bad-command-count", func(c *rangeCase) { c.Commands[0].Count = 4294967295 }},
		{"bad-ref-start", func(c *rangeCase) { c.Commands[0].RefsStart = 4294967295 }},
		{"bad-ref-count", func(c *rangeCase) { c.Commands[0].RefsCount = 4294967295 }},
		{"zero-reference", func(c *rangeCase) { c.Refs[0] = 0 }},
		{"large-reference", func(c *rangeCase) { c.Refs[0] = 257 }},
		{"unused-reference", func(c *rangeCase) { c.Refs = append(c.Refs, 4294967295) }},
		{"unused-invalid-literal", func(c *rangeCase) { c.Pool = append(c.Pool, 6) }},
		{"unused-valid-literal", func(c *rangeCase) { c.Pool = append(c.Pool, 5) }},
		{"zero-variables", func(c *rangeCase) { c.Variables = 0 }},
		{"large-variables", func(c *rangeCase) { c.Variables = 65 }},
		{"large-addition-id", func(c *rangeCase) { c.Commands[0].ID = 257 }},
		{"ignored-deletion-literal-range", func(c *rangeCase) {
			c.Commands = append(c.Commands, rangeCommand{false, 3, 4294967295, 4294967295, 2, 0})
		}},
		{"max-deletion-stamp", func(c *rangeCase) { c.Commands = append(c.Commands, rangeCommand{false, 2147483647, 0, 0, 2, 0}) }},
		{"overflow-deletion-stamp", func(c *rangeCase) { c.Commands = append(c.Commands, rangeCommand{false, 2147483648, 0, 0, 2, 0}) }},
	}
	for _, m := range mutations {
		c := base()
		m.change(&c)
		add(m.name, c)
	}
	for _, n := range []int{4096, 4097} {
		add(fmt.Sprintf("pool-%d", n), rangeCase{Variables: 1, Pool: make([]uint32, n), Starts: []uint32{0}, Sizes: []uint32{0}})
		add(fmt.Sprintf("refs-%d", n), rangeCase{Variables: 1, Refs: make([]uint32, n), Starts: []uint32{0}, Sizes: []uint32{0}})
	}
	for _, n := range []int{256, 257} {
		refs := make([]uint32, n)
		for i := range refs {
			refs[i] = 1
		}
		add(fmt.Sprintf("hint-count-%d", n), rangeCase{Variables: 1, Pool: []uint32{1, 0}, Starts: []uint32{0, 2}, Sizes: []uint32{1, 0}, Refs: refs, Commands: []rangeCommand{{true, 3, 0, 2, 0, uint32(n)}}})
	}
	return out
}
func TestSelfHostedRangeBridge(t *testing.T) {
	cases := rangeCorpus(t)
	accepted, decoded := 0, 0
	var source, main strings.Builder
	for _, path := range []string{"self_hosted_rup.oak", "self_hosted_stream.oak"} {
		data, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		source.Write(data)
		source.WriteByte('\n')
	}
	main.WriteString("main: (): i32 {\n")
	for i, c := range cases {
		fmt.Fprintf(&source, "range_case_%d: (): Bool {\n", i)
		for _, a := range []struct {
			name  string
			items []uint32
		}{{"pool", c.Pool}, {"starts", c.Starts}, {"sizes", c.Sizes}, {"refs", c.Refs}} {
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
		fmt.Fprintf(&source, "command_view: []RUPCommand = commands[0:%d]\nrup_stream_check(pool_view, starts_view, sizes_view, refs_view, command_view, u32(%d)) == %t\n}\n", len(c.Commands), c.Variables, c.Accepted)
		fmt.Fprintf(&main, "assert(range_case_%d())\n", i)
		if c.Accepted {
			accepted++
		}
		if c.Decoded {
			decoded++
		}
	}
	main.WriteString("42\n}\n")
	source.WriteString(main.String())
	runOakStream(t, source.String())
	if path := os.Getenv("OAK_RANGE_CORPUS_OUT"); path != "" {
		data, err := json.MarshalIndent(cases, "", "  ")
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, append(data, '\n'), 0644); err != nil {
			t.Fatal(err)
		}
	}
	t.Logf("Oak/Go range bridge: %d layouts (%d decoded, %d accepted, %d rejected)", len(cases), decoded, accepted, len(cases)-accepted)
}
