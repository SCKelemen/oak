package compiler

import (
	"fmt"
	"strings"
	"testing"
)

const oakLibraryPrelude = `
import(std)
filter_ok: (r: Result[Bool, FilterError]): Bool = r ? | .Ok(v) => v | .Err(e) => false
filter_code: (r: Result[Bool, FilterError]): u32 = r ?
 | .Ok(v) => u32(0)
 | .Err(e) => e ?
   | .InvalidConfig => u32(1)
   | .StorageTooSmall => u32(2)
   | .CounterOverflow => u32(3)
   | .NotPresent => u32(4)
   | .Incompatible => u32(5)
table_code: (r: Result[Bool, HashTableError]): u32 = r ?
 | .Ok(v) => (v ? u32(1) | u32(2))
 | .Err(e) => u32(3)
`

func oakLibraryRun(t *testing.T, source string) {
	t.Helper()
	c, err := New().WithSource("oaklibraries.oak", source).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, forbidden := range []string{"OAK_UNSUPPORTED", "OAK_UNRESOLVED", "malloc(", "calloc(", "realloc("} {
		if strings.Contains(c, forbidden) {
			t.Fatalf("generated C contains %q", forbidden)
		}
	}
	code, abnormal := buildAndRun(t, "oaklibraries", source)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func oakFilterMix(x uint64) uint64 {
	x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9
	x = (x ^ (x >> 27)) * 0x94d049bb133111eb
	return x ^ (x >> 31)
}

func oakFilterIndex(hash, seed uint64, cells, probe int, blocked bool) int {
	a := oakFilterMix(hash ^ seed)
	b := oakFilterMix(a+0x9e3779b97f4a7c15) | 1
	v := a + b*uint64(probe)
	if blocked {
		return int((a>>32)%uint64(cells/512))*512 + int(v%512)
	}
	return int(v % uint64(cells))
}

func TestE2EOakLibrariesFilters(t *testing.T) {
	skipInShort(t)
	for _, tc := range []struct {
		cells   int
		probes  int
		blocked bool
	}{{1, 64, false}, {67, 6, false}, {1024, 6, true}} {
		t.Run(fmt.Sprint(tc), func(t *testing.T) {
			var src strings.Builder
			src.WriteString(oakLibraryPrelude)
			n := (tc.cells + 7) / 8
			fmt.Fprintf(&src, "main: (): i32 {\ncfg: BloomConfig = BloomConfig { cells: u32(%d), probes: u32(%d), seed: u64(17), blocked: %t }\ndata: [%d]u8\ncounters: [%d]u8\n", tc.cells, tc.probes, tc.blocked, n+1, tc.cells+1)
			backing := make([]byte, n+1)
			counts := make([]byte, tc.cells+1)
			// Padding and unused storage must survive all filter operations.
			backing[n] = 165
			counts[tc.cells] = 165
			fmt.Fprintf(&src, "data[%d] = u8(165)\ncounters[%d] = u8(165)\n", n, tc.cells)
			for hash := uint64(0); hash < 18; hash++ {
				fmt.Fprintf(&src, "true ? {\ns: [*]u8 = span(&data)\nc: [*]u8 = span(&counters)\nassert(filter_code(bloom_insert(s, cfg, u64(%d))) == u32(0))\nassert(filter_ok(counting_bloom_update(c, cfg, u64(%d), true)))\n}\n", hash, hash)
				seen := map[int]bool{}
				for p := 0; p < tc.probes; p++ {
					i := oakFilterIndex(hash, 17, tc.cells, p, tc.blocked)
					backing[i/8] |= 1 << (i % 8)
					if !seen[i] {
						counts[i]++
						seen[i] = true
					}
				}
			}
			for i, v := range backing {
				fmt.Fprintf(&src, "assert(data[%d] == u8(%d))\n", i, v)
			}
			for i, v := range counts {
				fmt.Fprintf(&src, "assert(counters[%d] == u8(%d))\n", i, v)
			}
			src.WriteString("true ? {\nv: []u8 = view(&data)\nc: []u8 = view(&counters)\n")
			for hash := uint64(0); hash < 50; hash++ {
				present, counted := true, true
				for p := 0; p < tc.probes; p++ {
					i := oakFilterIndex(hash, 17, tc.cells, p, tc.blocked)
					present = present && backing[i/8]&(1<<(i%8)) != 0
					counted = counted && counts[i] > 0
				}
				fmt.Fprintf(&src, "assert(filter_ok(bloom_query(v, cfg, u64(%d))) == %t)\nassert(filter_ok(counting_bloom_query(c, cfg, u64(%d))) == %t)\n", hash, present, hash, counted)
			}
			src.WriteString("}\ntrue ? {\nc: [*]u8 = span(&counters)\n")
			for hash := uint64(0); hash < 18; hash++ {
				fmt.Fprintf(&src, "assert(filter_ok(counting_bloom_update(c, cfg, u64(%d), false)))\n", hash)
			}
			src.WriteString("}\n")
			for i := 0; i < tc.cells; i++ {
				fmt.Fprintf(&src, "assert(counters[%d] == u8(0))\n", i)
			}
			fmt.Fprintf(&src, "assert(counters[%d] == u8(165))\ntrue ? {\ns: [*]u8 = span(&data)\nassert(filter_ok(bloom_clear(s, cfg)))\n}\n", tc.cells)
			for i := 0; i < n; i++ {
				fmt.Fprintf(&src, "assert(data[%d] == u8(0))\n", i)
			}
			fmt.Fprintf(&src, "assert(data[%d] == u8(165))\n42\n}\n", n)
			oakLibraryRun(t, src.String())
		})
	}
}

func TestE2EOakLibrariesFilterFailures(t *testing.T) {
	oakLibraryRun(t, oakLibraryPrelude+`
main: (): i32 {
 cfg: BloomConfig = BloomConfig { cells: u32(1), probes: u32(64), seed: u64(0), blocked: false }
 bad: BloomConfig = BloomConfig { cells: u32(0), probes: u32(0), seed: u64(0), blocked: false }
 undersized: BloomConfig = BloomConfig { cells: u32(17), probes: u32(6), seed: u64(0), blocked: false }
 blocked: BloomConfig = BloomConfig { cells: u32(1), probes: u32(6), seed: u64(0), blocked: true }
 data: [2]u8
 s: [*]u8 = span(&data)
 s[0] = u8(254)
 s[1] = u8(165)
 assert(filter_code(counting_bloom_update(s, cfg, u64(9), true)) == u32(0))
 assert(s[0] == u8(255))
 assert(filter_code(counting_bloom_update(s, cfg, u64(9), true)) == u32(3))
 assert(s[0] == u8(255))
 assert(filter_code(bloom_insert(s, bad, u64(9))) == u32(1))
 assert(filter_code(bloom_insert(s, blocked, u64(9))) == u32(1))
 assert(filter_code(bloom_insert(s, undersized, u64(9))) == u32(2))
 assert(filter_code(counting_bloom_update(s, undersized, u64(9), true)) == u32(2))
 assert(s[0] == u8(255))
 assert(s[1] == u8(165))
 assert(filter_ok(bloom_clear(s, cfg)))
 assert(s[0] == u8(254))
 s[0] = u8(0)
 assert(filter_code(counting_bloom_update(s, cfg, u64(9), false)) == u32(4))
 assert(s[0] == u8(0))
 assert(s[1] == u8(165))
 42
}
`)
}

func TestE2EOakLibrariesHashTable(t *testing.T) {
	skipInShort(t)
	for _, capacity := range []int{1, 7} {
		t.Run(fmt.Sprint(capacity), func(t *testing.T) {
			var src strings.Builder
			src.WriteString(oakLibraryPrelude)
			fmt.Fprintf(&src, "Entry: type = struct { key: u64, state: u8, value: u32 }\nmain: (): i32 {\ndata: [%d]Entry\n", capacity)
			// All keys share their initial bucket, including a cluster wrapping at the end.
			keys := []uint64{}
			for k := uint64(0); len(keys) < capacity+2; k++ {
				if oakFilterMix(k)%uint64(capacity) == uint64(capacity-1) {
					keys = append(keys, k)
				}
			}
			model := map[uint64]uint32{}
			seed := uint32(45)
			for step := 0; step < 100; step++ {
				seed = seed*1664525 + 1013904223
				key := keys[int(seed>>16)%len(keys)]
				op := int(seed>>28) % 5
				src.WriteString("true ? {\ns: [*]Entry = span(&data)\n")
				switch op {
				case 0, 1, 2:
					_, existed := model[key]
					code := 1
					if existed {
						code = 2
					} else if len(model) == capacity {
						code = 3
					}
					if code != 3 {
						model[key] = seed >> 8
					}
					fmt.Fprintf(&src, "item: Entry = Entry { key: u64(%d), state: u8(99), value: u32(%d) }\nassert(table_code(hash_table_put(s, item)) == u32(%d))\n", key, seed>>8, code)
				case 3:
					_, existed := model[key]
					delete(model, key)
					fmt.Fprintf(&src, "assert(hash_table_remove(s, u64(%d)) == %t)\n", key, existed)
				case 4:
					if step%9 == 0 {
						src.WriteString("hash_table_clear(s)\n")
						clear(model)
					}
				}
				src.WriteString("}\ntrue ? {\nv: []Entry = view(&data)\n")
				fmt.Fprintf(&src, "assert(hash_table_count(v) == u32(%d))\n", len(model))
				for i, k := range keys {
					value, found := model[k]
					fmt.Fprintf(&src, "r%d: Option[u32] = hash_table_find(v, u64(%d))\nf%d: Bool = r%d ? | .Some(index) => true | .None => false\nassert(f%d == %t)\n", i, k, i, i, i, found)
					if found {
						fmt.Fprintf(&src, "ix%d: u32 = option_or(r%d, u32(4294967295))\nassert(v[ix%d].value == u32(%d))\n", i, i, i, value)
					}
				}
				src.WriteString("}\n")
			}
			src.WriteString("42\n}\n")
			oakLibraryRun(t, src.String())
		})
	}
}

func TestE2EOakLibrariesBitsAndSet(t *testing.T) {
	oakLibraryRun(t, oakLibraryPrelude+`
bits_ok: (r: Result[Bool, BitSetError]): Bool = r ? | .Ok(v) => v | .Err(e) => false
flag_value: (r: Result[FlagBits, FlagError]): FlagBits = r ?
 | .Ok(v) => v
 | .Err(e) => FlagBits { bits: u64(0), allowed: u64(0) }
flag_error: (r: Result[FlagBits, FlagError]): Bool = r ? | .Ok(v) => false | .Err(e) => true
found_bit: (r: Result[Option[u32], BitSetError]): u32 = r ?
 | .Ok(v) => option_or(v, u32(99))
 | .Err(e) => u32(98)
main: (): i32 {
 data: [3]u8
 other: [2]u8
 data[0] = u8(5)
 data[1] = u8(254)
 data[2] = u8(165)
 other[0] = u8(6)
 other[1] = u8(1)
 true ? {
  s: [*]u8 = span(&data)
  v: []u8 = view(&other)
  assert(bits_ok(bitset_combine(s, v, u32(9), .Union)))
  assert(s[0] == u8(7))
  assert(s[1] == u8(255))
  assert(bits_ok(bitset_combine(s, v, u32(9), .Difference)))
  assert(s[0] == u8(1))
  assert(s[1] == u8(254))
  assert(bits_ok(bitset_combine(s, v, u32(9), .SymmetricDifference)))
  assert(s[0] == u8(7))
  assert(s[1] == u8(255))
  assert(bits_ok(bitset_combine(s, v, u32(9), .Intersection)))
  assert(s[0] == u8(6))
  assert(s[1] == u8(255))
  assert(s[2] == u8(165))
 }
 true ? {
  v: []u8 = view(&data)
  assert(found_bit(bitset_find_next(v, u32(9), u32(0), true)) == u32(1))
  assert(found_bit(bitset_find_next(v, u32(9), u32(3), true)) == u32(8))
  assert(found_bit(bitset_find_next(v, u32(9), u32(9), true)) == u32(99))
  assert(found_bit(bitset_find_next(v, u32(9), u32(0), false)) == u32(0))
 }
 f: FlagBits = flag_value(flags_create(u64(1), u64(7)))
 assert(flags_contains_all(f, u64(1)))
 assert(!flags_contains_any(f, u64(2)))
 assert(flag_error(flags_create(u64(8), u64(7))))
 assert(flag_error(flags_update(f, u64(8), true)))
 g: FlagBits = flag_value(flags_update(f, u64(6), true))
 assert(g.bits == u64(7))
 h: FlagBits = flag_value(flags_update(g, u64(2), false))
 assert(h.bits == u64(5))
 assert(!flags_contains_all(h, u64(8)))
 slots: [2]HashSetSlot
 true ? {
  s: [*]HashSetSlot = span(&slots)
  assert(table_code(hash_set_insert(s, u64(0))) == u32(1))
  assert(table_code(hash_set_insert(s, u64(0))) == u32(2))
  assert(table_code(hash_set_insert(s, u64(1))) == u32(1))
  assert(table_code(hash_set_insert(s, u64(2))) == u32(3))
  assert(hash_set_remove(s, u64(0)))
  assert(table_code(hash_set_insert(s, u64(2))) == u32(1))
 }
 true ? {
  v: []HashSetSlot = view(&slots)
  assert(!hash_set_contains(v, u64(0)))
  assert(hash_set_contains(v, u64(1)))
  assert(hash_set_contains(v, u64(2)))
 }
 42
}
`)
}

func TestE2EOakLibrariesBoundaries(t *testing.T) {
	var src strings.Builder
	src.WriteString(oakLibraryPrelude)
	src.WriteString(`
main: (): i32 {
 high: u64 = u64(1) << u64(63)
`)
	for _, value := range []uint64{0, 1, 0x8000000000000000, 0xffffffffffffffff, 0x123456789abcdef0} {
		want := oakFilterMix(value)
		fmt.Fprintf(&src, "assert(filter_mix((u64(%d) << u64(32)) | u64(%d)) == ((u64(%d) << u64(32)) | u64(%d)))\n", value>>32, uint32(value), want>>32, uint32(want))
	}
	src.WriteString(`
 cfg: BloomConfig = BloomConfig { cells: u32(17), probes: u32(6), seed: u64(17), blocked: false }
 counters: [18]u8
 s: [*]u8 = span(&counters)
 i: u32 = 0
 while i < u32(18) { s[i] = u8(7); i = i + u32(1) }
 last: u32 = filter_index(cfg, u64(0), u32(5))
 s[last] = u8(255)
 assert(filter_code(counting_bloom_update(s, cfg, u64(0), true)) == u32(3))
 i = u32(0)
 while i < u32(18) {
  expected: u8 = i == last ? u8(255) | u8(7)
  assert(s[i] == expected)
  i = i + u32(1)
 }
 s[last] = u8(0)
 assert(filter_code(counting_bloom_update(s, cfg, u64(0), false)) == u32(4))
 i = u32(0)
 while i < u32(18) {
  after: u8 = i == last ? u8(0) | u8(7)
  assert(s[i] == after)
  i = i + u32(1)
 }
 one: [1]HashSetSlot
 q: [*]HashSetSlot = span(&one)
 assert(table_code(hash_set_insert(q, high)) == u32(1))
 assert(table_code(hash_set_insert(q, high)) == u32(2))
 assert(table_code(hash_set_insert(q, u64(0))) == u32(3))
 assert(q[0].key == high)
 assert(hash_set_remove(q, high))
 assert(table_code(hash_set_insert(q, u64(0))) == u32(1))
 assert(hash_set_remove(q, u64(0)))
 assert(!hash_set_remove(q, u64(0)))
 42
}
`)
	oakLibraryRun(t, src.String())
}
