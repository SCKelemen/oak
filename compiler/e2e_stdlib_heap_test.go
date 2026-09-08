package compiler

import (
	"fmt"
	"sort"
	"strings"
	"testing"
)

const heapTestPrelude = collectionTestPrelude + `
Job: type = struct { priority: u64, value: u32 }
job_code: (result: Result[Job, CollectionError]): u32 = result ?
 | .Ok(entry) => u32(0)
 | .Err(reason) => error_code(reason)
job_value: (result: Result[Job, CollectionError]): u32 = result ?
 | .Ok(entry) => entry.value
 | .Err(reason) => u32(4294967295)
job_priority: (result: Result[Job, CollectionError]): u64 = result ?
 | .Ok(entry) => entry.priority
 | .Err(reason) => u64(0)
`

func TestE2EStdlibMinHeapTrace(t *testing.T) {
	type entry struct {
		priority uint64
		value    uint32
	}
	for _, capacity := range []int{1, 4, 9} {
		t.Run(fmt.Sprint(capacity), func(t *testing.T) {
			var src strings.Builder
			src.WriteString(heapTestPrelude)
			fmt.Fprintf(&src, "main: (): i32 {\ndata: [%d]Job\nstate: [1]MinHeapCursor\nq: [*]MinHeapCursor = span(&state)\n", capacity)
			var model []entry
			seed := uint32(8831)
			for step := 0; step < 90; step++ {
				seed = seed*1664525 + 1013904223
				priority := uint64(seed%31)*1000 + uint64(step)
				value := uint32(step + 1)
				op := seed >> 28
				failed := false
				src.WriteString("true ? {\ns: [*]Job = span(&data)\n")
				fmt.Fprintf(&src, "snapshot: [%d]Job\ni: u32 = 0\nwhile i < u32(%d) { snapshot[i] = s[i]\ni = i + u32(1) }\n", capacity, capacity)
				fmt.Fprintf(&src, "item: Job = Job { priority: u64(%d), value: u32(%d) }\n", priority, value)
				switch {
				case op < 8:
					src.WriteString("r: Result[u32, CollectionError] = min_heap_push(q, s, item)\n")
					if len(model) == capacity {
						src.WriteString("assert(result_code(r) == u32(1))\n")
						failed = true
					} else {
						model = append(model, entry{priority, value})
						fmt.Fprintf(&src, "assert(result_code(r) == u32(0) && result_value(r) == u32(%d))\n", len(model))
					}
				case op < 12:
					src.WriteString("r: Result[Job, CollectionError] = min_heap_pop(q, s)\n")
					if len(model) == 0 {
						src.WriteString("assert(job_code(r) == u32(2))\n")
						failed = true
					} else {
						fmt.Fprintf(&src, "assert(job_code(r) == u32(0) && job_value(r) == u32(%d) && job_priority(r) == u64(%d))\n", model[0].value, model[0].priority)
						model = model[1:]
					}
				case op < 15:
					src.WriteString("r: Result[Job, CollectionError] = min_heap_replace_top(q, s, item)\n")
					if len(model) == 0 {
						src.WriteString("assert(job_code(r) == u32(2))\n")
						failed = true
					} else {
						fmt.Fprintf(&src, "assert(job_code(r) == u32(0) && job_value(r) == u32(%d) && job_priority(r) == u64(%d))\n", model[0].value, model[0].priority)
						model[0] = entry{priority, value}
					}
				default:
					fmt.Fprintf(&src, "min_heap_clear(q, u32(%d))\n", capacity)
					model = nil
					failed = true // Logical clear also preserves the backing bytes.
				}
				if failed {
					for i := 0; i < capacity; i++ {
						fmt.Fprintf(&src, "assert(s[%d].priority == snapshot[%d].priority && s[%d].value == snapshot[%d].value)\n", i, i, i, i)
					}
				}
				src.WriteString("}\n")
				sort.Slice(model, func(i, j int) bool { return model[i].priority < model[j].priority })
				fmt.Fprintf(&src, "assert(q[0].length == u32(%d))\ntrue ? {\nv: []Job = view(&data)\nmin_heap_validate(q, v)\nr: Result[Job, CollectionError] = min_heap_peek(q, v)\n", len(model))
				if len(model) == 0 {
					src.WriteString("assert(job_code(r) == u32(2))\n")
				} else {
					fmt.Fprintf(&src, "assert(job_code(r) == u32(0) && job_value(r) == u32(%d) && job_priority(r) == u64(%d))\n", model[0].value, model[0].priority)
				}
				// Each expected entry must occur exactly once in the live prefix.
				for _, expected := range model {
					fmt.Fprintf(&src, "true ? {\nfound: u32 = 0\ni: u32 = 0\nwhile i < q[0].length {\nv[i].value == u32(%d) && v[i].priority == u64(%d) ? { found = found + u32(1) }\ni = i + u32(1) }\nassert(found == u32(1))\n}\n", expected.value, expected.priority)
				}
				src.WriteString("}\n")
			}
			src.WriteString("true ? {\ns: [*]Job = span(&data)\n")
			for _, expected := range model {
				fmt.Fprintf(&src, "assert(job_value(min_heap_pop(q, s)) == u32(%d))\n", expected.value)
			}
			src.WriteString("}\nassert(q[0].length == u32(0))\n42\n}\n")
			code, abnormal := buildAndRun(t, "heaptrace", src.String())
			if abnormal || code != 42 {
				t.Fatalf("exit=(%d,%v)", code, abnormal)
			}
		})
	}
}

func TestE2EStdlibMinHeapBuild(t *testing.T) {
	for _, count := range []int{0, 1, 2, 3, 8, 9} {
		t.Run(fmt.Sprint(count), func(t *testing.T) {
			var src strings.Builder
			src.WriteString(heapTestPrelude)
			src.WriteString("main: (): i32 {\ndata: [10]Job\nstate: [1]MinHeapCursor\nq: [*]MinHeapCursor = span(&state)\ns: [*]Job = span(&data)\n")
			for i := 0; i < 10; i++ {
				fmt.Fprintf(&src, "s[%d].priority = u64(%d)\ns[%d].value = u32(%d)\n", i, 10-i, i, 10-i)
			}
			fmt.Fprintf(&src, "built: Result[u32, CollectionError] = min_heap_build(q, s, u32(%d))\nassert(result_code(built) == u32(0) && result_value(built) == u32(%d))\n", count, count)
			for i := count; i < 10; i++ {
				fmt.Fprintf(&src, "assert(s[%d].value == u32(%d) && s[%d].priority == u64(%d))\n", i, 10-i, i, 10-i)
			}
			src.WriteString("snapshot: [10]Job\ni: u32 = 0\nwhile i < u32(10) { snapshot[i] = s[i]\ni = i + u32(1) }\n")
			for _, invalid := range []uint32{11, ^uint32(0)} {
				fmt.Fprintf(&src, "assert(result_code(min_heap_build(q, s, u32(%d))) == u32(3))\nassert(q[0].length == u32(%d))\n", invalid, count)
			}
			for i := 0; i < 10; i++ {
				fmt.Fprintf(&src, "assert(s[%d].priority == snapshot[%d].priority && s[%d].value == snapshot[%d].value)\n", i, i, i, i)
			}
			for want := 11 - count; want <= 10; want++ {
				fmt.Fprintf(&src, "assert(job_value(min_heap_pop(q, s)) == u32(%d))\n", want)
			}
			src.WriteString("assert(q[0].length == u32(0))\n42\n}\n")
			code, abnormal := buildAndRun(t, "heapbuild", src.String())
			if abnormal || code != 42 {
				t.Fatalf("exit=(%d,%v)", code, abnormal)
			}
		})
	}
}

func TestE2EStdlibMinHeapTiesAndUnsignedRange(t *testing.T) {
	src := heapTestPrelude + `
main: (): i32 {
 data: [5]Job
 state: [1]MinHeapCursor
 s: [*]Job = span(&data)
 q: [*]MinHeapCursor = span(&state)
 high: u64 = u64(1) << u64(63)
 maximum: u64 = (high | (high - u64(1)))
 s[0] = Job { priority: maximum, value: u32(40) }
 s[1] = Job { priority: high, value: u32(10) }
 s[2] = Job { priority: u64(0), value: u32(0) }
 s[3] = Job { priority: high, value: u32(20) }
 s[4] = Job { priority: maximum - u64(1), value: u32(30) }
 built: Result[u32, CollectionError] = min_heap_build(q, s, u32(5))
 assert(result_value(built) == u32(5))
 first: Result[Job, CollectionError] = min_heap_pop(q, s)
 assert(job_value(first) == u32(0) && job_priority(first) == u64(0))
 a: Result[Job, CollectionError] = min_heap_pop(q, s)
 b: Result[Job, CollectionError] = min_heap_pop(q, s)
 assert(job_priority(a) == high && job_priority(b) == high)
 assert(job_value(a) != job_value(b))
 assert(job_value(a) == u32(10) || job_value(a) == u32(20))
 assert(job_value(b) == u32(10) || job_value(b) == u32(20))
 fourth: Result[Job, CollectionError] = min_heap_pop(q, s)
 fifth: Result[Job, CollectionError] = min_heap_pop(q, s)
 assert(job_value(fourth) == u32(30) && job_priority(fourth) == maximum - u64(1))
 assert(job_value(fifth) == u32(40) && job_priority(fifth) == maximum)
 assert(job_code(min_heap_pop(q, s)) == u32(2))
 other: [1]Job
 other_state: [1]MinHeapCursor
 t: [*]Job = span(&other)
 p: [*]MinHeapCursor = span(&other_state)
 low: Job = Job { priority: u64(1), value: u32(7) }
 big: Job = Job { priority: maximum, value: u32(9) }
 assert(result_code(min_heap_push(q, s, big)) == u32(0))
 assert(result_code(min_heap_push(p, t, low)) == u32(0))
 assert(job_value(min_heap_pop(q, s)) == u32(9))
 assert(p[0].length == u32(1))
 assert(job_value(min_heap_pop(p, t)) == u32(7))
 42
}
`
	output, err := New().WithSource("heaprange.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "OAK_UNSUPPORTED"} {
		if strings.Contains(output, forbidden) {
			t.Fatalf("unexpected %s in emitted C", forbidden)
		}
	}
	code, abnormal := buildAndRun(t, "heaprange", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestStdlibMinHeapRejectsInvalidEntry(t *testing.T) {
	for _, fields := range []string{"value: u32", "priority: u32, value: u32"} {
		src := "import(std)\nBad: type = struct { " + fields + " }\nmain: (): i32 {\ndata: [1]Bad\nstate: [1]MinHeapCursor\ns: [*]Bad = span(&data)\nq: [*]MinHeapCursor = span(&state)\nr: Result[u32, CollectionError] = min_heap_build(q, s, u32(1))\n0\n}"
		if _, err := New().WithSource("badheap.oak", src).EmitC().Get(); err == nil {
			t.Fatal("heap entry must have a u64 priority")
		}
	}
}

func TestE2EStdlibMinHeapGuards(t *testing.T) {
	for _, body := range []string{
		"q[0].length = u32(3)\nr: Result[Job, CollectionError] = min_heap_peek(q, v)",
		"q[0].length = u32(2)\nmin_heap_validate(q, v)",
	} {
		src := heapTestPrelude + "main: (): i32 {\ndata: [2]Job\ndata[0].priority = u64(2)\ndata[1].priority = u64(1)\nstate: [1]MinHeapCursor\nq: [*]MinHeapCursor = span(&state)\nv: []Job = view(&data)\n" + body + "\n0\n}"
		_, abnormal := buildAndRun(t, "heapguard", src)
		if !abnormal {
			t.Fatal("invalid heap state must trap")
		}
	}
}
