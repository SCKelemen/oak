package compiler

import (
	"fmt"
	"strings"
	"testing"
)

const collectionTestPrelude = `
import(std)
error_code: (reason: CollectionError): u32 = reason ?
 | .Full => u32(1)
 | .Empty => u32(2)
 | .OutOfBounds => u32(3)
 | .AlreadyLinked => u32(4)
 | .NotMember => u32(5)
result_code: (result: Result[u32, CollectionError]): u32 = result ?
 | .Ok(value) => u32(0)
 | .Err(reason) => error_code(reason)
result_value: (result: Result[u32, CollectionError]): u32 = result ?
 | .Ok(value) => value
 | .Err(reason) => u32(4294967295)
`

func TestE2EStdlibArrayListTrace(t *testing.T) {
	for _, capacity := range []int{1, 4, 9} {
		t.Run(fmt.Sprint(capacity), func(t *testing.T) {
			var src strings.Builder
			src.WriteString(collectionTestPrelude)
			fmt.Fprintf(&src, "main: (): i32 {\ndata: [%d]u32\nstate: [1]ArrayListCursor\nq: [*]ArrayListCursor = span(&state)\n", capacity)
			backing := make([]uint32, capacity)
			n := 0
			seed := uint32(345)
			for step := 0; step < 100; step++ {
				seed = seed*1664525 + 1013904223
				op := int(seed>>28) % 8
				index := int(seed>>8) % (capacity + 2)
				value := seed >> 16
				code, result := 0, uint32(0)
				src.WriteString("true ? {\ns: [*]u32 = span(&data)\n")
				switch op {
				case 0, 1:
					fmt.Fprintf(&src, "r: Result[u32, CollectionError] = array_list_push(q, s, u32(%d))\n", value)
					if n == capacity {
						code = 1
					} else {
						result = uint32(n)
						backing[n] = value
						n++
					}
				case 2:
					fmt.Fprintf(&src, "r: Result[u32, CollectionError] = array_list_insert(q, s, u32(%d), u32(%d))\n", index, value)
					if index > n {
						code = 3
					} else if n == capacity {
						code = 1
					} else {
						copy(backing[index+1:n+1], backing[index:n])
						backing[index] = value
						n++
						result = uint32(index)
					}
				case 3, 4, 5:
					name := map[int]string{3: "remove", 4: "swap_remove", 5: "set"}[op]
					fmt.Fprintf(&src, "r: Result[u32, CollectionError] = array_list_%s(q, s, u32(%d)", name, index)
					if op == 5 {
						fmt.Fprintf(&src, ", u32(%d)", value)
					}
					src.WriteString(")\n")
					if index >= n {
						code = 3
					} else {
						result = backing[index]
						switch op {
						case 3:
							copy(backing[index:n-1], backing[index+1:n])
							n--
						case 4:
							backing[index] = backing[n-1]
							n--
						case 5:
							backing[index] = value
						}
					}
				case 6:
					src.WriteString("r: Result[u32, CollectionError] = array_list_pop(q, s)\n")
					if n == 0 {
						code = 2
					} else {
						n--
						result = backing[n]
					}
				case 7:
					fmt.Fprintf(&src, "array_list_clear(q, u32(%d))\nr: Result[u32, CollectionError] = .Ok(u32(0))\n", capacity)
					n = 0
				}
				fmt.Fprintf(&src, "assert(result_code(r) == u32(%d))\n", code)
				if code == 0 {
					fmt.Fprintf(&src, "assert(result_value(r) == u32(%d))\n", result)
				}
				src.WriteString("}\n")
				fmt.Fprintf(&src, "assert(q[0].length == u32(%d))\n", n)
				for i, value := range backing {
					fmt.Fprintf(&src, "assert(data[%d] == u32(%d))\n", i, value)
				}
				src.WriteString("true ? {\nv: []u32 = view(&data)\n")
				for i := 0; i <= n; i++ {
					expected := uint32(4294967295)
					if i < n {
						expected = backing[i]
					}
					fmt.Fprintf(&src, "assert(result_value(array_list_get(q, v, u32(%d))) == u32(%d))\n", i, expected)
				}
				src.WriteString("}\n")
			}
			src.WriteString("42\n}\n")
			code, abnormal := buildAndRun(t, "arraylisttrace", src.String())
			if abnormal || code != 42 {
				t.Fatalf("exit=(%d,%v)", code, abnormal)
			}
		})
	}
}

func TestE2EStdlibIntrusiveTrace(t *testing.T) {
	for _, family := range []string{"slist", "dlist"} {
		t.Run(family, func(t *testing.T) {
			var src strings.Builder
			src.WriteString(collectionTestPrelude)
			src.WriteString("Task: type = struct { value: u32, slist: SListHook, dlist: DListHook }\nmain: (): i32 {\npool: [7]Task\na: [1]IntrusiveCursor\nb: [1]IntrusiveCursor\ns: [*]Task = span(&pool)\nqa: [*]IntrusiveCursor = span(&a)\nqb: [*]IntrusiveCursor = span(&b)\nintrusive_init(qa, u32(1))\nintrusive_init(qb, u32(2))\n")
			for i := 0; i < 7; i++ {
				fmt.Fprintf(&src, "s[%d].value = u32(%d)\n", i, i+100)
			}
			lists := [2][]int{}
			owners := [7]int{}
			seed := uint32(987)
			for step := 0; step < 140; step++ {
				seed = seed*1664525 + 1013904223
				which := int(seed>>16) % 2
				q := []string{"qa", "qb"}[which]
				index := int(seed>>8) % 9
				op := int(seed >> 28)
				name := "remove"
				if op < 4 {
					name = "push_front"
				} else if op < 9 {
					name = "push_back"
				} else if op < 12 {
					name = "pop_front"
				} else if op == 12 && family == "dlist" {
					name = "pop_back"
				}
				code := 0
				src.WriteString("true ? {\n")
				fmt.Fprintf(&src, "r: Result[u32, CollectionError] = %s_%s(%s, s", family, name, q)
				if !strings.HasPrefix(name, "pop") {
					fmt.Fprintf(&src, ", u32(%d)", index)
				}
				src.WriteString(")\n")
				if strings.HasPrefix(name, "pop") {
					if len(lists[which]) == 0 {
						code = 2
					} else if name == "pop_front" {
						index = lists[which][0]
						lists[which] = lists[which][1:]
						owners[index] = 0
					} else {
						index = lists[which][len(lists[which])-1]
						lists[which] = lists[which][:len(lists[which])-1]
						owners[index] = 0
					}
				} else if index >= 7 {
					code = 3
				} else if strings.HasPrefix(name, "push") {
					if owners[index] != 0 {
						code = 4
					} else {
						owners[index] = which + 1
						if name == "push_front" {
							lists[which] = append([]int{index}, lists[which]...)
						} else {
							lists[which] = append(lists[which], index)
						}
					}
				} else if owners[index] != which+1 {
					code = 5
				} else {
					for i, member := range lists[which] {
						if member == index {
							lists[which] = append(lists[which][:i], lists[which][i+1:]...)
							break
						}
					}
					owners[index] = 0
				}
				fmt.Fprintf(&src, "assert(result_code(r) == u32(%d))\n", code)
				if code == 0 {
					fmt.Fprintf(&src, "assert(result_value(r) == u32(%d))\n", index)
				}
				src.WriteString("}\n")
				next, prev := [7]int{}, [7]int{}
				for k, list := range lists {
					qname := []string{"qa", "qb"}[k]
					head, tail := 0, 0
					if len(list) > 0 {
						head, tail = list[0]+1, list[len(list)-1]+1
					}
					fmt.Fprintf(&src, "%s_validate(%s, s)\nassert(%s[0].head == u32(%d) && %s[0].tail == u32(%d) && %s[0].count == u32(%d))\n", family, qname, qname, head, qname, tail, qname, len(list))
					for i, member := range list {
						if i+1 < len(list) {
							next[member] = list[i+1] + 1
						}
						if i > 0 {
							prev[member] = list[i-1] + 1
						}
					}
				}
				for i := 0; i < 7; i++ {
					fmt.Fprintf(&src, "assert(s[%d].%s.owner == u32(%d) && s[%d].%s.next == u32(%d) && s[%d].value == u32(%d))\n", i, family, owners[i], i, family, next[i], i, i+100)
					if family == "dlist" {
						fmt.Fprintf(&src, "assert(s[%d].dlist.prev == u32(%d))\n", i, prev[i])
					}
				}
			}
			src.WriteString("42\n}\n")
			code, abnormal := buildAndRun(t, "intrusivetrace", src.String())
			if abnormal || code != 42 {
				t.Fatalf("exit=(%d,%v)", code, abnormal)
			}
		})
	}
}

func TestE2EStdlibIntrusiveIndependentHooks(t *testing.T) {
	src := collectionTestPrelude + `
Task: type = struct { value: u32, slist: SListHook, dlist: DListHook }
main: (): i32 {
 pool: [2]Task
 ready: [1]IntrusiveCursor
 timer: [1]IntrusiveCursor
 s: [*]Task = span(&pool)
 q: [*]IntrusiveCursor = span(&ready)
 t: [*]IntrusiveCursor = span(&timer)
 intrusive_init(q, u32(1))
 intrusive_init(t, u32(1))
 s[0].value = u32(42)
 assert(result_code(intrusive_queue_push(q, s, u32(0))) == u32(0))
 assert(result_code(intrusive_queue_push(q, s, u32(1))) == u32(0))
 assert(result_code(dlist_push_back(t, s, u32(0))) == u32(0))
 assert(result_value(intrusive_queue_pop(q, s)) == u32(0))
 assert(s[0].slist.owner == u32(0) && s[0].dlist.owner == u32(1))
 assert(result_value(intrusive_queue_pop(q, s)) == u32(1))
 assert(result_code(intrusive_queue_pop(q, s)) == u32(2))
 assert(result_value(dlist_pop_back(t, s)) == u32(0))
 assert(s[0].slist.next == u32(0) && s[0].dlist.prev == u32(0) && s[0].dlist.next == u32(0) && s[0].dlist.owner == u32(0))
 assert(result_code(intrusive_queue_push(q, s, u32(0))) == u32(0))
 assert(result_value(intrusive_queue_pop(q, s)) == u32(0))
 slist_validate(q, s)
 dlist_validate(t, s)
 i32(s[0].value)
}
`
	output, err := New().WithSource("intrusivehooks.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "OAK_UNSUPPORTED"} {
		if strings.Contains(output, forbidden) {
			t.Fatalf("unexpected %s in intrusive C", forbidden)
		}
	}
	code, abnormal := buildAndRun(t, "intrusivehooks", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EStdlibArrayListRecordValues(t *testing.T) {
	src := `
import(std)
Point: type = struct { x: u32, y: u32 }
main: (): i32 {
 data: [2]Point
 state: [1]ArrayListCursor
 s: [*]Point = span(&data)
 q: [*]ArrayListCursor = span(&state)
 point: Point = Point { x: u32(11), y: u32(31) }
 inserted: Result[u32, CollectionError] = array_list_push(q, s, point)
 popped: Result[Point, CollectionError] = array_list_pop(q, s)
 popped ? | .Ok(p) => i32(p.x + p.y) | .Err(e) => 0
}
`
	code, abnormal := buildAndRun(t, "arraylistrecord", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestStdlibIntrusiveRejectsMissingHook(t *testing.T) {
	src := `
import(std)
Task: type = struct { value: u32 }
main: (): i32 {
 pool: [1]Task
 state: [1]IntrusiveCursor
 s: [*]Task = span(&pool)
 q: [*]IntrusiveCursor = span(&state)
 intrusive_init(q, u32(1))
 r: Result[u32, CollectionError] = slist_push_back(q, s, u32(0))
 0
}
`
	if _, err := New().WithSource("missinghook.oak", src).EmitC().Get(); err == nil {
		t.Fatal("node without required hook must fail compilation")
	}
}

func TestE2EStdlibIntrusiveCorruptionTraps(t *testing.T) {
	for _, corruption := range []string{
		"s[0].slist.next = u32(1)",
		"s[0].slist.next = u32(99)",
		"s[0].slist.owner = u32(2)",
	} {
		src := collectionTestPrelude + `
Task: type = struct { slist: SListHook }
main: (): i32 {
 pool: [2]Task
 state: [1]IntrusiveCursor
 s: [*]Task = span(&pool)
 q: [*]IntrusiveCursor = span(&state)
 intrusive_init(q, u32(1))
 a: Result[u32, CollectionError] = slist_push_back(q, s, u32(0))
 b: Result[u32, CollectionError] = slist_push_back(q, s, u32(1))
` + corruption + "\nslist_validate(q, s)\n0\n}\n"
		_, abnormal := buildAndRun(t, "corruptlist", src)
		if !abnormal {
			t.Fatal("corrupt links must trap during bounded validation")
		}
	}
}
