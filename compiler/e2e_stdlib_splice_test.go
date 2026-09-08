package compiler

import (
	"fmt"
	"strings"
	"testing"
)

const transferTestPrelude = collectionTestPrelude + `
transfer_error_code: (reason: ListTransferError): u32 = reason ?
 | .SameList => u32(1)
 | .OutOfBounds => u32(2)
 | .NotMember => u32(3)
transfer_code: (result: Result[u32, ListTransferError]): u32 = result ?
 | .Ok(value) => u32(0)
 | .Err(reason) => transfer_error_code(reason)
transfer_value: (result: Result[u32, ListTransferError]): u32 = result ?
 | .Ok(value) => value
 | .Err(reason) => u32(4294967295)
`

func TestE2EStdlibIntrusiveTransferTrace(t *testing.T) {
	for _, family := range []string{"slist", "dlist"} {
		t.Run(family, func(t *testing.T) {
			other := "dlist"
			if family == "dlist" {
				other = "slist"
			}
			var src strings.Builder
			src.WriteString(transferTestPrelude)
			src.WriteString("Task: type = struct { value: u32, slist: SListHook, dlist: DListHook }\nmain: (): i32 {\npool: [8]Task\ns: [*]Task = span(&pool)\n")
			for q := 0; q < 4; q++ {
				fmt.Fprintf(&src, "state%d: [1]IntrusiveCursor\nq%d: [*]IntrusiveCursor = span(&state%d)\nintrusive_init(q%d, u32(%d))\n", q, q, q, q, q+1)
			}
			lists := [3][]int{}
			for i := 0; i < 8; i++ {
				q := i % 3
				lists[q] = append(lists[q], i)
				fmt.Fprintf(&src, "s[%d].value = u32(%d)\nassert(result_code(%s_push_back(q%d, s, u32(%d))) == u32(0))\nassert(result_code(%s_push_back(q3, s, u32(%d))) == u32(0))\n", i, i+100, family, q, i, other, i)
			}
			seed := uint32(883)
			for step := 0; step < 120; step++ {
				seed = seed*1664525 + 1013904223
				from, to := int(seed>>8)%3, int(seed>>16)%3
				index := uint32(seed % 10)
				if step%13 == 0 {
					index = ^uint32(0)
				}
				op := int(seed>>28) % 4
				name := []string{"transfer_front", "transfer_back", "splice_front", "splice_back"}[op]
				code, value := 0, uint32(0)
				if from == to {
					code = 1
				} else if op < 2 {
					if index >= 8 {
						code = 2
					} else {
						at := -1
						for i, node := range lists[from] {
							if node == int(index) {
								at = i
							}
						}
						if at < 0 {
							code = 3
						} else {
							lists[from] = append(lists[from][:at], lists[from][at+1:]...)
							if op == 0 {
								lists[to] = append([]int{int(index)}, lists[to]...)
							} else {
								lists[to] = append(lists[to], int(index))
							}
							value = index
						}
					}
				} else {
					value = uint32(len(lists[from]))
					moved := append([]int(nil), lists[from]...)
					if op == 2 {
						lists[to] = append(moved, lists[to]...)
					} else {
						lists[to] = append(lists[to], moved...)
					}
					lists[from] = nil
				}
				fmt.Fprintf(&src, "true ? {\nr: Result[u32, ListTransferError] = %s_%s(q%d, q%d, s", family, name, to, from)
				if op < 2 {
					fmt.Fprintf(&src, ", u32(%d)", index)
				}
				fmt.Fprintf(&src, ")\nassert(transfer_code(r) == u32(%d))\n", code)
				if code == 0 {
					fmt.Fprintf(&src, "assert(transfer_value(r) == u32(%d))\n", value)
				}
				src.WriteString("}\n")
				next, prev, owner := [8]int{}, [8]int{}, [8]int{}
				for q, list := range lists {
					head, tail := 0, 0
					if len(list) != 0 {
						head, tail = list[0]+1, list[len(list)-1]+1
					}
					fmt.Fprintf(&src, "%s_validate(q%d, s)\nassert(q%d[0].count == u32(%d) && q%d[0].head == u32(%d) && q%d[0].tail == u32(%d) && q%d[0].id == u32(%d))\n", family, q, q, len(list), q, head, q, tail, q, q+1)
					for at, node := range list {
						owner[node] = q + 1
						if at > 0 {
							prev[node] = list[at-1] + 1
						}
						if at+1 < len(list) {
							next[node] = list[at+1] + 1
						}
					}
				}
				fmt.Fprintf(&src, "%s_validate(q3, s)\nassert(q3[0].count == u32(8) && q3[0].head == u32(1) && q3[0].tail == u32(8))\n", other)
				for i := 0; i < 8; i++ {
					fmt.Fprintf(&src, "assert(s[%d].%s.owner == u32(%d) && s[%d].%s.next == u32(%d) && s[%d].value == u32(%d))\n", i, family, owner[i], i, family, next[i], i, i+100)
					if family == "dlist" {
						fmt.Fprintf(&src, "assert(s[%d].dlist.prev == u32(%d))\n", i, prev[i])
					} else {
						fmt.Fprintf(&src, "assert(s[%d].dlist.prev == u32(%d))\n", i, i)
					}
					otherNext := i + 2
					if i == 7 {
						otherNext = 0
					}
					fmt.Fprintf(&src, "assert(s[%d].%s.owner == u32(4) && s[%d].%s.next == u32(%d))\n", i, other, i, other, otherNext)
				}
			}
			src.WriteString("42\n}\n")
			code, abnormal := buildAndRun(t, "transfertrace", src.String())
			if abnormal || code != 42 {
				t.Fatalf("exit=(%d,%v)", code, abnormal)
			}
		})
	}
}

func TestE2EStdlibQueueAppendMembership(t *testing.T) {
	src := transferTestPrelude + `
Task: type = struct { value: u32, slist: SListHook }
main: (): i32 {
 pool: [3]Task
 ready: [1]IntrusiveCursor
 pending: [1]IntrusiveCursor
 s: [*]Task = span(&pool)
 q: [*]IntrusiveCursor = span(&ready)
 p: [*]IntrusiveCursor = span(&pending)
 intrusive_init(q, u32(1))
 intrusive_init(p, u32(2))
 assert(result_code(intrusive_queue_push(q, s, u32(0))) == u32(0))
 assert(result_code(intrusive_queue_push(p, s, u32(1))) == u32(0))
 assert(result_code(intrusive_queue_push(p, s, u32(2))) == u32(0))
 assert(transfer_value(intrusive_queue_append(q, p, s)) == u32(2))
 assert(transfer_value(intrusive_queue_append(q, p, s)) == u32(0))
 assert(result_code(slist_remove(p, s, u32(1))) == u32(5))
 assert(result_code(intrusive_queue_push(p, s, u32(1))) == u32(4))
 assert(result_value(intrusive_queue_pop(q, s)) == u32(0))
 assert(result_value(intrusive_queue_pop(q, s)) == u32(1))
 assert(result_value(intrusive_queue_pop(q, s)) == u32(2))
 assert(result_code(intrusive_queue_push(p, s, u32(1))) == u32(0))
 assert(result_value(intrusive_queue_pop(p, s)) == u32(1))
 slist_validate(q, s)
 slist_validate(p, s)
 42
}
`
	output, err := New().WithSource("queueappend.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "OAK_UNSUPPORTED"} {
		if strings.Contains(output, forbidden) {
			t.Fatalf("unexpected %s in emitted C", forbidden)
		}
	}
	code, abnormal := buildAndRun(t, "queueappend", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EStdlibSpliceRejectsCorruptSource(t *testing.T) {
	for _, family := range []string{"slist", "dlist"} {
		for _, next := range []uint32{1, 99} {
			src := transferTestPrelude + fmt.Sprintf(`
Task: type = struct { slist: SListHook, dlist: DListHook }
main: (): i32 {
 pool: [3]Task
 a: [1]IntrusiveCursor
 b: [1]IntrusiveCursor
 s: [*]Task = span(&pool)
 q: [*]IntrusiveCursor = span(&a)
 p: [*]IntrusiveCursor = span(&b)
 intrusive_init(q, u32(1))
 intrusive_init(p, u32(2))
 first: Result[u32, CollectionError] = %s_push_back(p, s, u32(0))
 second: Result[u32, CollectionError] = %s_push_back(p, s, u32(1))
 s[0].%s.next = u32(%d)
 r: Result[u32, ListTransferError] = %s_splice_back(q, p, s)
 0
}
`, family, family, family, next, family)
			_, abnormal := buildAndRun(t, "corruptsplice", src)
			if !abnormal {
				t.Fatal("corrupt source must trap during bounded validation")
			}
		}
	}
}
