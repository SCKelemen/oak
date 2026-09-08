package compiler

import (
	"fmt"
	"os"
	"strings"
	"testing"
)

func TestE2EStdlibDequeTrace(t *testing.T) {
	for _, capacity := range []int{0, 1, 3, 8} {
		t.Run(fmt.Sprint(capacity), func(t *testing.T) {
			var src strings.Builder
			src.WriteString(collectionTestPrelude)
			fmt.Fprintf(&src, "main: (): i32 {\ndata: [%d]u32\nstate: [1]DequeCursor\nq: [*]DequeCursor = span(&state)\n", capacity)
			var model []uint32
			seed := uint32(551)
			for step := 0; step < 100; step++ {
				seed = seed*1664525 + 1013904223
				op := int(seed>>27) % 7
				if step < capacity+2 {
					op = step % 2 // Fill each end and exercise rejection before the trace.
				}
				index := int(seed>>8) % (capacity + 2)
				value := uint32(step + 1)
				errCode, want := 0, uint32(0)
				src.WriteString("true ? {\ns: [*]u32 = span(&data)\nold_head: u32 = q[0].head\nold_count: u32 = q[0].count\n")
				fmt.Fprintf(&src, "snapshot: [%d]u32\ni: u32 = 0\nwhile i < u32(%d) { snapshot[i] = s[i]\ni = i + u32(1) }\n", capacity, capacity)
				switch op {
				case 0, 1:
					end := "back"
					if op == 1 {
						end = "front"
					}
					fmt.Fprintf(&src, "r: Result[u32, CollectionError] = deque_push_%s(q, s, u32(%d))\n", end, value)
					if len(model) == capacity {
						errCode = 1
					} else {
						if op == 0 {
							model = append(model, value)
						} else {
							model = append([]uint32{value}, model...)
						}
						want = uint32(len(model))
					}
				case 2, 3:
					end := "back"
					if op == 3 {
						end = "front"
					}
					fmt.Fprintf(&src, "r: Result[u32, CollectionError] = deque_pop_%s(q, s)\n", end)
					if len(model) == 0 {
						errCode = 2
					} else if op == 2 {
						want = model[len(model)-1]
						model = model[:len(model)-1]
					} else {
						want = model[0]
						model = model[1:]
					}
				case 4, 5:
					fmt.Fprintf(&src, "r: Result[u32, CollectionError] = deque_set(q, s, u32(%d), u32(%d))\n", index, value)
					if index >= len(model) {
						errCode = 3
					} else {
						want = model[index]
						model[index] = value
					}
				case 6:
					fmt.Fprintf(&src, "deque_clear(q, u32(%d))\n", capacity)
					model = nil
				}
				if op != 6 {
					fmt.Fprintf(&src, "assert(result_code(r) == u32(%d))\n", errCode)
					if errCode == 0 {
						fmt.Fprintf(&src, "assert(result_value(r) == u32(%d))\n", want)
					} else {
						src.WriteString("assert(q[0].head == old_head && q[0].count == old_count)\n")
					}
				}
				if errCode != 0 || op == 2 || op == 3 || op == 6 {
					for i := 0; i < capacity; i++ {
						fmt.Fprintf(&src, "assert(s[%d] == snapshot[%d])\n", i, i)
					}
				}
				fmt.Fprintf(&src, "}\nassert(q[0].count == u32(%d))\ntrue ? {\nv: []u32 = view(&data)\n", len(model))
				if len(model) == 0 {
					src.WriteString("assert(result_code(deque_front(q, v)) == u32(2))\nassert(result_code(deque_back(q, v)) == u32(2))\n")
				} else {
					fmt.Fprintf(&src, "assert(result_value(deque_front(q, v)) == u32(%d))\nassert(result_value(deque_back(q, v)) == u32(%d))\n", model[0], model[len(model)-1])
				}
				for i, v := range model {
					fmt.Fprintf(&src, "assert(result_value(deque_get(q, v, u32(%d))) == u32(%d))\n", i, v)
				}
				fmt.Fprintf(&src, "assert(result_code(deque_get(q, v, u32(%d))) == u32(3))\nassert(result_code(deque_get(q, v, u32(4294967295))) == u32(3))\n}\n", len(model))
			}
			src.WriteString("42\n}\n")
			code, abnormal := buildAndRun(t, "dequetrace", src.String())
			if abnormal || code != 42 {
				t.Fatalf("exit=(%d,%v)", code, abnormal)
			}
		})
	}
}

const idPoolTestPrelude = `
import(std)
id_code: (result: Result[u32, IdPoolError]): u32 = result ?
 | .Ok(value) => u32(0)
 | .Err(reason) => reason ?
   | .StorageTooSmall => u32(1)
   | .Full => u32(2)
   | .OutOfBounds => u32(3)
   | .AlreadyAllocated => u32(4)
   | .NotAllocated => u32(5)
id_value: (result: Result[u32, IdPoolError]): u32 = result ?
 | .Ok(value) => value
 | .Err(reason) => u32(4294967295)
id_present: (result: Result[Bool, IdPoolError]): Bool = result ?
 | .Ok(value) => value
 | .Err(reason) => false
`

func TestE2EStdlibIdPoolTrace(t *testing.T) {
	for _, limit := range []int{0, 1, 7, 8, 9, 17} {
		t.Run(fmt.Sprint(limit), func(t *testing.T) {
			var src strings.Builder
			src.WriteString(idPoolTestPrelude)
			capacity := (limit+7)/8 + 1
			fmt.Fprintf(&src, "main: (): i32 {\ndata: [%d]u8\ntrue ? { s: [*]u8 = span(&data)\nbytes_fill(s, u8(165))\nassert(id_code(id_pool_clear(s, u32(%d))) == u32(0))\n}\n", capacity, limit)
			model := make([]bool, limit)
			seed := uint32(933)
			for step := 0; step < 100; step++ {
				seed = seed*1664525 + 1013904223
				op := int(seed>>28) % 5
				if step < limit+2 {
					op = 0
				}
				id := int(seed>>8) % (limit + 2)
				errCode, want := 0, id
				src.WriteString("true ? {\ns: [*]u8 = span(&data)\n")
				switch op {
				case 0, 1:
					fmt.Fprintf(&src, "r: Result[u32, IdPoolError] = id_pool_allocate(s, u32(%d))\n", limit)
					want = -1
					for i, allocated := range model {
						if !allocated {
							want = i
							model[i] = true
							break
						}
					}
					if want == -1 {
						errCode = 2
					}
				case 2:
					fmt.Fprintf(&src, "r: Result[u32, IdPoolError] = id_pool_reserve(s, u32(%d), u32(%d))\n", limit, id)
					if id >= limit {
						errCode = 3
					} else if model[id] {
						errCode = 4
					} else {
						model[id] = true
					}
				case 3:
					fmt.Fprintf(&src, "r: Result[u32, IdPoolError] = id_pool_release(s, u32(%d), u32(%d))\n", limit, id)
					if id >= limit {
						errCode = 3
					} else if !model[id] {
						errCode = 5
					} else {
						model[id] = false
					}
				case 4:
					fmt.Fprintf(&src, "r: Result[u32, IdPoolError] = id_pool_clear(s, u32(%d))\n", limit)
					want = limit
					clear(model)
				}
				fmt.Fprintf(&src, "assert(id_code(r) == u32(%d))\n", errCode)
				if errCode == 0 {
					fmt.Fprintf(&src, "assert(id_value(r) == u32(%d))\n", want)
				}
				// Independent byte oracle includes unused tail bits and spare bytes.
				for b := 0; b < capacity; b++ {
					wantByte := byte(165)
					for bit := 0; bit < 8 && b*8+bit < limit; bit++ {
						wantByte &^= 1 << bit
						if model[b*8+bit] {
							wantByte |= 1 << bit
						}
					}
					fmt.Fprintf(&src, "assert(s[%d] == u8(%d))\n", b, wantByte)
				}
				src.WriteString("}\ntrue ? {\nv: []u8 = view(&data)\n")
				for i, allocated := range model {
					fmt.Fprintf(&src, "assert(id_present(id_pool_contains(v, u32(%d), u32(%d))) == %t)\n", limit, i, allocated)
				}
				src.WriteString("}\n")
			}
			src.WriteString("42\n}\n")
			code, abnormal := buildAndRun(t, "idpooltrace", src.String())
			if abnormal || code != 42 {
				t.Fatalf("exit=(%d,%v)", code, abnormal)
			}
		})
	}
}

func TestE2EStdlibIdPoolBounds(t *testing.T) {
	src := idPoolTestPrelude + `
main: (): i32 {
 data: [1]u8
 true ? {
  s: [*]u8 = span(&data)
  s[0] = u8(165)
  assert(id_code(id_pool_allocate(s, u32(9))) == u32(1))
  assert(id_code(id_pool_clear(s, u32(4294967295))) == u32(1))
  assert(id_code(id_pool_reserve(s, u32(9), u32(0))) == u32(1))
  assert(id_code(id_pool_release(s, u32(9), u32(0))) == u32(1))
  assert(id_code(id_pool_reserve(s, u32(8), u32(4294967295))) == u32(3))
  assert(id_code(id_pool_release(s, u32(8), u32(8))) == u32(3))
  assert(s[0] == u8(165))
  assert(id_value(id_pool_clear(s, u32(8))) == u32(8))
  assert(id_value(id_pool_reserve(s, u32(8), u32(0))) == u32(0))
  assert(id_code(id_pool_reserve(s, u32(8), u32(0))) == u32(4))
  assert(id_value(id_pool_release(s, u32(8), u32(0))) == u32(0))
  assert(id_code(id_pool_release(s, u32(8), u32(0))) == u32(5))
  assert(s[0] == u8(0))
 }
 true ? {
  v: []u8 = view(&data)
  short: Bool = id_pool_contains(v, u32(9), u32(0)) ? | .Ok(x) => false | .Err(e) => e ? | .StorageTooSmall => true | _ => false
  outside: Bool = id_pool_contains(v, u32(8), u32(8)) ? | .Ok(x) => false | .Err(e) => e ? | .OutOfBounds => true | _ => false
  assert(short && outside)
 }
 42
}
`
	code, abnormal := buildAndRun(t, "idpoolbounds", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EStdlibDequeGuards(t *testing.T) {
	for _, body := range []string{
		"q[0].head = u32(2)\ndeque_check(q, u32(2))",
		"q[0].count = u32(3)\ndeque_check(q, u32(2))",
		"q[0].head = u32(1)\ndeque_check(q, u32(0))",
		"deque_offset(u32(0), u32(0), u32(0))",
	} {
		src := "import(std)\nmain: (): i32 {\nstate: [1]DequeCursor\nq: [*]DequeCursor = span(&state)\n" + body + "\n0\n}"
		_, abnormal := buildAndRun(t, "dequeguard", src)
		if !abnormal {
			t.Fatal("invalid deque state must trap")
		}
	}
}

func TestE2EStdlibSerenityExample(t *testing.T) {
	source, err := os.ReadFile("../examples/stdlib_deque_ids.oak")
	if err != nil {
		t.Fatal(err)
	}
	output, err := New().WithSource("dequeids.oak", string(source)).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "OAK_UNSUPPORTED"} {
		if strings.Contains(output, forbidden) {
			t.Fatalf("unexpected %s in emitted C", forbidden)
		}
	}
	code, abnormal := buildAndRun(t, "dequeids", string(source))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
