package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// interpretChecked evaluates the TYPE-CHECKED program tree — the same tree
// codegen consumes, after generic specialization and builtin rewrites —
// in the interpreter, then calls main().
func interpretChecked(t *testing.T, src string) int64 {
	t.Helper()
	model, err := New().WithSource("sweep.oak", src).Check().Get()
	if err != nil {
		t.Fatalf("check failed: %v", err)
	}
	env := object.NewEnvironment()
	env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
	result := evaluator.Eval(model.Tree.Root, env)
	if e, isErr := result.(*object.Error); isErr {
		t.Fatalf("interpreter error evaluating program: %s", e.Message)
	}
	p := parser.New(layout.New(scanner.New("main()")))
	call := p.ParseProgram()
	result = evaluator.Eval(call, env)
	if e, isErr := result.(*object.Error); isErr {
		t.Fatalf("interpreter error in main(): %s", e.Message)
	}
	integer, ok := result.(*object.Integer)
	if !ok {
		t.Fatalf("main() returned %s", result.Inspect())
	}
	return integer.Value
}

// The differential sweep: representative executed programs from across the
// corpus, run through the compiled C and the interpreter, must agree.
// Compile-time-only builtins (size_of, static_assert, address_of) are out
// of scope by design. Every divergence found here is a bug in one
// realization.
func TestDifferentialSweep(t *testing.T) {
	programs := map[string]string{
		"refinement types": `
Slot: type = u16 where value < u16(8)
TABLE: [8]u8 = [8]u8{ 1, 2, 3, 4, 5, 6, 7, 8 }

pick: (i: Slot): u8 = TABLE[i]

main: (): i32 {
  n: u16 = 3
  a: Slot = Slot(n)
  b: Slot = Slot(n + n)
  plain: u16 = a
  i32_bits_u32(u32(pick(a)) + u32(pick(b)) + u32(plain) + u32(pick(Slot(u16(7)))) + u32(20))
}
`,
		"sum-type equality": `
Color: type = Red | Green | Blue
Shape: type = Dot | Box: u8

next: (c: Color): Color = c ? | .Red => .Green | .Green => .Blue | .Blue => .Red

main: (): i32 {
  c: Color = .Red
  same: Bool = next(next(next(c))) == c
  other: Bool = next(c) != c
  boxed: Bool = Shape.Box(u8(3)) == Shape.Box(u8(3))
  unboxed: Bool = Shape.Box(u8(3)) != Shape.Box(u8(4))
  flag: Bool = (u8(1) < u8(2)) == true
  (same && other && boxed && unboxed && flag) ? 42 | 1
}
`,
		"bitfields": `
main: (): i32 {
  hcr: u64 = 0x1 | 0x8 | (u64(1) << 27)
  assert(hcr == 0x8000009)
  cleared: u64 = hcr & ^u64(0x8)
  field: u64 = (hcr >> 3) & 0x3
  assert(cleared == 0x8000001)
  assert(field == u64(1))
  lane: u32 = 0b1010
  assert(lane | 0b0101 == 0xF)
  42
}
`,
		"value conditionals": `
Ordering: type = Less | Equal | Greater

cmp[T]: (a: T, b: T): Ordering {
  a < b ? .Less | (a == b ? .Equal | .Greater)
}

max[T]: (a: T, b: T): T {
  a < b ? b | a
}

main: (): i32 {
  best: u32 = 5
  v: u32 = 9
  cmp(v, best) ?
    | .Greater => { best = v }
    | .Less => { }
    | .Equal => { }
  assert(best == u32(9))
  best = max(best, u32(3))
  wide: u64 = max(u64(40), u64(2))
  assert(wide == u64(40))
  cmp(u64(1), u64(1)) ?
    | .Equal => { 42 }
    | .Less => { 0 }
    | .Greater => { 0 }
}
`,
		"records and tags": `
json: tag = { name: string, omit: Bool }

User: type = struct {
  id(json: "user_id"): u64
  score: u32
  active: Bool
}

bump: (u: User): User = User { id: u.id, score: u.score + u32(1), active: u.active }

main: (): i32 {
  u: User = User { id: u64(7), score: u32(41), active: true }
  w: User = bump(u)
  assert(w.score == u32(42))
  assert(w.id == u64(7))
  w.active ? { 42 } | { 0 }
}
`,
		"spsc ring over atomics": `
buffer: [4]u32
head: Atomic[u32]
tail: Atomic[u32]

push: (v: u32): Bool {
  t: u32 = atomic_load_relaxed(tail)
  h: u32 = atomic_load_acquire(head)
  t - h == u32(4) ? { false } | {
    buffer[t % u32(4)] = v
    atomic_store_release(tail, t + u32(1))
    true
  }
}

pop: (): u32 {
  h: u32 = atomic_load_relaxed(head)
  v: u32 = buffer[h % u32(4)]
  atomic_store_release(head, h + u32(1))
  v
}

main: (): i32 {
  assert(push(u32(40)))
  assert(push(u32(2)))
  total: u32 = pop() + pop()
  assert(total == u32(42))
  42
}
`,
		"phantom links": `
Idx[P]: type = struct { raw: u32 }

Thread: type = struct {
  priority: u8
  next: Idx[Thread]
}

pool: [4]Thread
freeHead: Idx[Thread]

seed: (): () {
  i: u32 = 0
  while i < u32(4) {
    pool[i].next.raw = i
    i = i + u32(1)
  }
  freeHead.raw = u32(4)
}

acquire: (): u32 {
  id: u32 = freeHead.raw - u32(1)
  freeHead = pool[id].next
  id
}

main: (): i32 {
  seed()
  a: u32 = acquire()
  b: u32 = acquire()
  assert(a == u32(3) && b == u32(2))
  pool[b].priority = u8(42)
  i32(pool[u32(2)].priority)
}
`,
		"const-parameter ring": `
Ring[T, N: u32]: type = struct {
  head: u32
  count: u32
  buffer: [N]T
}

events: Ring[u8, 4]

push: (v: u8): () {
  events.buffer[(events.head + events.count) % u32(4)] = v
  events.count = events.count + u32(1)
}

main: (): i32 {
  push(u8(40))
  push(u8(2))
  a: u8 = events.buffer[u32(0)]
  b: u8 = events.buffer[u32(1)]
  assert(events.count == u32(2))
  i32(a) + i32(b)
}
`,
	}
	for name, src := range programs {
		t.Run(name, func(t *testing.T) {
			code, abnormal := buildAndRun(t, "sweep_"+name, src)
			if abnormal || code != 42 {
				t.Fatalf("compiled: exit = (%d, abnormal=%v), want 42", code, abnormal)
			}
			if got := interpretChecked(t, src); got != 42 {
				t.Fatalf("interpreted: %d, want 42", got)
			}
		})
	}
}
