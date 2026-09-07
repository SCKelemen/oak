package compiler

import (
 "fmt"
 "strings"
 "testing"
)

func TestE2EStdlibValues(t *testing.T) {
 src := `
import(std)
main: (): i32 {
 a: Option[i32] = .Some(19)
 b: Option[u8] = .None
 assert(option_or[i32](a, 0) == 19)
 assert(option_or[u8](b, u8(7)) == u8(7))
 good: Result[u8, Overflow] = u8_checked_u32(u32(255))
 bad: Result[u8, Overflow] = u8_checked_u32(u32(256))
 x: i32 = good ? | .Ok(v) => i32(v) | .Err(e) => 0
 y: i32 = bad ? | .Ok(v) => 0 | .Err(e) => 1
 assert(x == 255 && y == 1)
 42
}
`
 code, abnormal := buildAndRun(t,"stdvalues",src)
 if abnormal || code!=42 { t.Fatalf("exit=(%d,%v)",code,abnormal) }
}

func TestE2EStdlibRing(t *testing.T) {
 // Independent cursors and capacities; storage and state are borrowed, not
 // copied into a function. Full insertion must not change either.
 src := `
import(std)
main: (): i32 {
 a: [3]u8
 b: [1]u32
 ca: [1]RingCursor
 cb: [1]RingCursor
 sa: [*]u8 = span(&a)
 sb: [*]u32 = span(&b)
 qa: [*]RingCursor = span(&ca)
 qb: [*]RingCursor = span(&cb)
 empty: Option[u8] = ring_pop[u8](qa, sa)
 assert(option_or[u8](empty, u8(99)) == u8(99))
 first: RingPush = ring_push[u8](qa, sa, u8(10))
 second: RingPush = ring_push[u8](qa, sa, u8(20))
 third: RingPush = ring_push[u8](qa, sa, u8(30))
 wide: RingPush = ring_push[u32](qb, sb, u32(123456))
 full: RingPush = ring_push[u8](qa, sa, u8(90))
 status: i32 = full ? | .Inserted => 0 | .Full => 1
 assert(status == 1 && qa[0].head == u32(0) && qa[0].count == u32(3))
 assert(sa[0] == u8(10) && sa[1] == u8(20) && sa[2] == u8(30))
 assert(option_or[u8](ring_pop[u8](qa, sa), u8(0)) == u8(10))
 wrapped: RingPush = ring_push[u8](qa, sa, u8(40))
 assert(option_or[u8](ring_pop[u8](qa, sa), u8(0)) == u8(20))
 assert(option_or[u8](ring_pop[u8](qa, sa), u8(0)) == u8(30))
 assert(option_or[u8](ring_pop[u8](qa, sa), u8(0)) == u8(40))
 assert(qa[0].count == u32(0))
 assert(option_or[u32](ring_pop[u32](qb, sb), u32(0)) == u32(123456))
 again: RingPush = ring_push[u32](qb, sb, u32(77))
 assert(option_or[u32](ring_pop[u32](qb, sb), u32(0)) == u32(77))
 42
}
`
 output,err:=New().WithSource("ring.oak",src).EmitC().Get()
 if err!=nil { t.Fatal(err) }
 for _, forbidden:=range []string{"malloc(","calloc(","realloc(","OAK_UNSUPPORTED"} {
  if strings.Contains(output,forbidden) { t.Fatalf("unexpected %s in generated C",forbidden) }
 }
 code,abnormal:=buildAndRun(t,"stdring",src)
 if abnormal || code!=42 { t.Fatalf("exit=(%d,%v)",code,abnormal) }
}

func TestE2EStdlibBytes(t *testing.T) {
 src:=`
import(std)
main: (): i32 {
 input: [3]u8
 output: [3]u8
 tiny: [1]u8
 v: []u8 = view(&input)
 d: [*]u8 = span(&output)
 small: [*]u8 = span(&tiny)
 small[0] = u8(77)
 d[0] = u8(9)
 copied: Result[u32, CopyError] = bytes_copy_into(d, v)
 count: u32 = copied ? | .Ok(n) => n | .Err(e) => u32(99)
 assert(count == u32(3) && d[0] == u8(0) && d[2] == u8(0))
 failed: Result[u32, CopyError] = bytes_copy_into(small, v)
 rejected: Bool = failed ? | .Ok(n) => false | .Err(e) => true
 assert(rejected && small[0] == u8(77))
 assert(bytes_equal(v, v))
 assert(option_or[u32](bytes_find(v, u8(0)), u32(99)) == u32(0))
 assert(option_or[u32](bytes_find(v, u8(1)), u32(99)) == u32(99))
 42
}
`
 code,abnormal:=buildAndRun(t,"stdbytes",src)
 if abnormal || code!=42 { t.Fatalf("exit=(%d,%v)",code,abnormal) }
}

func TestStdlibImportsFailClosed(t *testing.T) {
 for _,src:=range []string{
  "import(missing)\nmain: (): i32 = 0",
  "import(std) as other\nmain: (): i32 = 0",
  "import(std)\nOption[T]: type = Some: T | None\nmain: (): i32 = 0",
 } {
  if _,err:=New().WithSource("bad.oak",src).EmitC().Get();err==nil { t.Fatalf("accepted %s",src) }
 }
 if _,err:=New().WithSource("twice.oak","import(std)\nimport(std)\nmain: (): i32 = 0").EmitC().Get();err!=nil { t.Fatal(err) }
}

func TestE2EExplicitGenericFunctions(t *testing.T) {
 src:=`
identity[T]: (arg: T): T = arg
forward[T]: (arg: T): T = identity[T](arg)
main: (): i32 {
 assert(forward[u8](u8(7)) == u8(7))
 assert(identity[i32](42) == 42)
 42
}
`
 code,abnormal:=buildAndRun(t,"genericfn",src)
 if abnormal || code!=42 { t.Fatalf("exit=(%d,%v)",code,abnormal) }
}

func TestExplicitGenericsRejectUnsupportedAndUnsoundCalls(t *testing.T) {
 for i,src:=range []string{
  "identity[T]: (x: T): T = x\nmain: (): i32 = identity[u8](i32(7))",
  "identity[T]: (x: T): T = x\nmain: (): i32 = identity(7)",
  "identity[T]: (x: T): T = x\nmain: (): i32 = identity[Missing](7)",
  "identity[T]: (T: T): T = T\nmain: (): i32 = identity[i32](7)",
  "identity[T]: (x: T): T = x\nmain: (): i32 = identity[u8,i32](7)",
  "identity[T]: (x: T): T = x\noak_spec_8_identity_3_i32: (): i32 = 0\nmain: (): i32 = identity[i32](7)",
  "bad[T]: (x: T): T = true\nmain: (): i32 = bad[i32](7)",
 } {
  t.Run(fmt.Sprint(i),func(t *testing.T) { if _,err:=New().WithSource("bad.oak",src).EmitC().Get();err==nil { t.Fatal("accepted unsupported or unsound specialization") } })
 }
}
