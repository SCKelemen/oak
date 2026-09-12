package compiler

import (
	"regexp"
	"strings"
	"testing"
)

// The propagation form (docs/spec/10-syntax.md section 2d): `x: T = try e`
// in a block whose value is the function's Result or Option binds the
// payload and re-raises the error. It lowers to the match the library
// writes by hand, so a function written each way computes the same value
// in both realizations.
const tryProgram = `
import(std)
Fault: type = | Small | Odd
half_checked: (n: u32): Result[u32, Fault] = n % u32(2) == u32(0) ? .Ok(n / u32(2)) | .Err(.Odd)
above: (n: u32): Result[u32, Fault] = n > u32(4) ? .Ok(n) | .Err(.Small)

// Two propagations in one body, then the result.
quarter_try: (n: u32): Result[u32, Fault] {
  big: u32 = try above(n)
  h: u32 = try half_checked(big)
  q: u32 = try half_checked(h)
  .Ok(q + u32(1))
}
quarter_hand: (n: u32): Result[u32, Fault] {
  above(n) ?
   | .Err(e) => .Err(e)
   | .Ok(big) => half_checked(big) ?
     | .Err(e) => .Err(e)
     | .Ok(h) => half_checked(h) ?
       | .Err(e) => .Err(e)
       | .Ok(q) => .Ok(q + u32(1))
}

// A try inside a tail arm's block, a discarded try, and try as the value.
tail_try: (n: u32, flag: Bool): Result[u32, Fault] {
  flag ? {
    _ = try above(n)
    h: u32 = try half_checked(n)
    .Ok(h)
  } | {
    try above(n)
  }
}

// Option propagates the same way with None.
first_even: (a: u32, b: u32): Option[u32] = a % u32(2) == u32(0) ? .Some(a) | (b % u32(2) == u32(0) ? .Some(b) | .None)
sum_evens: (a: u32, b: u32, c: u32): Option[u32] {
  x: u32 = try first_even(a, b)
  y: u32 = try first_even(b, c)
  .Some(x + y)
}

fault_code: (e: Fault): u32 = e ? | .Small => u32(100) | .Odd => u32(200)
code_of: (r: Result[u32, Fault]): u32 = r ? | .Ok(v) => v | .Err(e) => fault_code(e)
opt_of: (o: Option[u32]): u32 = o ? | .Some(v) => v | .None => u32(300)

main: (): i32 {
  ok: Bool = true
  n: u32 = u32(0)
  while n < u32(40) {
    ok = ok && code_of(quarter_try(n)) == code_of(quarter_hand(n))
    n = n + u32(1)
  }
  // 6 -> 3 -> Odd; 12 -> 6 -> 3 -> 4; 16 -> 8 -> 4 -> 5; 3 -> Small
  ok = ok && code_of(quarter_try(u32(6))) == u32(200)
  ok = ok && code_of(quarter_try(u32(12))) == u32(4)
  ok = ok && code_of(quarter_try(u32(16))) == u32(5)
  ok = ok && code_of(quarter_try(u32(3))) == u32(100)
  ok = ok && code_of(tail_try(u32(8), true)) == u32(4)
  ok = ok && code_of(tail_try(u32(2), true)) == u32(100)
  ok = ok && code_of(tail_try(u32(7), true)) == u32(200)
  ok = ok && code_of(tail_try(u32(9), false)) == u32(9)
  ok = ok && code_of(tail_try(u32(1), false)) == u32(100)
  ok = ok && opt_of(sum_evens(u32(2), u32(3), u32(4))) == u32(6)
  ok = ok && opt_of(sum_evens(u32(1), u32(3), u32(4))) == u32(300)
  ok = ok && opt_of(sum_evens(u32(2), u32(3), u32(5))) == u32(300)
  ok ? 42 | 1
}
`

func TestE2ETryCompiled(t *testing.T) {
	output, err := New().WithSource("try.oak", tryProgram).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if strings.Contains(output, "try") && strings.Contains(output, "OAK_UNSUPPORTED") {
		t.Fatalf("the try form reached the backend:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "try", tryProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ETryInterpreted(t *testing.T) {
	if got := interpretChecked(t, tryProgram); got != 42 {
		t.Fatalf("interpreter: got %d, want 42", got)
	}
}

// The lowering is the hand-written match: the emitted C of a try body
// names no try and dispatches on the same variants.
func TestTryLowersToTheMatch(t *testing.T) {
	src := `
import(std)
Fault: type = | Bad
step: (n: u32): Result[u32, Fault] = n > u32(0) ? .Ok(n - u32(1)) | .Err(.Bad)
twice: (n: u32): Result[u32, Fault] {
  a: u32 = try step(n)
  b: u32 = try step(a)
  .Ok(b)
}
main: (): i32 = twice(u32(5)) ? | .Ok(v) => { v == u32(3) ? 1 | 2 } | .Err(_) => 9
`
	tree, err := New().WithSource("lower.oak", src).Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	text := tree.Tree.Root.String()
	if regexp.MustCompile(`(^|[^A-Za-z0-9_])try[^A-Za-z0-9_]`).MatchString(text) {
		t.Fatalf("a try survived lowering:\n%s", text)
	}
	for _, want := range []string{"_try_err_", ".Err(_try_err_"} {
		if !strings.Contains(text, want) {
			t.Fatalf("lowered program lacks %q:\n%s", want, text)
		}
	}
}

// Where the re-raise could not leave the function, or the value would be
// dropped, the try is a diagnostic at the try.
func TestTryRejections(t *testing.T) {
	prelude := "import(std)\nFault: type = | Bad\nstep: (n: u32): Result[u32, Fault] = n > u32(0) ? .Ok(n - u32(1)) | .Err(.Bad)\n"
	cases := map[string]struct{ src, want string }{
		"in a loop body": {prelude + `
f: (n: u32): Result[u32, Fault] {
  acc: u32 = u32(0)
  i: u32 = u32(0)
  while i < n {
    a: u32 = try step(i)
    acc = acc + a
    i = i + u32(1)
  }
  .Ok(acc)
}
main: (): i32 = 0
`, "try here does not return from the function"},
		"in expression position": {prelude + `
f: (n: u32): Result[u32, Fault] = .Ok(u32(1) + try step(n))
main: (): i32 = 0
`, "try here does not return from the function"},
		"bare statement": {prelude + `
f: (n: u32): Result[u32, Fault] {
  try step(n)
  .Ok(n)
}
main: (): i32 = 0
`, "bind it (`x: T = try e`) or discard it on purpose"},
		"last statement": {prelude + `
f: (n: u32): Result[u32, Fault] {
  a: u32 = try step(n)
}
main: (): i32 = 0
`, "try in the last statement of a block"},
		"function returns a scalar": {prelude + `
f: (n: u32): u32 {
  a: u32 = try step(n)
  a
}
main: (): i32 = 0
`, "try here does not return from the function"},
		"error types differ": {prelude + `
Other: type = | Worse
f: (n: u32): Result[u32, Other] {
  a: u32 = try step(n)
  .Ok(a)
}
main: (): i32 = 0
`, "Fault"},
		"option in a result function": {prelude + `
maybe: (n: u32): Option[u32] = n > u32(0) ? .Some(n) | .None
f: (n: u32): Result[u32, Fault] {
  a: u32 = try maybe(n)
  .Ok(a)
}
main: (): i32 = 0
`, "Err"},
	}
	for name, c := range cases {
		_, err := New().WithSource("bad.oak", c.src).EmitC().Get()
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: want %q, got %v", name, c.want, err)
		}
	}
}
