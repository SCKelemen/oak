package compiler

import "testing"

// Generic ADT monomorphization (docs/spec/30-adts): each concrete
// instantiation gets its own specialized tagged union, and variant
// construction/matching is resolved type-directed by the checker's records
// — never by name guessing. Two instantiations of the same generic in one
// program is the case that guessing cannot survive.
func TestE2EGenericADTMonomorphization(t *testing.T) {
	code, abnormal := buildAndRun(t, "generics", `
Option[T]: type = Some: T | None

pick: (n: i32): Option[i32] = n < 0 ? { .None } | { .Some(n) }

tag: (n: u32): Option[u8] = n == u32(0) ? { .None } | { .Some(u8_saturating_u32(n)) }

unwrap_or: (v: Option[i32], fallback: i32): i32 = v ?
  | .Some(x) => x
  | .None => fallback

main: (): i32 {
  a: Option[i32] = pick(7)
  b: Option[i32] = pick(0 - 3)
  c: Option[u8] = tag(u32(9))
  small: i32 = c ?
    | .Some(byteVal) => i32(byteVal)
    | .None => 0
  unwrap_or(a, 0) + unwrap_or(b, 20) + small + 6
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42 (7 + 20 + 9 + 6)", code, abnormal)
	}
}

// Result[T, E]: the two-parameter shape the kernel error idiom needs.
func TestE2EGenericResultRoundTrip(t *testing.T) {
	code, abnormal := buildAndRun(t, "resultadt", `
ParseError: type = Empty | TooLong

Result[T, E]: type = Ok: T | Err: E

parse_len: (n: u32): Result[u32, ParseError] {
  n == u32(0) ? {
    .Err(.Empty)
  } | {
    n > u32(16) ? { .Err(.TooLong) } | { .Ok(n) }
  }
}

score: (r: Result[u32, ParseError]): i32 = r ?
  | .Ok(n) => i32_bits_u32(n)
  | .Err(e) => e ?
    | .Empty => 0 - 1
    | .TooLong => 0 - 2

main: (): i32 {
  a: Result[u32, ParseError] = parse_len(u32(40))
  b: Result[u32, ParseError] = parse_len(u32(0))
  c: Result[u32, ParseError] = parse_len(u32(9))
  score(a) + score(b) + score(c) + 36
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42 (-2 + -1 + 9 + 36)", code, abnormal)
	}
}

// checked_* conversions produce Result[T, Overflow] once the program
// declares Result and Overflow (docs/spec/20-types.md §11.1) — the checked
// row of the conversion family, previously fail-closed, now monomorphized
// like any other instantiation.
func TestE2ECheckedConversion(t *testing.T) {
	code, abnormal := buildAndRun(t, "checkedconv", `
Overflow: type = | Overflow

Result[T, E]: type = Ok: T | Err: E

clamp_report: (n: u32): i32 = u8_checked_u32(n) ?
  | .Ok(b) => i32(b)
  | .Err(e) => 0 - 1

main: (): i32 {
  fits: i32 = clamp_report(u32(200))
  overflows: i32 = clamp_report(u32(300))
  fits + overflows + 43
}
`)
	if abnormal || code != 242 {
		t.Fatalf("exit = (%d, abnormal=%v), want 242 (200 - 1 + 43)", code, abnormal)
	}
}
