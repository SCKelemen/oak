package compiler

import (
	"fmt"
	"math"
	"math/rand"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// The time package (stdlib/time.oak): instants and durations as checked i64
// nanoseconds, the proleptic Gregorian calendar, RFC 3339 text, and Go's
// duration spelling, all in Oak with no clock. Every expectation here comes
// from Go's time package, so the two implementations are compared rather
// than the Oak one being checked against hand-computed values; the same
// programs run compiled and interpreted and must agree with Go in both.

// timeTestPrelude is shared by the check programs: byte comparison and thin
// adapters that turn each package call into a Bool or an error code the
// generated checks can compare (0 is Ok; the codes follow the TimeError
// variants in declaration order).
const timeTestPrelude = `import(std)
import("time")

same: (a: []u8, b: []u8): Bool {
  len(a) != len(b) ? { false } | {
    i: u32 = 0
    ok: Bool = true
    while i < len(a) && ok {
      ok = a[i] == b[i]
      i = i + u32(1)
    }
    ok
  }
}

err_code: (e: time.TimeError): u32 {
  e ?
    | .Overflowed => u32(1)
    | .InvalidCivil => u32(2)
    | .InvalidFormat => u32(3)
    | .InvalidOffset => u32(4)
    | .InvalidDuration => u32(5)
    | .DestinationTooSmall => u32(6)
    | .Unattested => u32(7)
}

civil: (y: i32, mo: u8, d: u8, h: u8, mi: u8, s: u8, ns: u32): time.Civil {
  time.Civil { year: y, month: mo, day: d, hour: h, minute: mi, second: s, nanos: ns }
}

civil_eq: (a: time.Civil, b: time.Civil): Bool {
  a.year == b.year && a.month == b.month && a.day == b.day && a.hour == b.hour && a.minute == b.minute && a.second == b.second && a.nanos == b.nanos
}

date_is: (days: i64, y: i32, mo: u8, d: u8): Bool {
  c: time.Civil = time.civil_from_days(days)
  c.year == y && c.month == mo && c.day == d
}

to_instant_code: (c: time.Civil, off: i32): u32 {
  r: Result[time.Instant, time.TimeError] = time.civil_to_instant(c, off)
  r ? | .Ok(i) => { u32(0) } | .Err(e) => { err_code(e) }
}

to_instant_is: (c: time.Civil, off: i32, nanos: i64): Bool {
  r: Result[time.Instant, time.TimeError] = time.civil_to_instant(c, off)
  r ? | .Ok(i) => { i.nanos == nanos } | .Err(e) => { false }
}

to_civil_code: (nanos: i64, off: i32): u32 {
  r: Result[time.Civil, time.TimeError] = time.instant_to_civil(time.instant_nanos(nanos), off)
  r ? | .Ok(c) => { u32(0) } | .Err(e) => { err_code(e) }
}

to_civil_is: (nanos: i64, off: i32, expected: time.Civil): Bool {
  r: Result[time.Civil, time.TimeError] = time.instant_to_civil(time.instant_nanos(nanos), off)
  r ? | .Ok(c) => { civil_eq(c, expected) } | .Err(e) => { false }
}

fmt_is: (nanos: i64, off: i32, frac: u32, expected: []u8): Bool {
  buf: [48]u8
  r: Result[u32, time.TimeError] = time.format_rfc3339(span(&buf), time.instant_nanos(nanos), off, frac)
  r ? | .Ok(n) => {
    v: []u8 = view(&buf)
    same(v[0:n], expected)
  } | .Err(e) => { false }
}

fmt_code: (nanos: i64, off: i32, frac: u32): u32 {
  buf: [48]u8
  r: Result[u32, time.TimeError] = time.format_rfc3339(span(&buf), time.instant_nanos(nanos), off, frac)
  r ? | .Ok(n) => { u32(0) } | .Err(e) => { err_code(e) }
}

fmt_small_code: (nanos: i64, off: i32, frac: u32): u32 {
  buf: [10]u8
  r: Result[u32, time.TimeError] = time.format_rfc3339(span(&buf), time.instant_nanos(nanos), off, frac)
  r ? | .Ok(n) => { u32(0) } | .Err(e) => { err_code(e) }
}

parse_code: (text: []u8): u32 {
  r: Result[time.Zoned, time.TimeError] = time.parse_rfc3339(text)
  r ? | .Ok(z) => { u32(0) } | .Err(e) => { err_code(e) }
}

parse_is: (text: []u8, nanos: i64, off: i32): Bool {
  r: Result[time.Zoned, time.TimeError] = time.parse_rfc3339(text)
  r ? | .Ok(z) => { z.instant.nanos == nanos && z.offset_minutes == off } | .Err(e) => { false }
}

dur_fmt_is: (nanos: i64, expected: []u8): Bool {
  buf: [48]u8
  r: Result[u32, time.TimeError] = time.format_duration(span(&buf), time.duration_nanos(nanos))
  r ? | .Ok(n) => {
    v: []u8 = view(&buf)
    same(v[0:n], expected)
  } | .Err(e) => { false }
}

dur_fmt_small_code: (nanos: i64): u32 {
  buf: [10]u8
  r: Result[u32, time.TimeError] = time.format_duration(span(&buf), time.duration_nanos(nanos))
  r ? | .Ok(n) => { u32(0) } | .Err(e) => { err_code(e) }
}

dur_parse_code: (text: []u8): u32 {
  r: Result[time.Duration, time.TimeError] = time.parse_duration(text)
  r ? | .Ok(d) => { u32(0) } | .Err(e) => { err_code(e) }
}

dur_parse_is: (text: []u8, nanos: i64): Bool {
  r: Result[time.Duration, time.TimeError] = time.parse_duration(text)
  r ? | .Ok(d) => { d.nanos == nanos } | .Err(e) => { false }
}

dur_code: (r: Result[time.Duration, time.TimeError]): u32 {
  r ? | .Ok(d) => { u32(0) } | .Err(e) => { err_code(e) }
}

dur_is: (r: Result[time.Duration, time.TimeError], nanos: i64): Bool {
  r ? | .Ok(d) => { d.nanos == nanos } | .Err(e) => { false }
}

inst_code: (r: Result[time.Instant, time.TimeError]): u32 {
  r ? | .Ok(i) => { u32(0) } | .Err(e) => { err_code(e) }
}

inst_is: (r: Result[time.Instant, time.TimeError], nanos: i64): Bool {
  r ? | .Ok(i) => { i.nanos == nanos } | .Err(e) => { false }
}

dur: (nanos: i64): time.Duration = time.duration_nanos(nanos)
inst: (nanos: i64): time.Instant = time.instant_nanos(nanos)
`

// timeChecks accumulates numbered Bool checks; program(chunk) renders a
// slice of at most timeChunk checks into an Oak main that returns 42 when
// every check holds and otherwise the id of the first failure (ids start at
// 100 and stay below 256 so the exit status carries them, and no failure
// can be mistaken for success).
type timeChecks struct {
	entries []timeCheck
	pending strings.Builder
	arrays  int
}

type timeCheck struct {
	decls string
	cond  string
}

const timeChunk = 120

// text declares a local byte array holding s and returns a view of it.
func (b *timeChecks) text(s string) string {
	b.arrays++
	name := fmt.Sprintf("t%d", b.arrays)
	fmt.Fprintf(&b.pending, "  %s: [%d]u8 = %s\n", name, len(s), oakByteArray([]byte(s)))
	return "view(&" + name + ")"
}

func (b *timeChecks) check(cond string) {
	b.entries = append(b.entries, timeCheck{decls: b.pending.String(), cond: cond})
	b.pending.Reset()
}

func (b *timeChecks) chunks() int { return (len(b.entries) + timeChunk - 1) / timeChunk }

func (b *timeChecks) chunk(n int) []timeCheck {
	lo := n * timeChunk
	hi := lo + timeChunk
	if hi > len(b.entries) {
		hi = len(b.entries)
	}
	return b.entries[lo:hi]
}

func (b *timeChecks) program(n int) string {
	var body strings.Builder
	for i, e := range b.chunk(n) {
		body.WriteString(e.decls)
		fmt.Fprintf(&body, "  fail = fail == u32(0) && !(%s) ? { u32(%d) } | { fail }\n", e.cond, 100+i)
	}
	return timeTestPrelude + "\nmain: (): i32 {\n  fail: u32 = 0\n" + body.String() +
		"  fail == u32(0) ? { i32(42) } | { i32_bits_u32(fail) }\n}\n"
}

// describe names the check behind an exit code of chunk n.
func (b *timeChecks) describe(n int, code int) string {
	entries := b.chunk(n)
	index := code - 100
	if index < 0 || index >= len(entries) {
		return fmt.Sprintf("exit code %d (not a check id)", code)
	}
	return fmt.Sprintf("check %d of chunk %d: %s", code, n, entries[index].cond)
}

func oakByteArray(data []byte) string {
	var sb strings.Builder
	fmt.Fprintf(&sb, "[%d]u8{", len(data))
	for i, b := range data {
		if i > 0 {
			sb.WriteString(",")
		}
		fmt.Fprintf(&sb, "%d", b)
	}
	sb.WriteString("}")
	return sb.String()
}

// oakI64 spells an i64 constant; the minimum has no literal of its own.
func oakI64(v int64) string {
	if v == math.MinInt64 {
		return "(i64(-9223372036854775807) - i64(1))"
	}
	return fmt.Sprintf("i64(%d)", v)
}

func oakI32(v int32) string { return fmt.Sprintf("i32(%d)", v) }

// runTimeChecks compiles and runs each chunk of a check program as a module
// root, then interprets the same program; both must return 42.
func runTimeChecks(t *testing.T, name string, b *timeChecks) {
	t.Helper()
	for n := 0; n < b.chunks(); n++ {
		src := b.program(n)
		root := writeModule(t, map[string]string{
			"oak.mod":  "module example.com/" + name + "\noak 0.1.0\n",
			"main.oak": "package main\n" + src,
		})
		code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
		if abnormal || code != 42 {
			t.Fatalf("compiled time program failed: %s (abnormal=%v)", b.describe(n, code), abnormal)
		}
		model, err := New().WithPackageDir(root).Check().Get()
		if err != nil {
			t.Fatalf("check failed: %v", err)
		}
		env := object.NewEnvironment()
		env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
		if result := evaluator.Eval(model.Tree.Root, env); result != nil {
			if e, isErr := result.(*object.Error); isErr {
				t.Fatalf("interpreter error evaluating program: %s", e.Message)
			}
		}
		call := parser.New(layout.New(scanner.New("main()"))).ParseProgram()
		result := evaluator.Eval(call, env)
		if e, isErr := result.(*object.Error); isErr {
			t.Fatalf("interpreter error in main(): %s", e.Message)
		}
		integer, ok := result.(*object.Integer)
		if !ok {
			t.Fatalf("interpreter returned %s", result.Inspect())
		}
		if integer.Value != 42 {
			t.Fatalf("interpreted time program failed: %s", b.describe(n, int(integer.Value)))
		}
	}
}

// goDays is Go's day count since the epoch for a proleptic Gregorian date.
func goDays(y int, m time.Month, d int) int64 {
	seconds := time.Date(y, m, d, 0, 0, 0, 0, time.UTC).Unix()
	days := seconds / 86400
	if seconds%86400 != 0 && seconds < 0 {
		days--
	}
	return days
}

func TestE2EStdlibTimeCalendar(t *testing.T) {
	b := &timeChecks{}
	type date struct {
		y    int
		m    time.Month
		d    int
		leap bool // whether y is a leap year
	}
	dates := []date{
		{1970, time.January, 1, false}, {1970, time.January, 2, false}, {1969, time.December, 31, false},
		{2000, time.February, 29, true}, {2000, time.March, 1, true}, {2000, time.December, 31, true},
		{1900, time.February, 28, false}, {1900, time.March, 1, false}, {1900, time.December, 31, false},
		{2100, time.February, 28, false}, {2100, time.March, 1, false},
		{2024, time.February, 29, true}, {1999, time.December, 31, false}, {2038, time.January, 19, false},
		{1600, time.February, 29, true}, {1, time.January, 1, false}, {0, time.January, 1, true},
		{0, time.February, 29, true}, {-1, time.December, 31, false}, {-400, time.February, 29, true},
		{-4713, time.November, 24, false}, {1677, time.September, 21, false}, {2262, time.April, 11, false},
		{9999, time.December, 31, false}, {32767, time.June, 15, false}, {-32768, time.June, 15, true},
	}
	for _, c := range dates {
		days := goDays(c.y, c.m, c.d)
		t0 := time.Date(c.y, c.m, c.d, 0, 0, 0, 0, time.UTC)
		b.check(fmt.Sprintf("time.days_from_civil(%s, u8(%d), u8(%d)) == %s", oakI32(int32(c.y)), c.m, c.d, oakI64(days)))
		b.check(fmt.Sprintf("date_is(%s, %s, u8(%d), u8(%d))", oakI64(days), oakI32(int32(c.y)), c.m, c.d))
		b.check(fmt.Sprintf("time.weekday(%s) == u8(%d)", oakI64(days), int(t0.Weekday())))
		b.check(fmt.Sprintf("time.day_of_year(civil(%s, u8(%d), u8(%d), u8(0), u8(0), u8(0), u32(0))) == u32(%d)", oakI32(int32(c.y)), c.m, c.d, t0.YearDay()))
		b.check(fmt.Sprintf("time.is_leap_year(%s) == %v", oakI32(int32(c.y)), c.leap))
		b.check(fmt.Sprintf("time.days_in_month(%s, u8(%d)) == u8(%d)", oakI32(int32(c.y)), c.m, daysIn(c.y, c.m)))
	}
	// days_in_month outside the calendar, validation.
	b.check("time.days_in_month(i32(2001), u8(0)) == u8(0)")
	b.check("time.days_in_month(i32(2001), u8(13)) == u8(0)")
	b.check("time.civil_valid(civil(i32(2000), u8(2), u8(29), u8(23), u8(59), u8(59), u32(999999999)))")
	b.check("!time.civil_valid(civil(i32(1900), u8(2), u8(29), u8(0), u8(0), u8(0), u32(0)))")
	b.check("!time.civil_valid(civil(i32(2000), u8(4), u8(31), u8(0), u8(0), u8(0), u32(0)))")
	b.check("!time.civil_valid(civil(i32(2000), u8(0), u8(1), u8(0), u8(0), u8(0), u32(0)))")
	b.check("!time.civil_valid(civil(i32(2000), u8(1), u8(0), u8(0), u8(0), u8(0), u32(0)))")
	b.check("!time.civil_valid(civil(i32(2000), u8(1), u8(1), u8(24), u8(0), u8(0), u32(0)))")
	b.check("!time.civil_valid(civil(i32(2000), u8(1), u8(1), u8(0), u8(60), u8(0), u32(0)))")
	b.check("!time.civil_valid(civil(i32(2000), u8(1), u8(1), u8(0), u8(0), u8(60), u32(0)))")
	b.check("!time.civil_valid(civil(i32(2000), u8(1), u8(1), u8(0), u8(0), u8(0), u32(1000000000)))")

	// Civil <-> instant against Go at several offsets, both directions.
	type stamp struct {
		t   time.Time
		off int32
	}
	stamps := []stamp{
		{time.Date(1970, 1, 1, 0, 0, 0, 0, time.UTC), 0},
		{time.Date(2000, 2, 29, 12, 34, 56, 123456789, time.UTC), 330},
		{time.Date(1969, 12, 31, 23, 59, 59, 999999999, time.UTC), 0},
		{time.Date(1969, 12, 31, 15, 59, 59, 1, time.UTC), -480},
		{time.Date(2038, 1, 19, 3, 14, 8, 0, time.UTC), 1439},
		{time.Date(1900, 3, 1, 0, 0, 0, 0, time.UTC), -1439},
		{time.Date(2100, 2, 28, 23, 59, 59, 0, time.UTC), 60},
		{time.Date(2262, 4, 11, 23, 47, 16, 854775807, time.UTC), 0},
		{time.Date(1677, 9, 21, 0, 12, 43, 145224192, time.UTC), 0},
	}
	for _, s := range stamps {
		local := s.t.In(time.FixedZone("", int(s.off)*60))
		c := fmt.Sprintf("civil(%s, u8(%d), u8(%d), u8(%d), u8(%d), u8(%d), u32(%d))",
			oakI32(int32(local.Year())), local.Month(), local.Day(), local.Hour(), local.Minute(), local.Second(), local.Nanosecond())
		b.check(fmt.Sprintf("to_instant_is(%s, %s, %s)", c, oakI32(s.off), oakI64(s.t.UnixNano())))
		b.check(fmt.Sprintf("to_civil_is(%s, %s, %s)", oakI64(s.t.UnixNano()), oakI32(s.off), c))
	}
	b.check("to_instant_code(civil(i32(2001), u8(2), u8(29), u8(0), u8(0), u8(0), u32(0)), i32(0)) == u32(2)")
	b.check("to_instant_code(civil(i32(2016), u8(12), u8(31), u8(23), u8(59), u8(60), u32(0)), i32(0)) == u32(2)")
	b.check("to_instant_code(civil(i32(2000), u8(1), u8(1), u8(0), u8(0), u8(0), u32(0)), i32(1440)) == u32(4)")
	b.check("to_instant_code(civil(i32(2000), u8(1), u8(1), u8(0), u8(0), u8(0), u32(0)), i32(-1440)) == u32(4)")
	b.check("to_instant_code(civil(i32(2000), u8(1), u8(1), u8(0), u8(0), u8(0), u32(0)), i32(1439)) == u32(0)")
	b.check("to_instant_code(civil(i32(2262), u8(4), u8(12), u8(0), u8(0), u8(0), u32(0)), i32(0)) == u32(1)")
	b.check("to_instant_code(civil(i32(2262), u8(4), u8(11), u8(23), u8(47), u8(16), u32(854775808)), i32(0)) == u32(1)")
	b.check("to_instant_code(civil(i32(1677), u8(9), u8(20), u8(0), u8(0), u8(0), u32(0)), i32(0)) == u32(1)")
	b.check("to_instant_code(civil(i32(9999), u8(12), u8(31), u8(0), u8(0), u8(0), u32(0)), i32(0)) == u32(1)")
	b.check("to_instant_code(civil(i32(2262), u8(4), u8(11), u8(23), u8(47), u8(16), u32(854775807)), i32(-1)) == u32(1)")
	b.check("to_civil_code(i64(9223372036854775807), i32(1)) == u32(1)")
	b.check("to_civil_code(i64(9223372036854775807), i32(-1)) == u32(0)")
	b.check(fmt.Sprintf("to_civil_code(%s, i32(-1)) == u32(1)", oakI64(math.MinInt64)))
	b.check("to_civil_code(i64(0), i32(1440)) == u32(4)")
	// Floored second decomposition around the epoch.
	b.check("time.instant_unix_seconds(inst(i64(-1))) == i64(-1)")
	b.check("time.instant_subsecond_nanos(inst(i64(-1))) == u32(999999999)")
	b.check("time.instant_unix_seconds(inst(i64(1500000000))) == i64(1)")
	b.check("time.instant_subsecond_nanos(inst(i64(1500000000))) == u32(500000000)")
	b.check("time.instant_unix_seconds(inst(i64(0))) == i64(0)")
	runTimeChecks(t, "timecalendar", b)
}

func daysIn(y int, m time.Month) int {
	return time.Date(y, m+1, 0, 0, 0, 0, 0, time.UTC).Day()
}

const rfc3339Fixed = "2006-01-02T15:04:05.000000000Z07:00"

// goRFC3339 formats an instant at an offset with exactly `digits` fraction
// digits (0 for none), as format_rfc3339 does.
func goRFC3339(nanos int64, off int32, digits int) string {
	layout := "2006-01-02T15:04:05"
	if digits > 0 {
		layout += "." + strings.Repeat("0", digits)
	}
	layout += "Z07:00"
	return time.Unix(0, nanos).In(time.FixedZone("", int(off)*60)).Format(layout)
}

func TestE2EStdlibTimeRfc3339(t *testing.T) {
	b := &timeChecks{}
	type vector struct {
		nanos  int64
		off    int32
		digits int
	}
	vectors := []vector{
		{0, 0, 0}, {0, 0, 9}, {951807896123456789, 330, 9}, {951807896123456789, 330, 3}, {951807896123456789, 330, 0},
		{-1, -480, 3}, {-1, 0, 9}, {math.MaxInt64, 0, 9}, {math.MinInt64, 0, 9}, {math.MaxInt64, -1439, 9},
		{math.MinInt64, 1439, 9}, {1234567890123456789, 1439, 1}, {1234567890123456789, -1439, 2}, {1234567890123456789, -60, 6},
		{999999999, 0, 0}, {999999999, 0, 1}, {999999999, 0, 8}, {-999999999, 0, 9}, {-86400000000000, 0, 0},
	}
	for _, v := range vectors {
		expected := goRFC3339(v.nanos, v.off, v.digits)
		b.check(fmt.Sprintf("fmt_is(%s, %s, u32(%d), %s)", oakI64(v.nanos), oakI32(v.off), v.digits, b.text(expected)))
		b.check(fmt.Sprintf("time.rfc3339_size(%s, u32(%d)) == u32(%d)", oakI32(v.off), v.digits, len(expected)))
		// What Oak writes, Oak reads back to the same instant and offset.
		b.check(fmt.Sprintf("parse_is(%s, %s, %s)", b.text(expected), oakI64(floorTrunc(v.nanos, pow10(9-v.digits))), oakI32(v.off)))
	}
	b.check("fmt_code(i64(0), i32(0), u32(10)) == u32(3)")
	b.check("fmt_code(i64(0), i32(1440), u32(0)) == u32(4)")
	b.check("fmt_code(i64(0), i32(-1440), u32(0)) == u32(4)")
	b.check("fmt_code(i64(9223372036854775807), i32(1), u32(0)) == u32(1)")
	b.check("fmt_small_code(i64(0), i32(0), u32(0)) == u32(6)")

	// Parsing: Go's spellings, lower-case letters, error classes.
	parseOK := []struct {
		text  string
		nanos int64
		off   int32
	}{
		{"1970-01-01T00:00:00Z", 0, 0},
		{"1970-01-01t00:00:00z", 0, 0},
		{"2000-02-29T12:34:56.123+05:30", 951807896123000000, 330},
		{"2000-02-29t12:34:56.123456789+05:30", 951807896123456789, 330},
		{"1969-12-31T15:59:59.999-08:00", -1000000, -480},
		{"1969-12-31T23:59:59.999999999Z", -1, 0},
		{"1970-01-01T00:00:00.5Z", 500000000, 0},
		{"1970-01-01T00:00:00.000000001Z", 1, 0},
		{"1970-01-01T00:00:00-00:00", 0, 0},
		{"1970-01-01T00:00:00+00:00", 0, 0},
		{"1970-01-01T00:00:00+23:59", -(23*3600 + 59*60) * 1000000000, 1439},
		{"1970-01-01T00:00:00-23:59", (23*3600 + 59*60) * 1000000000, -1439},
		{"2262-04-11T23:47:16.854775807Z", math.MaxInt64, 0},
		{"1677-09-21T00:12:43.145224192Z", math.MinInt64, 0},
		{"2024-02-29T00:00:00Z", time.Date(2024, 2, 29, 0, 0, 0, 0, time.UTC).UnixNano(), 0},
	}
	for _, p := range parseOK {
		b.check(fmt.Sprintf("parse_is(%s, %s, %s)", b.text(p.text), oakI64(p.nanos), oakI32(p.off)))
	}
	parseErr := []struct {
		text string
		code int
	}{
		{"2016-12-31T23:59:60Z", 2},            // leap second: rejected
		{"2001-02-29T00:00:00Z", 2},            // not a leap year
		{"1900-02-29T00:00:00Z", 2},            // not a leap year (century)
		{"2000-13-01T00:00:00Z", 2},            // month
		{"2000-00-10T00:00:00Z", 2},            // month
		{"2000-01-00T00:00:00Z", 2},            // day
		{"2000-04-31T00:00:00Z", 2},            // day
		{"2000-01-01T24:00:00Z", 2},            // hour
		{"2000-01-01T00:60:00Z", 2},            // minute
		{"2000-01-01T00:00:00+24:00", 4},       // offset hours
		{"2000-01-01T00:00:00+05:60", 4},       // offset minutes
		{"2000-01-01T00:00:00+0530", 4},        // offset without colon
		{"2000-01-01T00:00:00+05:3", 4},        // offset cut short
		{"2000-01-01T00:00:00+05", 4},          // offset cut short
		{"2000-01-01T00:00:00", 3},             // no zone
		{"2000-01-01T00:00:00Zx", 3},           // trailing text
		{"2000-01-01T00:00:00Z ", 3},           // trailing space
		{"2000-01-01 00:00:00Z", 3},            // space separator (RFC 3339 note, not the grammar)
		{"2000-01-01T00:00:00.Z", 3},           // empty fraction
		{"2000-01-01T00:00:00.1234567890Z", 3}, // ten fraction digits
		{"2000-01-01T00:00:00,5Z", 3},          // comma fraction
		{"200-01-01T00:00:00Z", 3},             // short year
		{"2000-1-01T00:00:00Z", 3},             // short month
		{"2000-01-01T00:00:0Z", 3},             // short second
		{"2000/01/01T00:00:00Z", 3},            // separators
		{"2000-01-01X00:00:00Z", 3},            // separator letter
		{"2000-01-01T00:00:00Q", 3},            // zone letter
		{"+000-01-01T00:00:00Z", 3},            // signed year
		{"2000-01-01T00:00:00+05:30Z", 3},      // two zones
		{"1970-01-01T00:00:00Z1", 3},           // trailing digit
		{"x", 3},                               // nothing like a timestamp
	}
	for _, p := range parseErr {
		b.check(fmt.Sprintf("parse_code(%s) == u32(%d)", b.text(p.text), p.code))
	}

	// Go's RFC3339Nano spellings (trimmed fractions) at random offsets parse
	// to Go's nanoseconds.
	rng := rand.New(rand.NewSource(3339))
	offsets := []int32{0, 330, -480, 1380, -30, 60, -720, 1439, -1439}
	for i := 0; i < 160; i++ {
		nanos := rng.Int63n(math.MaxInt64-2*86400*1000000000) - (math.MaxInt64 / 2)
		if i%4 == 0 {
			nanos -= nanos % 1000000 // whole milliseconds: trailing zeros trimmed
		}
		if i%8 == 0 {
			nanos -= nanos % 1000000000 // whole seconds: no fraction at all
		}
		off := offsets[rng.Intn(len(offsets))]
		text := time.Unix(0, nanos).In(time.FixedZone("", int(off)*60)).Format(time.RFC3339Nano)
		b.check(fmt.Sprintf("parse_is(%s, %s, %s)", b.text(text), oakI64(nanos), oakI32(off)))
	}
	runTimeChecks(t, "timerfc3339", b)
}

// floorTrunc drops nanos below the unit p, toward negative infinity, as a
// truncated fraction does for instants before the epoch.
func floorTrunc(nanos, p int64) int64 {
	return nanos - ((nanos%p)+p)%p
}

func pow10(n int) int64 {
	r := int64(1)
	for ; n > 0; n-- {
		r *= 10
	}
	return r
}

func TestE2EStdlibTimeDuration(t *testing.T) {
	b := &timeChecks{}
	formats := []int64{
		0, 1, 999, 1000, 1500, 1001, 999999, 1000000, 1500000, 1000001, 999999999, 1000000000, 1500000000, 1000000001,
		60000000000, 90000000000, 3600000000000, 3723500000000, 3600000000000 * 25, 59999999999,
		-1, -1500, -1500000, -1000000000, -3723500000000, math.MaxInt64, math.MinInt64, 123456789012345678,
	}
	for _, n := range formats {
		expected := time.Duration(n).String()
		b.check(fmt.Sprintf("dur_fmt_is(%s, %s)", oakI64(n), b.text(expected)))
		// Every spelling Oak writes, Oak reads back exactly.
		b.check(fmt.Sprintf("dur_parse_is(%s, %s)", b.text(expected), oakI64(n)))
	}
	b.check("dur_fmt_small_code(i64(0)) == u32(6)")

	parses := []string{
		"1h2m3.5s", "0", "-0", "+0", "-1.5ms", "+300µs", "1μs", "300us", "12ns", "1.5h", ".5s", "5.s", "1h1h", "1m1h",
		"1.000000001s", "0.0000000001s", "1.9999999999s", "2562047h47m16.854775807s", "-2562047h47m16.854775808s",
		"9223372036854775807ns", "-9223372036854775808ns", "1h0m0s", "00001s", "1.500000000000000000001s",
		"0.5555555555555555555555h", "1000000000000000000ns", "0.000001ms",
	}
	for _, text := range parses {
		want, err := time.ParseDuration(text)
		if err != nil {
			t.Fatalf("Go rejects %q: %v", text, err)
		}
		b.check(fmt.Sprintf("dur_parse_is(%s, %s)", b.text(text), oakI64(int64(want))))
	}
	rejects := []string{
		"1", "s", "1x", "1 s", "1.5", "--1s", "1.2.3s", "-", "+", "1s-", "h", ".s", "1hs", "1ss", "1S", "1H", "1ms1",
		"3000000h", "2562048h", "2562047h47m16.854775808s", "-2562047h47m16.854775809s", "9223372036854775808ns",
		"18446744073709551616ns", "99999999999999999999999999s", "1e3s", "0x10s", " 1s", "1µ", "1m s",
	}
	for _, text := range rejects {
		if _, err := time.ParseDuration(text); err == nil {
			t.Fatalf("Go accepts %q", text)
		}
		b.check(fmt.Sprintf("dur_parse_code(%s) == u32(5)", b.text(text)))
	}

	// Constructors, accessors, arithmetic, comparison.
	b.check("dur_is(time.duration_seconds(i64(90)), i64(90000000000))")
	b.check("dur_is(time.duration_millis(i64(-1500)), i64(-1500000000))")
	b.check("dur_is(time.duration_micros(i64(7)), i64(7000))")
	b.check("dur_is(time.duration_minutes(i64(2)), i64(120000000000))")
	b.check("dur_is(time.duration_hours(i64(1)), i64(3600000000000))")
	b.check("time.duration_as_seconds(dur(i64(-1500000000))) == i64(-1)")
	b.check("time.duration_as_millis(dur(i64(1500000))) == i64(1)")
	b.check("time.duration_as_micros(dur(i64(-999))) == i64(0)")
	b.check("time.duration_as_minutes(dur(i64(119999999999))) == i64(1)")
	b.check("time.duration_as_hours(dur(i64(7200000000000))) == i64(2)")
	b.check("dur_is(time.duration_add(dur(i64(1)), dur(i64(2))), i64(3))")
	b.check("dur_is(time.duration_sub(dur(i64(1)), dur(i64(2))), i64(-1))")
	b.check("dur_is(time.duration_scale(dur(i64(-7)), i64(3)), i64(-21))")
	b.check("dur_is(time.duration_negate(dur(i64(5))), i64(-5))")
	b.check("dur_is(time.duration_negate(dur(i64(9223372036854775807))), i64(-9223372036854775807))")
	b.check("time.duration_compare(dur(i64(1)), dur(i64(2))) == i32(-1)")
	b.check("time.duration_compare(dur(i64(2)), dur(i64(2))) == i32(0)")
	b.check("time.duration_compare(dur(i64(3)), dur(i64(2))) == i32(1)")
	b.check("inst_is(time.instant_seconds(i64(-1)), i64(-1000000000))")
	b.check("inst_is(time.instant_add(inst(i64(10)), dur(i64(-15))), i64(-5))")
	b.check("inst_is(time.instant_sub(inst(i64(10)), dur(i64(-15))), i64(25))")
	b.check("dur_is(time.instant_since(inst(i64(10)), inst(i64(25))), i64(-15))")
	b.check("time.instant_compare(inst(i64(-1)), inst(i64(0))) == i32(-1)")
	b.check("time.instant_compare(inst(i64(0)), inst(i64(0))) == i32(0)")
	b.check("time.instant_compare(inst(i64(1)), inst(i64(0))) == i32(1)")
	b.check("time.DURATION_TEXT_SIZE >= u32(26)")
	runTimeChecks(t, "timeduration", b)
}

func TestE2EStdlibTimeOverflow(t *testing.T) {
	b := &timeChecks{}
	maxI := "i64(9223372036854775807)"
	minI := oakI64(math.MinInt64)
	b.check("dur_code(time.duration_seconds(i64(9223372036))) == u32(0)")
	b.check("dur_code(time.duration_seconds(i64(9223372037))) == u32(1)")
	b.check("dur_code(time.duration_seconds(i64(-9223372037))) == u32(1)")
	b.check("dur_code(time.duration_millis(i64(9223372036855))) == u32(1)")
	b.check("dur_code(time.duration_micros(i64(9223372036854776))) == u32(1)")
	b.check("dur_code(time.duration_minutes(i64(153722868))) == u32(1)")
	b.check("dur_code(time.duration_hours(i64(2562047))) == u32(0)")
	b.check("dur_code(time.duration_hours(i64(2562048))) == u32(1)")
	b.check("dur_code(time.duration_hours(i64(-2562048))) == u32(1)")
	b.check(fmt.Sprintf("dur_code(time.duration_add(dur(%s), dur(i64(1)))) == u32(1)", maxI))
	b.check(fmt.Sprintf("dur_code(time.duration_add(dur(%s), dur(i64(-1)))) == u32(1)", minI))
	b.check(fmt.Sprintf("dur_code(time.duration_add(dur(%s), dur(i64(-1)))) == u32(0)", maxI))
	b.check(fmt.Sprintf("dur_code(time.duration_sub(dur(%s), dur(i64(1)))) == u32(1)", minI))
	b.check(fmt.Sprintf("dur_code(time.duration_sub(dur(i64(0)), dur(%s))) == u32(1)", minI))
	b.check(fmt.Sprintf("dur_code(time.duration_sub(dur(i64(-1)), dur(%s))) == u32(0)", minI))
	b.check(fmt.Sprintf("dur_code(time.duration_negate(dur(%s))) == u32(1)", minI))
	b.check(fmt.Sprintf("dur_code(time.duration_negate(dur(%s))) == u32(0)", maxI))
	b.check("dur_code(time.duration_scale(dur(i64(4611686018427387904)), i64(2))) == u32(1)")
	b.check("dur_code(time.duration_scale(dur(i64(4611686018427387904)), i64(-2))) == u32(0)")
	b.check("dur_code(time.duration_scale(dur(i64(-4611686018427387904)), i64(-2))) == u32(1)")
	b.check(fmt.Sprintf("dur_code(time.duration_scale(dur(%s), i64(-1))) == u32(1)", minI))
	b.check("inst_code(time.instant_seconds(i64(9223372037))) == u32(1)")
	b.check(fmt.Sprintf("inst_code(time.instant_add(inst(%s), dur(i64(1)))) == u32(1)", maxI))
	b.check(fmt.Sprintf("inst_code(time.instant_add(inst(%s), dur(i64(-1)))) == u32(1)", minI))
	b.check(fmt.Sprintf("inst_code(time.instant_sub(inst(%s), dur(i64(1)))) == u32(1)", minI))
	b.check(fmt.Sprintf("inst_code(time.instant_sub(inst(%s), dur(i64(-1)))) == u32(1)", maxI))
	b.check(fmt.Sprintf("dur_code(time.instant_since(inst(%s), inst(i64(-1)))) == u32(1)", maxI))
	b.check(fmt.Sprintf("dur_code(time.instant_since(inst(i64(-1)), inst(%s))) == u32(0)", maxI))
	b.check(fmt.Sprintf("dur_code(time.instant_since(inst(i64(0)), inst(%s))) == u32(1)", minI))
	runTimeChecks(t, "timeoverflow", b)
}

// randomDurationText spells a random duration the way a person might type
// it for Go's ParseDuration: an optional sign, one to three terms, integer
// and fraction parts of random length (long fractions exercise the f64
// scaling), every unit spelling including both micro signs.
func randomDurationText(rng *rand.Rand) string {
	units := []string{"ns", "us", "µs", "μs", "ms", "s", "m", "h"}
	var sb strings.Builder
	if rng.Intn(3) == 0 {
		sb.WriteString("-")
	}
	terms := 1 + rng.Intn(3)
	for i := 0; i < terms; i++ {
		intDigits := rng.Intn(6)
		fracDigits := 0
		if rng.Intn(2) == 0 {
			fracDigits = 1 + rng.Intn(14)
		}
		if intDigits == 0 && fracDigits == 0 {
			intDigits = 1
		}
		for k := 0; k < intDigits; k++ {
			sb.WriteByte(byte('0' + rng.Intn(10)))
		}
		if fracDigits > 0 {
			sb.WriteByte('.')
			for k := 0; k < fracDigits; k++ {
				sb.WriteByte(byte('0' + rng.Intn(10)))
			}
		}
		sb.WriteString(units[rng.Intn(len(units))])
	}
	return sb.String()
}

// TestE2EStdlibTimeDifferential formats a few thousand random instants at
// several fixed offsets in Oak (nine fraction digits, weekday, day of year)
// and a thousand random durations, compares every line with Go's time
// package, has Oak parse each line back to the same value, and parses a few
// hundred random duration spellings to Go's ParseDuration result. The
// program is a module root and runs compiled; the check programs above
// cover the interpreter.
func TestE2EStdlibTimeDifferential(t *testing.T) {
	const count = 3000
	const durationCount = 1000
	const durationTexts = 400
	offsets := []int32{0, 330, -480, 1380, -1439, 1439, -30}
	rng := rand.New(rand.NewSource(20260911))
	nanos := make([]int64, count)
	offs := make([]int32, count)
	for i := range nanos {
		// Uniform over the Instant range, two days inside each end so the
		// offset shift never overflows.
		nanos[i] = rng.Int63n(math.MaxInt64-4*86400*1000000000) - (math.MaxInt64-4*86400*1000000000)/2
		switch i % 5 {
		case 1:
			nanos[i] -= nanos[i] % 1000000000 // whole seconds
		case 2:
			nanos[i] -= nanos[i] % 86400000000000 // midnight UTC
		case 3:
			nanos[i] = (nanos[i] % (3000 * 365 * 86400)) * 1000000000 // whole seconds near the epoch
		}
		offs[i] = offsets[i%len(offsets)]
	}
	var src strings.Builder
	src.WriteString("import(std)\nimport(\"time\")\n\n")
	src.WriteString("putchar: (ch: c.Int): c.Int = c.extern(\"putchar\")\n\n")
	fmt.Fprintf(&src, "NANOS: [%d]i64 = [%d]i64{", count, count)
	for i, n := range nanos {
		if i > 0 {
			src.WriteString(",")
		}
		if n == math.MinInt64 {
			src.WriteString("-9223372036854775807 - 1")
		} else {
			fmt.Fprintf(&src, "%d", n)
		}
	}
	src.WriteString("}\n")
	fmt.Fprintf(&src, "OFFSETS: [%d]i32 = [%d]i32{", count, count)
	for i, o := range offs {
		if i > 0 {
			src.WriteString(",")
		}
		fmt.Fprintf(&src, "%d", o)
	}
	src.WriteString("}\n")
	durations := make([]int64, durationCount)
	for i := range durations {
		switch i % 4 {
		case 0:
			durations[i] = rng.Int63() - math.MaxInt64/2 // any magnitude
		case 1:
			durations[i] = rng.Int63n(2*1000000000) - 1000000000 // sub-second
		case 2:
			durations[i] = rng.Int63n(2*3600*1000000000) - 3600*1000000000 // within an hour
		default:
			durations[i] = (rng.Int63n(200000) - 100000) * 1000000 // whole milliseconds
		}
	}
	durations[0] = math.MaxInt64
	durations[1] = math.MinInt64
	durations[2] = 0
	fmt.Fprintf(&src, "DURS: [%d]i64 = [%d]i64{", durationCount, durationCount)
	for i, d := range durations {
		if i > 0 {
			src.WriteString(",")
		}
		if d == math.MinInt64 {
			src.WriteString("-9223372036854775807 - 1")
		} else {
			fmt.Fprintf(&src, "%d", d)
		}
	}
	src.WriteString("}\n")
	var texts []string
	var wants []int64
	for len(texts) < durationTexts {
		text := randomDurationText(rng)
		want, err := time.ParseDuration(text)
		if err != nil {
			continue // out of range: the check programs cover rejection
		}
		texts = append(texts, text)
		wants = append(wants, int64(want))
	}
	var flat []byte
	var starts, lengths []int
	for _, text := range texts {
		starts = append(starts, len(flat))
		lengths = append(lengths, len(text))
		flat = append(flat, text...)
	}
	fmt.Fprintf(&src, "DTEXT: [%d]u8 = %s\n", len(flat), oakByteArray(flat))
	fmt.Fprintf(&src, "DSTART: [%d]u32 = [%d]u32{", len(starts), len(starts))
	for i, v := range starts {
		if i > 0 {
			src.WriteString(",")
		}
		fmt.Fprintf(&src, "%d", v)
	}
	src.WriteString("}\n")
	fmt.Fprintf(&src, "DLEN: [%d]u32 = [%d]u32{", len(lengths), len(lengths))
	for i, v := range lengths {
		if i > 0 {
			src.WriteString(",")
		}
		fmt.Fprintf(&src, "%d", v)
	}
	src.WriteString("}\n")
	fmt.Fprintf(&src, "DWANT: [%d]i64 = [%d]i64{", len(wants), len(wants))
	for i, v := range wants {
		if i > 0 {
			src.WriteString(",")
		}
		fmt.Fprintf(&src, "%d", v)
	}
	src.WriteString("}\n")
	src.WriteString(`
put: (b: u8): () {
  _ = putchar(c.Int(i32_bits_u32(u32(b))))
}

put_padded: (value: u32, width: u32): () {
  divisor: u32 = 1
  k: u32 = 1
  while k < width {
    divisor = divisor * u32(10)
    k = k + u32(1)
  }
  while divisor > u32(0) {
    put(u8(48) + u8_trunc_u32((value / divisor) % u32(10)))
    divisor = divisor / u32(10)
  }
}

// one formats NANOS[i] at OFFSETS[i] and prints the line; true when the
// text parses back to the same instant and offset.
one: (i: u32): Bool {
  nanos: i64 = NANOS[i]
  off: i32 = OFFSETS[i]
  buf: [48]u8
  r: Result[u32, time.TimeError] = time.format_rfc3339(span(&buf), time.instant_nanos(nanos), off, u32(9))
  r ?
    | .Err(e) => { false }
    | .Ok(n) => {
      k: u32 = 0
      while k < n {
        put(buf[k])
        k = k + u32(1)
      }
      civil: Result[time.Civil, time.TimeError] = time.instant_to_civil(time.instant_nanos(nanos), off)
      civil ?
        | .Err(e2) => { false }
        | .Ok(c) => {
          put(u8(32))
          put(u8(48) + time.weekday(time.days_from_civil(c.year, c.month, c.day)))
          put(u8(32))
          put_padded(time.day_of_year(c), u32(3))
          put(u8(10))
          v: []u8 = view(&buf)
          parsed: Result[time.Zoned, time.TimeError] = time.parse_rfc3339(v[0:n])
          parsed ? | .Err(e3) => { false } | .Ok(z) => { z.instant.nanos == nanos && z.offset_minutes == off }
        }
    }
}

// one_duration prints DURS[i] in Go's spelling; true when the text parses
// back to the same duration.
one_duration: (i: u32): Bool {
  nanos: i64 = DURS[i]
  buf: [48]u8
  r: Result[u32, time.TimeError] = time.format_duration(span(&buf), time.duration_nanos(nanos))
  r ?
    | .Err(e) => { false }
    | .Ok(n) => {
      k: u32 = 0
      while k < n {
        put(buf[k])
        k = k + u32(1)
      }
      put(u8(10))
      v: []u8 = view(&buf)
      parsed: Result[time.Duration, time.TimeError] = time.parse_duration(v[0:n])
      parsed ? | .Err(e2) => { false } | .Ok(d) => { d.nanos == nanos }
    }
}

// one_text parses the i-th embedded spelling to Go's value.
one_text: (i: u32): Bool {
  v: []u8 = view(&DTEXT)
  start: u32 = DSTART[i]
  parsed: Result[time.Duration, time.TimeError] = time.parse_duration(v[start:start + DLEN[i]])
  parsed ? | .Err(e) => { false } | .Ok(d) => { d.nanos == DWANT[i] }
}

main: (): i32 {
  failures: u32 = 0
  i: u32 = 0
  while i < len(NANOS) {
    one(i) ? { } | { failures = failures + u32(1) }
    i = i + u32(1)
  }
  j: u32 = 0
  while j < len(DURS) {
    one_duration(j) ? { } | { failures = failures + u32(1) }
    j = j + u32(1)
  }
  k: u32 = 0
  while k < len(DSTART) {
    one_text(k) ? { } | { failures = failures + u32(1) }
    k = k + u32(1)
  }
  failures > u32(200) ? { i32(200) } | { i32_bits_u32(failures) }
}
`)
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/timediff\noak 0.1.0\n",
		"main.oak": "package main\n" + src.String(),
	})
	stdout, code, abnormal := buildAndRunFrom(t, "timediff", New().WithPackageDir(root))
	if abnormal {
		t.Fatalf("differential program terminated abnormally (code %d)", code)
	}
	lines := strings.Split(strings.TrimSuffix(stdout, "\n"), "\n")
	if len(lines) != count+durationCount {
		t.Fatalf("got %d lines, want %d", len(lines), count+durationCount)
	}
	mismatches := 0
	for i, line := range lines[:count] {
		local := time.Unix(0, nanos[i]).In(time.FixedZone("", int(offs[i])*60))
		want := fmt.Sprintf("%s %d %03d", local.Format(rfc3339Fixed), int(local.Weekday()), local.YearDay())
		if line != want {
			mismatches++
			if mismatches <= 10 {
				t.Errorf("instant %d at %+d: oak %q, go %q", nanos[i], offs[i], line, want)
			}
		}
	}
	for i, line := range lines[count:] {
		want := time.Duration(durations[i]).String()
		if line != want {
			mismatches++
			if mismatches <= 10 {
				t.Errorf("duration %d: oak %q, go %q", durations[i], line, want)
			}
		}
	}
	if mismatches > 0 {
		t.Fatalf("%d of %d lines differ from Go", mismatches, len(lines))
	}
	if code != 0 {
		t.Fatalf("%d values did not parse back to themselves or to Go's value", code)
	}
}
