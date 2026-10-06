package compiler

import (
	"fmt"
	"math"
	"math/rand"
	"testing"
	"time"
)

const timeISOTestPrelude = `
date_value: (y: i32, m: u8, d: u8): time.Date = time.Date { year: y, month: m, day: d }
period: (m: i32, d: i32, ns: i64): time.Period = time.Period { months: m, days: d, time: time.duration_nanos(ns) }
iso_date_is: (r: Result[time.Date, time.TimeError], y: i32, m: u8, d: u8): Bool {
 r ? | .Err(e) => false | .Ok(v) => v.year == y && v.month == m && v.day == d
}
iso_date_code: (r: Result[time.Date, time.TimeError]): u32 { r ? | .Err(e) => err_code(e) | .Ok(v) => u32(0) }
iso_dt_is: (r: Result[time.DateTime, time.TimeError], c: time.Civil): Bool {
 r ? | .Err(e) => false | .Ok(v) => civil_eq(time.datetime_civil(v), c)
}
iso_period_is: (text: []u8, m: i32, d: i32, ns: i64): Bool {
 r: Result[time.Period, time.TimeError] = time.parse_iso_period(text)
 r ? | .Err(e) => false | .Ok(p) => p.months == m && p.days == d && p.time.nanos == ns
}
iso_period_code: (text: []u8): u32 {
 r: Result[time.Period, time.TimeError] = time.parse_iso_period(text)
 r ? | .Err(e) => err_code(e) | .Ok(p) => u32(0)
}
iso_duration_is: (text: []u8, ns: i64): Bool { dur_is(time.parse_iso_duration(text), ns) }
iso_fmt_is: (p: time.Period, expected: []u8): Bool {
 buf: [64]u8
 r: Result[u32, time.TimeError] = time.format_iso_period(span(&buf), p)
 r ? | .Err(e) => false | .Ok(n) => {
  v: []u8 = view(&buf)
  same(v[0:n], expected) && iso_period_is(v[0:n], p.months, p.days, p.time.nanos)
 }
}
iso_duration_roundtrip: (ns: i64): Bool {
 buf: [64]u8
 r: Result[u32, time.TimeError] = time.format_iso_duration(span(&buf), time.duration_nanos(ns))
 r ? | .Err(e) => false | .Ok(n) => { v: []u8 = view(&buf); iso_duration_is(v[0:n], ns) }
}
iso_canonical_date: (text: []u8, expected: []u8): Bool {
 r: Result[time.Date, time.TimeError] = time.parse_iso_date(text)
 r ? | .Err(e) => false | .Ok(d) => {
  buf: [10]u8
  f: Result[u32, time.TimeError] = time.format_iso_date(span(&buf), d)
  f ? | .Err(e) => false | .Ok(n) => { v: []u8 = view(&buf); same(v[0:n], expected) }
 }
}
iso_week_is: (d: time.Date, y: i32, w: u8, day: u8): Bool {
 r: Result[time.WeekDate, time.TimeError] = time.date_to_week(d)
 r ? | .Err(e) => false | .Ok(v) => v.year == y && v.week == w && v.weekday == day
}
rfc_canonical: (text: []u8, expected: []u8, kind: u32, off: i32): Bool {
 r: Result[time.OffsetDateTime, time.TimeError] = time.parse_rfc3339_datetime(text)
 r ? | .Err(e) => false | .Ok(z) => {
  actual: u32 = z.offset_kind ? | .UtcDesignator => u32(0) | .Numeric => u32(1) | .UnknownLocal => u32(2)
  buf: [35]u8
  f: Result[u32, time.TimeError] = time.format_rfc3339_datetime(span(&buf), z)
  f ? | .Err(e) => false | .Ok(n) => { v: []u8 = view(&buf); actual == kind && z.offset_minutes == off && same(v[0:n], expected) }
 }
}
rfc_datetime_code: (text: []u8): u32 {
 r: Result[time.OffsetDateTime, time.TimeError] = time.parse_rfc3339_datetime(text)
 r ? | .Err(e) => err_code(e) | .Ok(z) => u32(0)
}
rfc_instant_code: (text: []u8): u32 {
 r: Result[time.OffsetDateTime, time.TimeError] = time.parse_rfc3339_datetime(text)
 r ? | .Err(e) => err_code(e) | .Ok(z) => inst_code(time.offset_datetime_to_instant(z))
}
iso_week_code: (d: time.Date): u32 {
 r: Result[time.WeekDate, time.TimeError] = time.date_to_week(d)
 r ? | .Err(e) => err_code(e) | .Ok(w) => u32(0)
}
rfc_instant_is: (text: []u8, expected: i64): Bool {
 r: Result[time.OffsetDateTime, time.TimeError] = time.parse_rfc3339_datetime(text)
 r ? | .Err(e) => false | .Ok(z) => inst_is(time.offset_datetime_to_instant(z), expected)
}
iso_dt_roundtrip: (text: []u8, expected: []u8): Bool {
 r: Result[time.DateTime, time.TimeError] = time.parse_iso_datetime(text)
 r ? | .Err(e) => false | .Ok(dt) => {
  buf: [29]u8
  f: Result[u32, time.TimeError] = time.format_iso_datetime(span(&buf), dt)
  f ? | .Err(e) => false | .Ok(n) => { v: []u8 = view(&buf); same(v[0:n], expected) }
 }
}
iso_unchanged: (): Bool {
 buf: [3]u8 = [3]u8{11,22,33}
 p: time.Period = period(i32(1), i32(0), i64(0))
 // Exactly enough space succeeds, an undersized destination is unchanged.
 ok: Result[u32, time.TimeError] = time.format_iso_period(span(&buf), p)
 success: Bool = ok ? | .Ok(n) => n == u32(3) | .Err(e) => false
 buf[0] = u8(11); buf[1] = u8(22); buf[2] = u8(33)
 r: Result[u32, time.TimeError] = time.format_iso_date(span(&buf), date_value(i32(2024),u8(2),u8(29)))
 small: Bool = r ? | .Ok(n) => false | .Err(e) => err_code(e) == u32(6)
 invalid: Result[u32, time.TimeError] = time.format_iso_period(span(&buf), period(i32(1),i32(-1),i64(0)))
 mixed: Bool = invalid ? | .Ok(n) => false | .Err(e) => err_code(e) == u32(5)
 success && small && mixed && buf[0] == u8(11) && buf[1] == u8(22) && buf[2] == u8(33)
}
`

func TestE2EStdlibTimeISOCalendar(t *testing.T) {
	b := &timeChecks{prelude: timeISOTestPrelude}
	for _, pair := range [][2]string{
		{"2024-02-29", "2024-02-29"}, {"20240229", "2024-02-29"},
		{"2024-060", "2024-02-29"}, {"2024060", "2024-02-29"},
		{"2020-W01-1", "2019-12-30"}, {"2020W011", "2019-12-30"},
		{"2020-W53-7", "2021-01-03"}, {"0000-01-01", "0000-01-01"}, {"9999-12-31", "9999-12-31"},
	} {
		a, c := b.text(pair[0]), b.text(pair[1])
		b.check(fmt.Sprintf("iso_canonical_date(%s,%s)", a, c))
	}
	for _, bad := range []string{"", "2024", "2024-2-29", "2024-02-30", "1900-02-29", "2023-366", "2024-000", "2021-W53-1", "2024-W00-1", "2024-W01-0", "2024-W01-8", "2024-w01-1", "20240101x", "2024/01/01", "2024-W01", "2024-01-01Z"} {
		b.check(fmt.Sprintf("iso_date_code(time.parse_iso_date(%s)) != u32(0)", b.text(bad)))
	}
	b.check("iso_unchanged()")
	b.check("iso_week_code(date_value(i32(0),u8(1),u8(1))) == u32(1)")
	b.check("iso_week_is(date_value(i32(0),u8(1),u8(3)),i32(0),u8(1),u8(1))")
	b.check("iso_date_is(time.date_add_months(date_value(i32(2024),u8(3),u8(31)),i32(-1),.Clamp),i32(2024),u8(2),u8(29))")
	b.check("iso_date_code(time.date_add_months(date_value(i32(0),u8(1),u8(1)),i32(-1),.Reject)) == u32(1)")
	b.check("iso_date_code(time.date_add_days(date_value(i32(2024),u8(1),u8(1)),i64(9223372036854775807))) == u32(1)")
	rng := rand.New(rand.NewSource(8601))
	for i := 0; i < 100; i++ {
		day := time.Date(rng.Intn(9998)+1, time.Month(rng.Intn(12)+1), rng.Intn(28)+1, 0, 0, 0, 0, time.UTC)
		dv := fmt.Sprintf("date_value(i32(%d),u8(%d),u8(%d))", day.Year(), day.Month(), day.Day())
		delta := rng.Intn(1000) - 500
		next := day.AddDate(0, 0, delta)
		b.check(fmt.Sprintf("iso_date_is(time.date_add_days(%s,i64(%d)),i32(%d),u8(%d),u8(%d))", dv, delta, next.Year(), next.Month(), next.Day()))
		wy, ww := day.ISOWeek()
		wd := int(day.Weekday())
		if wd == 0 {
			wd = 7
		}
		b.check(fmt.Sprintf("iso_week_is(%s,i32(%d),u8(%d),u8(%d))", dv, wy, ww, wd))
		b.check(fmt.Sprintf("iso_date_is(time.date_from_epoch_days(i64(%d)),i32(%d),u8(%d),u8(%d))", day.Unix()/86400, day.Year(), day.Month(), day.Day()))
	}
	b.check("iso_date_code(time.date_add_months(date_value(i32(2024),u8(1),u8(31)),i32(1),.Reject)) == u32(2)")
	b.check("iso_date_is(time.date_add_months(date_value(i32(2024),u8(1),u8(31)),i32(1),.Clamp),i32(2024),u8(2),u8(29))")
	b.check("iso_date_is(time.date_add_period(date_value(i32(2024),u8(1),u8(31)),period(i32(1),i32(1),i64(0)),.Clamp),i32(2024),u8(3),u8(1))")
	for _, days := range []int64{math.MinInt64, math.MaxInt64, -719529, 2932897} {
		b.check(fmt.Sprintf("iso_date_code(time.date_from_epoch_days(%s)) == u32(1)", oakI64(days)))
	}
	b.check("iso_date_code(time.date_add_days(date_value(i32(9999),u8(12),u8(31)),i64(1))) == u32(1)")
	b.check("iso_date_code(time.date_add_days(date_value(i32(0),u8(1),u8(1)),i64(-1))) == u32(1)")
	b.check("iso_date_code(time.date_add_period(date_value(i32(2024),u8(1),u8(1)),period(i32(0),i32(0),i64(1)),.Reject)) == u32(5)")
	runTimeChecks(t, "timeisocalendar", b)
}

func TestE2EStdlibTimeISOPeriod(t *testing.T) {
	b := &timeChecks{prelude: timeISOTestPrelude}
	for _, c := range []struct {
		s    string
		m, d int32
		ns   int64
	}{
		{"P1Y2M3DT4H5M6.000000007S", 14, 3, 14706000000007},
		{"P2W", 0, 14, 0}, {"P1D", 0, 1, 0}, {"PT24H", 0, 0, 86400000000000},
		{"PT0S", 0, 0, 0}, {"P0D", 0, 0, 0}, {"-P1M2D", -1, -2, 0}, {"+PT0,5S", 0, 0, 500000000},
		{"PT9223372036.854775807S", 0, 0, math.MaxInt64},
		{"-PT9223372036.854775808S", 0, 0, math.MinInt64},
		{"P2147483647M2147483647D", math.MaxInt32, math.MaxInt32, 0},
		{"-P2147483648M2147483648D", math.MinInt32, math.MinInt32, 0},
	} {
		b.check(fmt.Sprintf("iso_period_is(%s,%s,%s,%s)", b.text(c.s), oakI32(c.m), oakI32(c.d), oakI64(c.ns)))
	}
	for _, s := range []string{"", "P", "PT", "P1DT", "PT1ST", "P1W1D", "P1D1W", "P1WT1H", "P1Y1W", "P1M1Y", "PT1S1M", "PT1M1M", "P1.5D", "PT1.5H", "PT.5S", "PT1.S", "PT1.0000000000S", "P-1D", "P1H", "P1S", "PT1D", "P1Q", "pt1s", " PT1S", "PT1Sx", "P1D2D", "P2147483647M1Y"} {
		b.check(fmt.Sprintf("iso_period_code(%s) == u32(5)", b.text(s)))
	}
	for _, s := range []string{"PT9223372036.854775808S", "-PT9223372036.854775809S", "P2147483648M", "P2147483648D", "P178956971Y", "P306783379W", "PT18446744073709551616S"} {
		b.check(fmt.Sprintf("iso_period_code(%s) == u32(1)", b.text(s)))
	}
	for _, s := range []string{"P1D", "P0D", "P1M", "P1W", "P1DT1H"} {
		b.check(fmt.Sprintf("dur_code(time.parse_iso_duration(%s)) == u32(5)", b.text(s)))
	}
	for _, c := range []struct {
		m, d int32
		ns   int64
		s    string
	}{
		{14, 3, 14706000000007, "P14M3DT4H5M6.000000007S"},
		{0, 1, 0, "P1D"}, {0, 0, 86400000000000, "PT24H"}, {0, 0, 0, "PT0S"},
		{0, 0, math.MinInt64, "-PT2562047H47M16.854775808S"},
		{math.MinInt32, math.MinInt32, 0, "-P2147483648M2147483648D"},
	} {
		b.check(fmt.Sprintf("iso_fmt_is(period(%s,%s,%s),%s)", oakI32(c.m), oakI32(c.d), oakI64(c.ns), b.text(c.s)))
	}
	rng := rand.New(rand.NewSource(3339))
	for _, n := range []int64{math.MinInt64, math.MaxInt64, -1, 0, 1} {
		b.check(fmt.Sprintf("iso_duration_roundtrip(%s)", oakI64(n)))
	}
	for i := 0; i < 100; i++ {
		b.check(fmt.Sprintf("iso_duration_roundtrip(%s)", oakI64(int64(rng.Uint64()))))
	}
	runTimeChecks(t, "timeisoperiod", b)
}

func TestE2EStdlibTimeISODateTime(t *testing.T) {
	b := &timeChecks{prelude: timeISOTestPrelude}
	for _, c := range []struct {
		s, want string
		kind    uint32
		off     int32
	}{
		{"0000-01-01T00:00:00Z", "0000-01-01T00:00:00Z", 0, 0},
		{"9999-12-31T23:59:59.999999999+23:59", "9999-12-31T23:59:59.999999999+23:59", 1, 1439},
		{"2024-02-29t12:34:56.1200z", "2024-02-29T12:34:56.12Z", 0, 0},
		{"1970-01-01T00:00:00+00:00", "1970-01-01T00:00:00+00:00", 1, 0},
		{"1970-01-01T00:00:00-00:00", "1970-01-01T00:00:00-00:00", 2, 0},
		{"2000-01-01T12:00:00-05:30", "2000-01-01T12:00:00-05:30", 1, -330},
	} {
		s, w := b.text(c.s), b.text(c.want)
		b.check(fmt.Sprintf("rfc_canonical(%s,%s,u32(%d),i32(%d))", s, w, c.kind, c.off))
	}
	for _, s := range []string{"", "2000-01-01", "2000-01-01T00:00:00", "2000-01-01 00:00:00Z", "2000-01-01T00:00:00,1Z", "2000-01-01T00:00:00.Z", "2000-01-01T00:00:00.1234567890Z", "2000-01-01T00:00:00+00", "2000-01-01T00:00:00+24:00", "2000-01-01T00:00:00+00:60", "2000-01-01T00:00:00Zx", "2000-01-01T24:00:00Z", "2016-12-31T23:59:60Z", "2001-02-29T00:00:00Z", "2000-W01-1T00:00:00Z"} {
		b.check(fmt.Sprintf("rfc_datetime_code(%s) != u32(0)", b.text(s)))
	}
	for _, s := range []string{"1970-01-01T00:00:00Z", "1970-01-01T00:00:00+00:00", "1970-01-01T00:00:00-00:00", "1970-01-01T01:00:00+01:00", "1969-12-31T23:00:00-01:00"} {
		b.check(fmt.Sprintf("rfc_instant_is(%s,i64(0))", b.text(s)))
	}
	a, c := b.text("2024-02-29T12:34:56,1200"), b.text("2024-02-29T12:34:56.12")
	b.check(fmt.Sprintf("iso_dt_roundtrip(%s,%s)", a, c))
	b.check(fmt.Sprintf("rfc_instant_code(%s) == u32(1)", b.text("0000-01-01T00:00:00Z")))
	b.check(fmt.Sprintf("rfc_instant_code(%s) == u32(1)", b.text("9999-12-31T23:59:59Z")))
	dt := "time.DateTime { date: date_value(i32(2024),u8(1),u8(31)), time: time.Time {hour:u8(23),minute:u8(59),second:u8(59),nanos:u32(999999999)} }"
	b.check(fmt.Sprintf("iso_dt_is(time.datetime_add_period(%s,period(i32(1),i32(0),i64(1)),.Clamp),civil(i32(2024),u8(3),u8(1),u8(0),u8(0),u8(0),u32(0)))", dt))
	rng := rand.New(rand.NewSource(20261006))
	for i := 0; i < 100; i++ {
		start := time.Date(2000+rng.Intn(20), time.Month(rng.Intn(12)+1), rng.Intn(28)+1, rng.Intn(24), rng.Intn(60), rng.Intn(60), rng.Intn(1000000000), time.UTC)
		delta := int64(rng.Uint64())
		if i == 0 {
			delta = math.MinInt64
		}
		if i == 1 {
			delta = math.MaxInt64
		}
		if i == 2 {
			delta = -1
			start = time.Date(2000, 1, 1, 0, 0, 0, 0, time.UTC)
		}
		end := start.Add(time.Duration(delta))
		dt := fmt.Sprintf("time.DateTime { date: date_value(i32(%d),u8(%d),u8(%d)), time: time.Time { hour:u8(%d),minute:u8(%d),second:u8(%d),nanos:u32(%d) } }", start.Year(), start.Month(), start.Day(), start.Hour(), start.Minute(), start.Second(), start.Nanosecond())
		b.check(fmt.Sprintf("iso_dt_is(time.datetime_add_duration(%s,time.duration_nanos(%s)),civil(i32(%d),u8(%d),u8(%d),u8(%d),u8(%d),u8(%d),u32(%d)))", dt, oakI64(delta), end.Year(), end.Month(), end.Day(), end.Hour(), end.Minute(), end.Second(), end.Nanosecond()))
	}
	runTimeChecks(t, "timeisodatetime", b)
}
