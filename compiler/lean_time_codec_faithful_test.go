package compiler

import (
	"fmt"
	"math"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// The same inputs and independent expected fields/bytes run through compiled
// Oak, interpreted Oak, and the extracted Lean. Round trips alone are not an
// oracle: a parser and formatter can share a bug. Go supplies civil spellings;
// the period oracle below uses unsigned magnitudes, including signed minima.
func TestLeanTimeCodecFaithful(t *testing.T) {
	skipInShort(t)
	lake := findLake()
	if lake == "" {
		if os.Getenv("OAK_REQUIRE_TIME_LEAN") == "1" {
			t.Fatal("OAK_REQUIRE_TIME_LEAN=1 but lake was not found")
		}
		t.Skip("codec correspondence requires lake")
	}
	b := &timeChecks{prelude: timeISOTestPrelude + codecTestPrelude}
	var lean strings.Builder
	lean.WriteString("import Oak.Stdlib.TimeCalendarExtracted\nopen Oak.Stdlib.Time\nset_option maxRecDepth 65536\nset_option maxHeartbeats 4000000\n")
	add := func(oak, call, want, label string) {
		i := len(b.entries)
		if i%timeChunk == 0 {
			fmt.Fprintf(&lean, "def check%d : IO Unit := do\n", i/timeChunk)
		}
		b.check(oak)
		fmt.Fprintf(&lean, "  unless %s == %s do\n    throw (IO.userError \"codec case %d: %s\")\n", call, want, i, label)
	}
	parse := func(c codecCase) {
		ov, lv := c.value.literals(c.kind)
		want := "some (.Ok " + lv + ")"
		if c.err != 0 {
			want = "some (.Err ." + codecError(c.err) + ")"
		}
		add(fmt.Sprintf("codec_parse_%s(%s,%s,u32(%d))", c.kind, b.text(c.text), ov, c.err),
			fmt.Sprintf("(parse_%s %s 256)", c.kind, leanBytes([]byte(c.text))), want, "parse_"+c.kind)
	}
	format := func(c codecCase, capacity int) {
		ov, lv := c.value.literals(c.kind)
		before := make([]byte, capacity)
		for i := range before {
			before[i] = byte(128 + i%127)
		}
		after := append([]byte(nil), before...)
		code := c.err
		if code == 0 && capacity < len(c.canonical) {
			code = 6
		}
		if code == 0 {
			copy(after, c.canonical)
		}
		i := len(b.entries)
		fmt.Fprintf(&b.pending, " buf%d: [%d]u8 = %s\n r%d: Result[u32,time.TimeError] = time.format_%s(span(&buf%d),%s)\n", i, capacity, oakByteArray(before), i, c.kind, i, ov)
		expected := b.text(string(after))
		result := fmt.Sprintf(".Ok %d", len(c.canonical))
		if code != 0 {
			result = ".Err ." + codecError(code)
		}
		add(fmt.Sprintf("codec_format_result(r%d,u32(%d),u32(%d)) && same(view(&buf%d),%s)", i, code, len(c.canonical), i, expected),
			fmt.Sprintf("(format_%s %s %s 256)", c.kind, leanBytes(before), lv),
			fmt.Sprintf("some (%s,%s)", result, leanBytes(after)), "format_"+c.kind)
	}
	cases := codecCorpus()
	for _, c := range cases {
		parse(c)
		if c.err == 0 {
			format(c, len(c.canonical)+3)
			if c.text != c.canonical {
				cc := c
				cc.text = cc.canonical
				parse(cc)
			}
		}
	}
	// Every capacity through each documented maximum, including zero, exact
	// capacity, and a suffix. Full destination arrays are compared on both paths.
	for _, c := range codecCapacityCases() {
		maximum := map[string]int{"iso_date": 10, "iso_time": 18, "iso_datetime": 29, "rfc3339_datetime": 35, "iso_period": 64, "iso_duration": 64}[c.kind]
		for n := 0; n <= maximum+2; n++ {
			format(c, n)
		}
	}
	// Validation errors must leave even a generously sized destination unchanged.
	for _, c := range codecInvalidValues() {
		for _, n := range []int{0, 3, 70} {
			format(c, n)
		}
	}
	lean.WriteString("def main : IO Unit := do\n")
	for n := 0; n < b.chunks(); n++ {
		fmt.Fprintf(&lean, "  check%d\n", n)
	}
	fmt.Fprintf(&lean, "  IO.println \"codecs: %d cases passed\"\n", len(b.entries))
	t.Run("compiled_and_interpreted", func(t *testing.T) { runTimeChecks(t, "codecfaithful", b) })
	t.Run("extracted_lean", func(t *testing.T) {
		root, err := filepath.Abs(filepath.Join("..", "spec", "lean"))
		if err != nil {
			t.Fatal(err)
		}
		build := exec.Command(lake, "build", "Oak.Stdlib.TimeCalendarExtracted")
		build.Dir = root
		if out, err := build.CombinedOutput(); err != nil {
			t.Fatalf("build temporal extraction: %v\n%s", err, out)
		}
		driver := filepath.Join(t.TempDir(), "codecs.lean")
		if err := os.WriteFile(driver, []byte(lean.String()), 0o644); err != nil {
			t.Fatal(err)
		}
		run := exec.Command(lake, "env", "lean", "--run", driver)
		run.Dir = root
		out, err := run.CombinedOutput()
		if err != nil {
			t.Fatalf("Lean codec corpus: %v\n%s", err, out)
		}
		if want := fmt.Sprintf("codecs: %d cases passed\n", len(b.entries)); string(out) != want {
			t.Fatalf("unexpected Lean result: %q (want %q)", out, want)
		}
	})
	if !t.Failed() {
		t.Logf("%d shared codec cases passed in the selected execution paths", len(b.entries))
	}
}

const codecTestPrelude = `
codec_time_eq: (a: time.Time,b: time.Time): Bool = a.hour == b.hour && a.minute == b.minute && a.second == b.second && a.nanos == b.nanos
codec_date_eq: (a: time.Date,b: time.Date): Bool = a.year == b.year && a.month == b.month && a.day == b.day
codec_dt_eq: (a: time.DateTime,b: time.DateTime): Bool = codec_date_eq(a.date,b.date) && codec_time_eq(a.time,b.time)
codec_kind: (k: time.OffsetKind): u32 = k ? | .UtcDesignator => u32(0) | .Numeric => u32(1) | .UnknownLocal => u32(2)
codec_parse_iso_date: (s: []u8,w: time.Date,c: u32): Bool {
 r: Result[time.Date,time.TimeError] = time.parse_iso_date(s)
 r ? | .Err(e) => err_code(e) == c | .Ok(v) => c == u32(0) && codec_date_eq(v,w)
}
codec_parse_iso_time: (s: []u8,w: time.Time,c: u32): Bool {
 r: Result[time.Time,time.TimeError] = time.parse_iso_time(s)
 r ? | .Err(e) => err_code(e) == c | .Ok(v) => c == u32(0) && codec_time_eq(v,w)
}
codec_parse_iso_datetime: (s: []u8,w: time.DateTime,c: u32): Bool {
 r: Result[time.DateTime,time.TimeError] = time.parse_iso_datetime(s)
 r ? | .Err(e) => err_code(e) == c | .Ok(v) => c == u32(0) && codec_dt_eq(v,w)
}
codec_parse_rfc3339_datetime: (s: []u8,w: time.OffsetDateTime,c: u32): Bool {
 r: Result[time.OffsetDateTime,time.TimeError] = time.parse_rfc3339_datetime(s)
 r ? | .Err(e) => err_code(e) == c | .Ok(v) => c == u32(0) && codec_dt_eq(v.datetime,w.datetime) && v.offset_minutes == w.offset_minutes && codec_kind(v.offset_kind) == codec_kind(w.offset_kind)
}
codec_parse_iso_period: (s: []u8,w: time.Period,c: u32): Bool {
 r: Result[time.Period,time.TimeError] = time.parse_iso_period(s)
 r ? | .Err(e) => err_code(e) == c | .Ok(v) => c == u32(0) && v.months == w.months && v.days == w.days && v.time.nanos == w.time.nanos
}
codec_parse_iso_duration: (s: []u8,w: time.Duration,c: u32): Bool {
 r: Result[time.Duration,time.TimeError] = time.parse_iso_duration(s)
 r ? | .Err(e) => err_code(e) == c | .Ok(v) => c == u32(0) && v.nanos == w.nanos
}
codec_format_result: (r: Result[u32,time.TimeError],c: u32,n: u32): Bool {
 r ? | .Err(e) => err_code(e) == c | .Ok(v) => c == u32(0) && v == n
}
`

type codecValue struct {
	y               int32
	mo, d, h, mi, s uint8
	ns              uint32
	off             int32
	kind            int
	months, days    int32
	duration        int64
}
type codecCase struct {
	kind, text, canonical string
	value                 codecValue
	err                   int
}

func (v codecValue) literals(kind string) (string, string) {
	od := fmt.Sprintf("date_value(%s,u8(%d),u8(%d))", oakI32(v.y), v.mo, v.d)
	ld := fmt.Sprintf("(⟨%d,%d,%d⟩ : Date)", v.y, v.mo, v.d)
	ot := fmt.Sprintf("time.Time { hour:u8(%d),minute:u8(%d),second:u8(%d),nanos:u32(%d) }", v.h, v.mi, v.s, v.ns)
	lt := fmt.Sprintf("(⟨%d,%d,%d,%d⟩ : Time)", v.h, v.mi, v.s, v.ns)
	odt := "time.DateTime { date:" + od + ",time:" + ot + " }"
	ldt := "(⟨" + ld + "," + lt + "⟩ : DateTime)"
	switch kind {
	case "iso_date":
		return od, ld
	case "iso_time":
		return ot, lt
	case "iso_datetime":
		return odt, ldt
	case "rfc3339_datetime":
		k := []string{"UtcDesignator", "Numeric", "UnknownLocal"}[v.kind]
		return fmt.Sprintf("time.OffsetDateTime { datetime:%s,offset_minutes:%s,offset_kind:.%s }", odt, oakI32(v.off), k), fmt.Sprintf("(⟨%s,%d,.%s⟩ : OffsetDateTime)", ldt, v.off, k)
	case "iso_period":
		return fmt.Sprintf("period(%s,%s,%s)", oakI32(v.months), oakI32(v.days), oakI64(v.duration)), fmt.Sprintf("(⟨%d,%d,⟨%d⟩⟩ : Period)", v.months, v.days, v.duration)
	case "iso_duration":
		return "time.duration_nanos(" + oakI64(v.duration) + ")", fmt.Sprintf("(⟨%d⟩ : Duration)", v.duration)
	}
	panic(kind)
}
func leanBytes(bs []byte) string {
	values := make([]string, len(bs))
	for i, b := range bs {
		values[i] = fmt.Sprint(b)
	}
	return "#[" + strings.Join(values, ",") + "]"
}
func codecError(n int) string {
	return []string{"", "Overflowed", "InvalidCivil", "InvalidFormat", "InvalidOffset", "InvalidDuration", "DestinationTooSmall", "Unattested"}[n]
}
func codecCivil(t time.Time) codecValue {
	return codecValue{y: int32(t.Year()), mo: uint8(t.Month()), d: uint8(t.Day()), h: uint8(t.Hour()), mi: uint8(t.Minute()), s: uint8(t.Second()), ns: uint32(t.Nanosecond())}
}
func codecMagnitude(n int64) uint64 {
	if n < 0 {
		return uint64(-(n + 1)) + 1
	}
	return uint64(n)
}
func codecPeriodText(v codecValue) string {
	var b strings.Builder
	if v.months < 0 || v.days < 0 || v.duration < 0 {
		b.WriteByte('-')
	}
	b.WriteByte('P')
	if v.months != 0 {
		fmt.Fprintf(&b, "%dM", codecMagnitude(int64(v.months)))
	}
	if v.days != 0 {
		fmt.Fprintf(&b, "%dD", codecMagnitude(int64(v.days)))
	}
	n := codecMagnitude(v.duration)
	if n != 0 || (v.months == 0 && v.days == 0) {
		b.WriteByte('T')
		seconds := n / 1e9
		fraction := n % 1e9
		if hours := seconds / 3600; hours != 0 {
			fmt.Fprintf(&b, "%dH", hours)
		}
		if minutes := seconds / 60 % 60; minutes != 0 {
			fmt.Fprintf(&b, "%dM", minutes)
		}
		if s := seconds % 60; s != 0 || fraction != 0 || n == 0 {
			fmt.Fprintf(&b, "%d", s)
			if fraction != 0 {
				b.WriteByte('.')
				b.WriteString(strings.TrimRight(fmt.Sprintf("%09d", fraction), "0"))
			}
			b.WriteByte('S')
		}
	}
	return b.String()
}

func codecCorpus() []codecCase {
	var out []codecCase
	good := func(kind, text, canonical string, v codecValue) {
		out = append(out, codecCase{kind: kind, text: text, canonical: canonical, value: v})
	}
	bad := func(kind string, code int, texts ...string) {
		for _, s := range texts {
			out = append(out, codecCase{kind: kind, text: s, err: code})
		}
	}
	rng := rand.New(rand.NewSource(86013339))
	dates := []time.Time{}
	for _, s := range []string{"0000-01-01", "0000-02-29", "0001-01-01", "1582-10-15", "1900-02-28", "2000-02-29", "2019-12-30", "2021-01-03", "2024-02-29", "9999-12-31"} {
		d, e := time.Parse("2006-01-02", s)
		if e != nil {
			panic(e)
		}
		dates = append(dates, d)
	}
	for i := 0; i < 12; i++ {
		dates = append(dates, time.Date(rng.Intn(10000), time.Month(rng.Intn(12)+1), rng.Intn(28)+1, 0, 0, 0, 0, time.UTC))
	}
	for _, d := range dates {
		v := codecCivil(d)
		canon := d.Format("2006-01-02")
		for _, s := range []string{canon, d.Format("20060102"), fmt.Sprintf("%04d-%03d", d.Year(), d.YearDay()), fmt.Sprintf("%04d%03d", d.Year(), d.YearDay())} {
			good("iso_date", s, canon, v)
		}
		wy, w := d.ISOWeek()
		wd := int(d.Weekday())
		if wd == 0 {
			wd = 7
		}
		if wy >= 0 && wy <= 9999 {
			good("iso_date", fmt.Sprintf("%04d-W%02d-%d", wy, w, wd), canon, v)
			good("iso_date", fmt.Sprintf("%04dW%02d%d", wy, w, wd), canon, v)
		}
	}
	// Each supported fractional width, zero trimming, comma ISO fractions, and
	// every zero-offset metadata spelling. Go is used only within its shared profile.
	fractions := []string{"", ".0", ".000000000", ".1", ".12", ".123", ".1234", ".12345", ".123456", ".1234567", ".12345678", ".123456789", ".120000000"}
	for _, f := range fractions {
		d, e := time.Parse("2006-01-02T15:04:05.999999999", "2024-02-29T23:59:59"+f)
		if e != nil {
			panic(e)
		}
		v := codecCivil(d)
		clock := d.Format("15:04:05.999999999")
		dt := d.Format("2006-01-02T15:04:05.999999999")
		good("iso_time", "23:59:59"+f, clock, v)
		good("iso_datetime", "2024-02-29T23:59:59"+f, dt, v)
		if f != "" {
			good("iso_time", "23:59:59"+strings.ReplaceAll(f, ".", ","), clock, v)
			good("iso_datetime", "2024-02-29T23:59:59"+strings.ReplaceAll(f, ".", ","), dt, v)
		}
		for _, z := range []struct {
			s    string
			off  int32
			kind int
		}{{"Z", 0, 0}, {"z", 0, 0}, {"+00:00", 0, 1}, {"-00:00", 0, 2}, {"+23:59", 1439, 1}, {"-05:30", -330, 1}} {
			zv := v
			zv.off = z.off
			zv.kind = z.kind
			suffix := z.s
			if suffix == "z" {
				suffix = "Z"
			}
			good("rfc3339_datetime", "2024-02-29t23:59:59"+f+z.s, dt+suffix, zv)
		}
	}
	for _, s := range []string{"0000-01-01T00:00:00Z", "9999-12-31T23:59:59.999999999Z"} {
		d, e := time.Parse(time.RFC3339Nano, s)
		if e != nil {
			panic(e)
		}
		good("rfc3339_datetime", s, s, codecCivil(d))
		good("iso_datetime", strings.TrimSuffix(s, "Z"), strings.TrimSuffix(s, "Z"), codecCivil(d))
	}
	periods := []struct {
		s    string
		m, d int32
		ns   int64
	}{
		{"P1Y2M3DT4H5M6.000000007S", 14, 3, 14706000000007}, {"P2W", 0, 14, 0}, {"P1D", 0, 1, 0}, {"P0D", 0, 0, 0}, {"-P1M2D", -1, -2, 0}, {"+PT0,5S", 0, 0, 500000000}, {"PT24H", 0, 0, 86400000000000},
		{"P2147483647M2147483647D", math.MaxInt32, math.MaxInt32, 0}, {"-P2147483648M2147483648D", math.MinInt32, math.MinInt32, 0},
		{"PT9223372036.854775807S", 0, 0, math.MaxInt64}, {"-PT9223372036.854775808S", 0, 0, math.MinInt64}, {"PT60M", 0, 0, 3600000000000}, {"PT60S", 0, 0, 60000000000}, {"-PT0S", 0, 0, 0},
	}
	for _, p := range periods {
		v := codecValue{months: p.m, days: p.d, duration: p.ns}
		good("iso_period", p.s, codecPeriodText(v), v)
		if strings.HasPrefix(strings.TrimLeft(p.s, "+-"), "PT") {
			good("iso_duration", p.s, codecPeriodText(v), v)
		}
	}
	for _, n := range []int64{math.MinInt64, math.MaxInt64, -1, 0, 1, 1000, 1000000, 1000000000} {
		v := codecValue{duration: n}
		s := codecPeriodText(v)
		good("iso_duration", s, s, v)
	}
	for i := 0; i < 24; i++ {
		v := codecValue{duration: int64(rng.Uint64())}
		s := codecPeriodText(v)
		good("iso_duration", s, s, v)
		v.months = int32(rng.Int31())
		v.days = int32(rng.Int31())
		if v.duration < 0 {
			v.months = -v.months
			v.days = -v.days
		}
		s = codecPeriodText(v)
		good("iso_period", s, s, v)
	}
	bad("iso_date", 3, "", "2024", "2024-2-29", "2024-02-2", "2024/02/29", "+2024-02-29", "2024-w01-1", "2024-01-01Z", "20240101x", "２０２４-01-01", "2024-01-0\x00")
	bad("iso_date", 2, "1900-02-29", "2024-02-30", "2024-00-01", "2024-13-01", "2024-01-00", "2024-000", "2023-366", "2024-367", "2021-W53-1", "2024-W00-1", "2024-W01-0", "2024-W01-8")
	bad("iso_time", 3, "", "12:34", "1:34:56", "12-34-56", "123456", "12:34:56.", "12:34:56.1234567890", "12:34:56Z", "12:34:56.1x", "12:34:56.\x00", " 12:34:56")
	bad("iso_time", 2, "24:00:00", "23:60:00", "23:59:60", "99:99:99")
	bad("iso_datetime", 3, "2024-01-01t12:34:56", "2024-01-01 12:34:56", "20240101T12:34:56", "2024-001T12:34:56", "2024-01-01T12:34:56Z")
	bad("iso_datetime", 2, "2023-02-29T12:34:56", "2024-01-01T24:00:00")
	bad("rfc3339_datetime", 3, "2024-01-01T12:34:56", "2024-01-01 12:34:56Z", "2024-01-01T12:34:56,1Z", "2024-01-01T12:34:56.Z", "2024-01-01T12:34:56.1234567890Z", "2024-01-01T12:34:56ZZ", "2024-01-01T12:34:56Z\x00", "2024-01-01T12:34:56Z[UTC]")
	bad("rfc3339_datetime", 2, "2023-02-29T12:34:56Z", "2024-01-01T24:00:00Z", "2024-01-01T23:59:60Z")
	bad("rfc3339_datetime", 4, "2024-01-01T12:34:56+24:00", "2024-01-01T12:34:56-00:60", "2024-01-01T12:34:56+0000", "2024-01-01T12:34:56+0a:00", "2024-01-01T12:34:56+00:00x")
	for _, k := range []string{"iso_period", "iso_duration"} {
		bad(k, 5, "", "P", "PT", "P1DT", "PT1ST", "P1W1D", "P1D1W", "P1WT1H", "P1M1Y", "PT1S1M", "PT1M1M", "P1.5D", "PT1.5H", "PT.5S", "PT1.S", "PT1.0000000000S", "P-1D", "P1H", "P1Q", "pt1s", " PT1S", "PT1Sx", "PT1S\x00")
		bad(k, 1, "PT9223372036.854775808S", "-PT9223372036.854775809S", "PT18446744073709551616S")
	}
	bad("iso_period", 1, "P2147483648M", "P2147483648D", "P178956971Y", "P306783379W")
	bad("iso_duration", 5, "P1D", "P0D", "P1M", "P1W", "P1DT1H")
	return out
}
func codecCapacityCases() []codecCase {
	v := codecCivil(time.Date(9999, 12, 31, 23, 59, 59, 999999999, time.UTC))
	v.off = 1439
	v.kind = 1
	p := codecValue{months: math.MinInt32, days: math.MinInt32, duration: math.MinInt64}
	d := codecValue{duration: math.MinInt64}
	return []codecCase{
		{kind: "iso_date", value: v, canonical: "9999-12-31"},
		{kind: "iso_time", value: v, canonical: "23:59:59.999999999"},
		{kind: "iso_datetime", value: v, canonical: "9999-12-31T23:59:59.999999999"},
		{kind: "rfc3339_datetime", value: v, canonical: "9999-12-31T23:59:59.999999999+23:59"},
		{kind: "iso_period", value: p, canonical: codecPeriodText(p)},
		{kind: "iso_duration", value: d, canonical: codecPeriodText(d)},
	}
}
func codecInvalidValues() []codecCase {
	valid := codecCivil(time.Date(2024, 2, 29, 12, 34, 56, 0, time.UTC))
	var out []codecCase
	for _, y := range []int32{-1, 10000, math.MinInt32, math.MaxInt32} {
		v := valid
		v.y = y
		out = append(out, codecCase{kind: "iso_date", value: v, err: 2})
	}
	for _, ns := range []uint32{1000000000, math.MaxUint32} {
		v := valid
		v.ns = ns
		out = append(out, codecCase{kind: "iso_time", value: v, err: 2})
	}
	v := valid
	v.h = 24
	out = append(out, codecCase{kind: "iso_datetime", value: v, err: 2}, codecCase{kind: "rfc3339_datetime", value: v, err: 2})
	for _, off := range []int32{-1440, 1440, math.MinInt32, math.MaxInt32} {
		v := valid
		v.off = off
		v.kind = 1
		out = append(out, codecCase{kind: "rfc3339_datetime", value: v, err: 4})
	}
	for _, kind := range []int{0, 2} {
		v := valid
		v.off = 1
		v.kind = kind
		out = append(out, codecCase{kind: "rfc3339_datetime", value: v, err: 4})
	}
	for _, v := range []codecValue{{months: 1, days: -1}, {months: -1, duration: 1}, {days: 1, duration: -1}} {
		out = append(out, codecCase{kind: "iso_period", value: v, err: 5})
	}
	return out
}
