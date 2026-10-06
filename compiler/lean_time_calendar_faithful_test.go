package compiler

import (
	"fmt"
	"math"
	"math/big"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// One corpus, one independent Go oracle, three execution paths. All fields and
// error constructors are compared; a pair of mutually inverse bugs cannot pass
// by merely round-tripping. The full-domain Lean certificates are separate.
func TestLeanTimeCalendarFaithful(t *testing.T) {
	skipInShort(t)
	lake := findLake()
	if lake == "" {
		if os.Getenv("OAK_REQUIRE_TIME_LEAN") == "1" {
			t.Fatal("OAK_REQUIRE_TIME_LEAN=1 but lake was not found")
		}
		t.Skip("calendar correspondence requires lake")
	}
	cases := calendarCorpus()
	b := &timeChecks{prelude: timeISOTestPrelude + `
calendar_epoch_is: (r: Result[i64, time.TimeError], want: i64): Bool {
 r ? | .Err(e) => false | .Ok(v) => v == want
}
calendar_epoch_code: (r: Result[i64, time.TimeError]): u32 {
 r ? | .Err(e) => err_code(e) | .Ok(v) => u32(0)
}
`}
	var lean strings.Builder
	lean.WriteString("import Oak.Stdlib.TimeCalendarExtracted\nopen Oak.Stdlib.Time\nset_option maxRecDepth 65536\nset_option maxHeartbeats 4000000\n")
	for i, c := range cases {
		if i%timeChunk == 0 {
			fmt.Fprintf(&lean, "def check%d : IO Unit := do\n", i/timeChunk)
		}
		oakCall, leanCall := c.calls()
		want := c.oracle()
		var oakCheck, leanWant string
		if want.err != 0 {
			helper := "iso_date_code"
			if c.op == "epoch" {
				helper = "calendar_epoch_code"
			}
			oakCheck = fmt.Sprintf("%s(%s) == u32(%d)", helper, oakCall, want.err)
			errName := "InvalidCivil"
			if want.err == 1 {
				errName = "Overflowed"
			}
			leanWant = "some (.Err ." + errName + ")"
		} else if c.op == "epoch" {
			oakCheck = fmt.Sprintf("calendar_epoch_is(%s,%s)", oakCall, oakI64(want.days))
			leanWant = fmt.Sprintf("some (.Ok (%d))", want.days)
		} else {
			oakCheck = fmt.Sprintf("iso_date_is(%s,i32(%d),u8(%d),u8(%d))", oakCall, want.y, want.m, want.d)
			leanWant = fmt.Sprintf("some (.Ok ⟨%d, %d, %d⟩)", want.y, want.m, want.d)
		}
		b.check(oakCheck)
		fmt.Fprintf(&lean, "  unless %s == %s do\n    throw (IO.userError \"calendar case %d: %s\")\n", leanCall, leanWant, i, c.op)
	}
	lean.WriteString("def main : IO Unit := do\n")
	for n := 0; n < b.chunks(); n++ {
		fmt.Fprintf(&lean, "  check%d\n", n)
	}
	fmt.Fprintf(&lean, "  IO.println \"calendar: %d cases passed\"\n", len(cases))
	t.Run("compiled_and_interpreted", func(t *testing.T) { runTimeChecks(t, "calendarfaithful", b) })
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
		driver := filepath.Join(t.TempDir(), "calendar.lean")
		if err := os.WriteFile(driver, []byte(lean.String()), 0o644); err != nil {
			t.Fatal(err)
		}
		run := exec.Command(lake, "env", "lean", "--run", driver)
		run.Dir = root
		out, err := run.CombinedOutput()
		if err != nil {
			t.Fatalf("Lean calendar corpus: %v\n%s", err, out)
		}
		if want := fmt.Sprintf("calendar: %d cases passed\n", len(cases)); string(out) != want {
			t.Fatalf("unexpected Lean result: %q (want %q)", out, want)
		}
	})
	if !t.Failed() {
		t.Logf("%d shared calendar cases passed in the selected execution paths", len(cases))
	}
}

type calendarCase struct {
	op    string
	y     int32
	m, d  uint8
	delta int64
	clamp bool
}

type calendarWant struct {
	y    int
	m, d int
	days int64
	err  int // TimeError codes: Overflowed=1, InvalidCivil=2
}

func (c calendarCase) calls() (string, string) {
	oakDate := fmt.Sprintf("date_value(%s,u8(%d),u8(%d))", oakI32(c.y), c.m, c.d)
	leanDate := fmt.Sprintf("(⟨%d, %d, %d⟩ : Date)", c.y, c.m, c.d)
	switch c.op {
	case "from":
		return fmt.Sprintf("time.date_from_epoch_days(%s)", oakI64(c.delta)), fmt.Sprintf("(date_from_epoch_days (%d) 0)", c.delta)
	case "epoch":
		return "time.date_epoch_days(" + oakDate + ")", "(date_epoch_days " + leanDate + " 0)"
	case "days":
		return fmt.Sprintf("time.date_add_days(%s,%s)", oakDate, oakI64(c.delta)), fmt.Sprintf("(date_add_days %s (%d) 0)", leanDate, c.delta)
	case "months":
		policy := "Reject"
		if c.clamp {
			policy = "Clamp"
		}
		return fmt.Sprintf("time.date_add_months(%s,%s,.%s)", oakDate, oakI32(int32(c.delta)), policy), fmt.Sprintf("(date_add_months %s (%d) .%s 0)", leanDate, c.delta, policy)
	default:
		panic("unknown calendar corpus operation: " + c.op)
	}
}

func (c calendarCase) oracle() calendarWant {
	date := time.Date(int(c.y), time.Month(c.m), int(c.d), 0, 0, 0, 0, time.UTC)
	if c.op != "from" && (c.y < 0 || c.y > 9999 || date.Year() != int(c.y) || date.Month() != time.Month(c.m) || date.Day() != int(c.d)) {
		return calendarWant{err: 2}
	}
	switch c.op {
	case "from", "days":
		target := big.NewInt(c.delta)
		if c.op == "days" {
			target.Add(target, big.NewInt(date.Unix()/86400))
		}
		if target.Cmp(big.NewInt(-719528)) < 0 || target.Cmp(big.NewInt(2932896)) > 0 {
			return calendarWant{err: 1}
		}
		date = time.Unix(target.Int64()*86400, 0).UTC()
	case "months":
		index := int64(c.y)*12 + int64(c.m) - 1 + c.delta
		if index < 0 || index >= 120000 {
			return calendarWant{err: 1}
		}
		y, m := int(index/12), time.Month(index%12+1)
		last := time.Date(y, m+1, 0, 0, 0, 0, 0, time.UTC).Day()
		d := int(c.d)
		if d > last {
			if !c.clamp {
				return calendarWant{err: 2}
			}
			d = last
		}
		date = time.Date(y, m, d, 0, 0, 0, 0, time.UTC)
	}
	return calendarWant{y: date.Year(), m: int(date.Month()), d: date.Day(), days: date.Unix() / 86400}
}

func calendarCorpus() []calendarCase {
	var cases []calendarCase
	for _, days := range []int64{math.MinInt64, math.MinInt64 + 1, -719529, -719528, -719527, -719469, -719468, -1, 0, 1, 2932895, 2932896, 2932897, math.MaxInt64 - 1, math.MaxInt64} {
		cases = append(cases, calendarCase{op: "from", delta: days})
	}
	// Year zero, Gregorian century exceptions, leap-day and year-end boundaries.
	for _, y := range []int32{0, 1, 100, 400, 1582, 1600, 1900, 1969, 1970, 2000, 2024, 2100, 9999} {
		for _, md := range [][2]uint8{{1, 1}, {2, 28}, {2, 29}, {3, 1}, {12, 31}} {
			cases = append(cases, calendarCase{op: "epoch", y: y, m: md[0], d: md[1]})
			for _, delta := range []int64{-1, 1} {
				cases = append(cases, calendarCase{op: "days", y: y, m: md[0], d: md[1], delta: delta})
			}
		}
	}
	for _, d := range []calendarCase{{y: 0, m: 1, d: 1}, {y: 9999, m: 12, d: 31}, {y: 2000, m: 2, d: 29}} {
		base := d.oracle().days
		for _, delta := range []int64{math.MinInt64, math.MaxInt64, -719529 - base, -719528 - base, 2932896 - base, 2932897 - base, 0} {
			d.op, d.delta = "days", delta
			cases = append(cases, d)
		}
	}
	// Both policies, every month, all potentially truncated days, in each leap class.
	for _, y := range []int32{0, 1900, 2000, 2023} {
		for m := uint8(1); m <= 12; m++ {
			for _, delta := range []int64{-1, 1} {
				for _, clamp := range []bool{false, true} {
					for day := uint8(28); day <= 31; day++ {
						cases = append(cases, calendarCase{op: "months", y: y, m: m, d: day, delta: delta, clamp: clamp})
					}
				}
			}
		}
	}
	for _, d := range []calendarCase{{y: -1, m: 1, d: 1}, {y: 10000, m: 1, d: 1}, {y: math.MinInt32, m: 1, d: 1}, {y: math.MaxInt32, m: 1, d: 1}, {y: 2024, m: 0, d: 1}, {y: 2024, m: 13, d: 1}, {y: 2024, m: 255, d: 1}, {y: 2024, m: 1, d: 0}, {y: 2024, m: 1, d: 255}} {
		for _, op := range []string{"epoch", "days", "months"} {
			d.op, d.delta = op, math.MaxInt32
			cases = append(cases, d)
		}
	}
	for _, y := range []int32{0, 9999, 2024} {
		for _, delta := range []int64{math.MinInt32, math.MaxInt32, -120000, -1, 0, 1, 120000} {
			for _, clamp := range []bool{false, true} {
				cases = append(cases, calendarCase{op: "months", y: y, m: 1, d: 31, delta: delta, clamp: clamp})
			}
		}
	}
	rng := rand.New(rand.NewSource(86013339))
	for i := 0; i < 100; i++ {
		d := calendarCase{y: int32(rng.Intn(10000)), m: uint8(1 + rng.Intn(12)), d: uint8(1 + rng.Intn(31))}
		d.op = "epoch"
		cases = append(cases, d)
		d.op, d.delta = "from", rng.Int63n(3652425)-719528
		cases = append(cases, d)
		d.op, d.delta = "days", int64(rng.Intn(7304851))-3652425
		cases = append(cases, d)
		d.op, d.delta, d.clamp = "months", int64(rng.Int31()), i%2 == 0
		if i%3 == 0 {
			d.delta = -d.delta
		}
		cases = append(cases, d)
	}
	return cases
}
