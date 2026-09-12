package compiler

import (
	"fmt"
	"math/rand"
	"os"
	"strconv"
	"strings"
	"testing"
)

// Generated-program differential witness: seeded, type-directed random Oak
// programs — fixed-width wrapping arithmetic on u8/u32/u64/i32 locals,
// comparison-driven value and statement conditionals, counted loops with a
// dedicated counter, owned arrays with constant in-bounds indices, a record
// with field reads and writes — run through the compiled C and the
// interpreter, and the exit codes must agree. Agreement is the oracle. A
// divergence prints the seed and the whole program for reproduction.
//
// OAK_FUZZ_PROGRAMS scales the run (default 24); OAK_FUZZ_SEED offsets the
// seeds so a longer campaign explores new programs.

type fuzzType string

const (
	tU8  fuzzType = "u8"
	tU32 fuzzType = "u32"
	tU64 fuzzType = "u64"
	tI32 fuzzType = "i32"
)

var fuzzTypes = []fuzzType{tU8, tU32, tU64, tI32}

func (t fuzzType) unsigned() bool { return t != tI32 }
func (t fuzzType) width() int {
	switch t {
	case tU8:
		return 8
	case tU64:
		return 64
	}
	return 32
}

type fuzzVar struct {
	name string
	typ  fuzzType
}

type fuzzGen struct {
	r        *rand.Rand
	vars     []fuzzVar // scalar locals in scope
	arrays   []fuzzVar // owned arrays of 4 elements, typed by element
	records  []string  // locals of the record type P (fields a, b: u32)
	counters map[string]bool
	next     int
	out      strings.Builder
}

func (g *fuzzGen) fresh(prefix string) string {
	g.next++
	return fmt.Sprintf("%s%d", prefix, g.next)
}

func (g *fuzzGen) line(indent int, format string, args ...interface{}) {
	g.out.WriteString(strings.Repeat("  ", indent))
	g.out.WriteString(fmt.Sprintf(format, args...))
	g.out.WriteString("\n")
}

func (g *fuzzGen) pick(vars []fuzzVar, typ fuzzType) (fuzzVar, bool) {
	var of []fuzzVar
	for _, v := range vars {
		if v.typ == typ && !g.counters[v.name] {
			of = append(of, v)
		}
	}
	if len(of) == 0 {
		return fuzzVar{}, false
	}
	return of[g.r.Intn(len(of))], true
}

// literal is a typed constant; signed values may be negative through a
// subtraction from zero (Oak literals are non-negative).
func (g *fuzzGen) literal(typ fuzzType) string {
	var v int64
	switch g.r.Intn(4) {
	case 0:
		v = int64(g.r.Intn(4))
	case 1:
		v = int64(g.r.Intn(300))
	case 2:
		v = int64(g.r.Intn(1 << 16))
	default:
		v = int64(g.r.Int31())
	}
	if typ == tU8 {
		v %= 256
	}
	if typ == tI32 && g.r.Intn(3) == 0 {
		return fmt.Sprintf("(i32(0) - i32(%d))", v)
	}
	return fmt.Sprintf("%s(%d)", typ, v)
}

// expr is a well-typed expression of typ with bounded depth.
func (g *fuzzGen) expr(typ fuzzType, depth int) string {
	if depth <= 0 || g.r.Intn(4) == 0 {
		if v, ok := g.pick(g.vars, typ); ok && g.r.Intn(3) != 0 {
			return v.name
		}
		if typ == tU32 && len(g.arrays) > 0 && g.r.Intn(4) == 0 {
			arr := g.arrays[g.r.Intn(len(g.arrays))]
			if arr.typ == tU32 {
				return fmt.Sprintf("%s[%d]", arr.name, g.r.Intn(4))
			}
		}
		if typ == tU32 && len(g.records) > 0 && g.r.Intn(4) == 0 {
			return fmt.Sprintf("%s.%s", g.records[g.r.Intn(len(g.records))], []string{"a", "b"}[g.r.Intn(2)])
		}
		return g.literal(typ)
	}
	switch g.r.Intn(10) {
	case 0, 1, 2:
		op := []string{"+", "-", "*"}[g.r.Intn(3)]
		return fmt.Sprintf("(%s %s %s)", g.expr(typ, depth-1), op, g.expr(typ, depth-1))
	case 3, 4:
		if !typ.unsigned() {
			return fmt.Sprintf("(%s - %s)", g.expr(typ, depth-1), g.expr(typ, depth-1))
		}
		op := []string{"&", "|", "^"}[g.r.Intn(3)]
		return fmt.Sprintf("(%s %s %s)", g.expr(typ, depth-1), op, g.expr(typ, depth-1))
	case 5:
		if !typ.unsigned() {
			return fmt.Sprintf("(%s + %s)", g.expr(typ, depth-1), g.literal(typ))
		}
		// Shift counts are constants below the width: total on both sides.
		op := []string{"<<", ">>"}[g.r.Intn(2)]
		return fmt.Sprintf("(%s %s %s(%d))", g.expr(typ, depth-1), op, typ, g.r.Intn(typ.width()))
	case 6, 7:
		// A value-position conditional; both arms parenthesized so the arm
		// separator is unambiguous.
		return fmt.Sprintf("(%s ? (%s) | (%s))", g.condition(depth-1), g.expr(typ, depth-1), g.expr(typ, depth-1))
	case 8:
		// A conversion from another width or signedness.
		switch typ {
		case tU32:
			switch g.r.Intn(3) {
			case 0:
				return fmt.Sprintf("u32(%s)", g.expr(tU8, depth-1))
			case 1:
				return fmt.Sprintf("u32_trunc_u64(%s)", g.expr(tU64, depth-1))
			default:
				return fmt.Sprintf("u32_bits_i32(%s)", g.expr(tI32, depth-1))
			}
		case tU64:
			return fmt.Sprintf("u64(%s)", g.expr(tU32, depth-1))
		case tI32:
			return fmt.Sprintf("i32_bits_u32(%s)", g.expr(tU32, depth-1))
		case tU8:
			return fmt.Sprintf("u8_trunc_u32(%s)", g.expr(tU32, depth-1))
		}
	}
	return g.literal(typ)
}

// condition is a Bool expression: a comparison, or comparisons joined.
func (g *fuzzGen) condition(depth int) string {
	typ := fuzzTypes[g.r.Intn(len(fuzzTypes))]
	cmp := []string{"<", "<=", ">", ">=", "==", "!="}[g.r.Intn(6)]
	c := fmt.Sprintf("%s %s %s", g.expr(typ, depth), cmp, g.expr(typ, depth))
	if depth > 0 && g.r.Intn(4) == 0 {
		return fmt.Sprintf("(%s) %s (%s)", c, []string{"&&", "||"}[g.r.Intn(2)], g.condition(depth-1))
	}
	return c
}

// statementCondition is a condition whose first token is a variable.
func (g *fuzzGen) statementCondition() string {
	typ := fuzzTypes[g.r.Intn(len(fuzzTypes))]
	v, ok := g.pick(g.vars, typ)
	if !ok {
		v = g.vars[0]
		typ = v.typ
	}
	cmp := []string{"<", "<=", ">", ">=", "==", "!="}[g.r.Intn(6)]
	c := fmt.Sprintf("%s %s %s", v.name, cmp, g.expr(typ, 2))
	if g.r.Intn(3) == 0 {
		return fmt.Sprintf("%s %s (%s)", c, []string{"&&", "||"}[g.r.Intn(2)], g.condition(1))
	}
	return c
}

// statement emits one statement at the given indent; loops may nest once.
func (g *fuzzGen) statement(indent int, inLoop bool) {
	switch g.r.Intn(10) {
	case 0, 1:
		typ := fuzzTypes[g.r.Intn(len(fuzzTypes))]
		name := g.fresh("v")
		g.line(indent, "%s: %s = %s", name, typ, g.expr(typ, 3))
		if !inLoop {
			g.vars = append(g.vars, fuzzVar{name, typ})
		}
	case 2, 3, 4:
		typ := fuzzTypes[g.r.Intn(len(fuzzTypes))]
		if v, ok := g.pick(g.vars, typ); ok {
			g.line(indent, "%s = %s", v.name, g.expr(typ, 3))
		}
	case 5:
		if len(g.arrays) > 0 {
			arr := g.arrays[g.r.Intn(len(g.arrays))]
			g.line(indent, "%s[%d] = %s", arr.name, g.r.Intn(4), g.expr(arr.typ, 2))
		}
	case 6:
		if len(g.records) > 0 {
			g.line(indent, "%s.%s = %s", g.records[g.r.Intn(len(g.records))], []string{"a", "b"}[g.r.Intn(2)], g.expr(tU32, 2))
		}
	case 7:
		// A statement-level conditional with an assignment in each arm. The
		// condition starts with a variable, never `(`: a line opening with a
		// parenthesis continues the previous statement as a call.
		typ := fuzzTypes[g.r.Intn(len(fuzzTypes))]
		if v, ok := g.pick(g.vars, typ); ok {
			w, _ := g.pick(g.vars, typ)
			g.line(indent, "%s ? { %s = %s } | { %s = %s }", g.statementCondition(), v.name, g.expr(typ, 2), w.name, g.expr(typ, 2))
		}
	case 8, 9:
		if inLoop {
			return
		}
		// A counted loop over its own counter, never assigned in the body.
		counter := g.fresh("i")
		g.counters[counter] = true
		g.vars = append(g.vars, fuzzVar{counter, tU32})
		g.line(indent, "%s: u32 = u32(0)", counter)
		g.line(indent, "while %s < u32(%d) {", counter, 1+g.r.Intn(6))
		for n := 1 + g.r.Intn(3); n > 0; n-- {
			g.statement(indent+1, true)
		}
		g.line(indent+1, "%s = %s + u32(1)", counter, counter)
		g.line(indent, "}")
	}
}

// program generates one complete program whose main returns a 7-bit digest
// of every scalar local.
func fuzzProgram(seed int64) string {
	g := &fuzzGen{r: rand.New(rand.NewSource(seed)), counters: map[string]bool{}}
	g.line(0, "P: type = struct {")
	g.line(1, "a: u32")
	g.line(1, "b: u32")
	g.line(0, "}")
	g.line(0, "")
	g.line(0, "main: (): i32 {")
	for _, typ := range fuzzTypes {
		name := g.fresh("v")
		g.line(1, "%s: %s = %s", name, typ, g.literal(typ))
		g.vars = append(g.vars, fuzzVar{name, typ})
	}
	g.line(1, "arr: [4]u32")
	g.arrays = append(g.arrays, fuzzVar{"arr", tU32})
	g.line(1, "p: P = P { a: %s, b: %s }", g.expr(tU32, 1), g.expr(tU32, 1))
	g.records = append(g.records, "p")
	for n := 4 + g.r.Intn(8); n > 0; n-- {
		g.statement(1, false)
	}
	// The digest: every scalar folded into a u32, masked to the exit range.
	parts := []string{"p.a", "p.b", "arr[0]", "arr[1]", "arr[2]", "arr[3]"}
	for _, v := range g.vars {
		switch v.typ {
		case tU32:
			parts = append(parts, v.name)
		case tU8:
			parts = append(parts, "u32("+v.name+")")
		case tU64:
			parts = append(parts, "u32_trunc_u64("+v.name+")")
		case tI32:
			parts = append(parts, "u32_bits_i32("+v.name+")")
		}
	}
	g.line(1, "digest: u32 = %s", strings.Join(parts, " ^ "))
	g.line(1, "i32_bits_u32((digest ^ (digest >> u32(16)) ^ (digest >> u32(8))) & u32(0x7F))")
	g.line(0, "}")
	return g.out.String()
}

func TestDifferentialGeneratedPrograms(t *testing.T) {
	skipInShort(t)
	count := 24
	if env := os.Getenv("OAK_FUZZ_PROGRAMS"); env != "" {
		if n, err := strconv.Atoi(env); err == nil && n > 0 {
			count = n
		}
	}
	base := int64(1)
	if env := os.Getenv("OAK_FUZZ_SEED"); env != "" {
		if n, err := strconv.ParseInt(env, 10, 64); err == nil {
			base = n
		}
	}
	for i := 0; i < count; i++ {
		seed := base + int64(i)
		src := fuzzProgram(seed)
		t.Run(fmt.Sprintf("seed_%d", seed), func(t *testing.T) {
			if _, err := New().WithSource("fuzz.oak", src).Check().Get(); err != nil {
				t.Fatalf("generated program does not typecheck (generator bug):\n%v\n--- program (seed %d) ---\n%s", err, seed, src)
			}
			code, abnormal := buildAndRun(t, fmt.Sprintf("fuzz_%d", seed), src)
			if abnormal {
				t.Fatalf("compiled program exited abnormally (code %d)\n--- program (seed %d) ---\n%s", code, seed, src)
			}
			got := interpretChecked(t, src)
			if int(got&0xFF) != code&0xFF {
				t.Fatalf("interpreter %d, compiled exit %d\n--- program (seed %d) ---\n%s", got, code, seed, src)
			}
		})
	}
}
