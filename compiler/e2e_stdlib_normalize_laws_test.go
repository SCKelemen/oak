package compiler

import (
	"encoding/json"
	"fmt"
	"math/rand"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"testing"
	"unicode/utf8"
)

// normalizeOracle is an independent Go transliteration of the UAX #15
// definitions over the same extract the Oak tables come from
// (stdlib/unicode17_normalize.json): full decomposition (D68/D65 with the
// Hangul algorithm), canonical ordering (D109, a stable sort of each run of
// non-starters by ccc), and canonical composition (D117 with the blocking
// rule and Hangul composition). It is the relation the Lean model states
// (spec/lean/Oak/Normalization.lean); the compiled Oak must agree with it on
// every generated sequence.
type normalizeOracle struct {
	ccc   map[rune]int
	nfd   map[rune][]rune
	nfkd  map[rune][]rune
	pairs map[[2]rune]rune
}

func loadNormalizeOracle(t *testing.T) *normalizeOracle {
	path := filepath.Join("..", "stdlib", "unicode17_normalize.json")
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	var raw struct {
		Version string   `json:"version"`
		Props   [][3]int `json:"props"`
		NFD     [][3]int `json:"nfd"`
		NFKD    [][3]int `json:"nfkd"`
		Pairs   [][3]int `json:"pairs"`
		Pool    []int    `json:"pool"`
	}
	if err := json.Unmarshal(data, &raw); err != nil {
		t.Fatal(err)
	}
	if raw.Version != "17.0.0" {
		t.Fatalf("extract version %q", raw.Version)
	}
	o := &normalizeOracle{ccc: map[rune]int{}, nfd: map[rune][]rune{}, nfkd: map[rune][]rune{}, pairs: map[[2]rune]rune{}}
	for _, r := range raw.Props {
		if c := r[2] & 255; c != 0 {
			for cp := r[0]; cp <= r[1]; cp++ {
				o.ccc[rune(cp)] = c
			}
		}
	}
	seq := func(off, n int) []rune {
		out := make([]rune, n)
		for i := 0; i < n; i++ {
			out[i] = rune(raw.Pool[off+i])
		}
		return out
	}
	for _, e := range raw.NFD {
		o.nfd[rune(e[0])] = seq(e[1], e[2])
	}
	for _, e := range raw.NFKD {
		o.nfkd[rune(e[0])] = seq(e[1], e[2])
	}
	for _, p := range raw.Pairs {
		o.pairs[[2]rune{rune(p[0]), rune(p[1])}] = rune(p[2])
	}
	return o
}

const (
	hangulSBase, hangulLBase, hangulVBase, hangulTBase = 0xAC00, 0x1100, 0x1161, 0x11A7
	hangulLCount, hangulVCount, hangulTCount           = 19, 21, 28
	hangulNCount                                       = hangulVCount * hangulTCount
	hangulSCount                                       = hangulLCount * hangulNCount
)

func (o *normalizeOracle) decompose(r rune, compat bool) []rune {
	if r >= hangulSBase && r < hangulSBase+hangulSCount {
		index := int(r - hangulSBase)
		out := []rune{hangulLBase + rune(index/hangulNCount), hangulVBase + rune((index%hangulNCount)/hangulTCount)}
		if index%hangulTCount != 0 {
			out = append(out, hangulTBase+rune(index%hangulTCount))
		}
		return out
	}
	if compat {
		if d, ok := o.nfkd[r]; ok {
			return d
		}
	}
	if d, ok := o.nfd[r]; ok {
		return d
	}
	return []rune{r}
}

func (o *normalizeOracle) composePair(a, b rune) (rune, bool) {
	if a >= hangulLBase && a < hangulLBase+hangulLCount && b >= hangulVBase && b < hangulVBase+hangulVCount {
		return hangulSBase + ((a-hangulLBase)*hangulVCount+(b-hangulVBase))*hangulTCount, true
	}
	if a >= hangulSBase && a < hangulSBase+hangulSCount && (a-hangulSBase)%hangulTCount == 0 && b > hangulTBase && b < hangulTBase+hangulTCount {
		return a + (b - hangulTBase), true
	}
	c, ok := o.pairs[[2]rune{a, b}]
	return c, ok
}

// normalize is the specification: decompose every scalar, stable-sort each
// maximal run of non-starters by ccc, then (for the composed forms) compose
// each unblocked character with the last starter.
func (o *normalizeOracle) normalize(text []rune, compat, compose bool) []rune {
	var d []rune
	for _, r := range text {
		d = append(d, o.decompose(r, compat)...)
	}
	for i := 0; i < len(d); {
		if o.ccc[d[i]] == 0 {
			i++
			continue
		}
		j := i
		for j < len(d) && o.ccc[d[j]] != 0 {
			j++
		}
		run := d[i:j]
		sort.SliceStable(run, func(a, b int) bool { return o.ccc[run[a]] < o.ccc[run[b]] })
		i = j
	}
	if !compose || len(d) == 0 {
		return d
	}
	out := []rune{}
	starter := -1
	lastClass := -1 // ccc of the last kept character after the starter; -1 when none
	for _, c := range d {
		cc := o.ccc[c]
		if starter >= 0 && (lastClass == -1 || lastClass < cc) {
			if composite, ok := o.composePair(out[starter], c); ok {
				out[starter] = composite
				continue
			}
		}
		out = append(out, c)
		if cc == 0 {
			starter = len(out) - 1
			lastClass = -1
		} else {
			lastClass = cc
		}
	}
	return out
}

// normalizeLawPool is the set of scalars the random sequences draw from:
// the classes normalization distinguishes.
func normalizeLawPool() []rune {
	var pool []rune
	add := func(lo, hi rune) {
		for r := lo; r <= hi; r++ {
			pool = append(pool, r)
		}
	}
	add(0x20, 0x7E)     // ASCII
	add(0xC0, 0xFF)     // Latin-1 letters with precomposed forms
	add(0x300, 0x34E)   // combining marks of several classes
	add(0x1100, 0x1112) // Hangul L
	add(0x1161, 0x1175) // Hangul V
	add(0x11A8, 0x11C2) // Hangul T
	add(0xAC00, 0xAC40) // Hangul syllables
	add(0x1E00, 0x1EFF) // Latin Extended Additional
	add(0x212A, 0x212B) // Kelvin and Angstrom singletons
	add(0xFB00, 0xFB06) // Latin ligatures (compatibility)
	add(0x0915, 0x0939) // Devanagari consonants
	add(0x093C, 0x093C) // nukta
	add(0x0958, 0x095F) // excluded composites
	add(0x3070, 0x3074) // Hiragana with dakuten (ccc 8 marks compose)
	add(0x3099, 0x309A)
	add(0x0F71, 0x0F73) // Tibetan vowel signs (ccc 129/130, excluded composite)
	add(0x1E9B, 0x1E9B) // long s with dot above: a compat-then-canonical chain
	return pool
}

// TestE2EStdlibNormalizeLaws compares the compiled normalizer with the Go
// oracle on random scalar sequences for all four forms.
func TestE2EStdlibNormalizeLaws(t *testing.T) {
	oracle := loadNormalizeOracle(t)
	pool := normalizeLawPool()
	rng := rand.New(rand.NewSource(20260912))
	const cases = 400
	var table []byte
	for i := 0; i < cases; i++ {
		n := rng.Intn(7)
		text := make([]rune, n)
		for k := range text {
			text[k] = pool[rng.Intn(len(pool))]
		}
		var in []byte
		for _, r := range text {
			in = utf8.AppendRune(in, r)
		}
		table = append(table, byte(len(in)))
		table = append(table, in...)
		for f := 0; f < 4; f++ {
			want := oracle.normalize(text, f == 1 || f == 3, f == 2 || f == 3)
			var out []byte
			for _, r := range want {
				out = utf8.AppendRune(out, r)
			}
			if len(out) > 255 {
				t.Fatalf("case %d form %d too long: %d bytes", i, f, len(out))
			}
			table = append(table, byte(len(out)))
			table = append(table, out...)
		}
	}
	var b strings.Builder
	b.WriteString("import(std)\n")
	b.WriteString(normalizeHelpers)
	b.WriteString(normalizeByteArray("LAW_TABLE", table))
	fmt.Fprintf(&b, "LAW_CASES: u32 = %d\n", cases)
	b.WriteString(`
main: (): i32 {
  table: []u8 = view(&LAW_TABLE)
  at: u32 = 0
  index: u32 = 0
  fail: u32 = 0
  while index < LAW_CASES && fail == u32(0) {
    in_len: u32 = u32(table[at])
    input: []u8 = table[at + u32(1):at + u32(1) + in_len]
    at = at + u32(1) + in_len
    form: u32 = 0
    while form < u32(4) {
      want_len: u32 = u32(table[at])
      want: []u8 = table[at + u32(1):at + u32(1) + want_len]
      at = at + u32(1) + want_len
      fail == u32(0) && !normalize_conf_check(form, input, want) ? { fail = index * u32(4) + form + u32(1) }
      form = form + u32(1)
    }
    index = index + u32(1)
  }
  fail == u32(0) ? { 42 } | { i32_bits_u32((fail - u32(1)) % u32(200) + u32(1)) }
}
`)
	code, abnormal := buildAndRun(t, "stdlib_normalize_laws", b.String())
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v): (case*4+form) mod 200 is exit-1", code, abnormal)
	}
}
