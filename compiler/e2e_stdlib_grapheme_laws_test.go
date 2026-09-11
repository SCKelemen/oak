package compiler

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// The grapheme law test: the compiled Oak state machine (grapheme_next over
// grapheme_breaks/grapheme_advance) must decide every boundary exactly as
// the UAX #29 rules do when the rules are read as scans over the preceding
// text. The Go functions below are a transliteration of `ruleBreak` in
// spec/lean/Oak/GraphemeBreak.lean, independent of the state machine; the
// Oak program enumerates every sequence of five symbol kinds (18^5) and
// folds its decisions into one checksum per leading kind, which must match
// the checksum the Go oracle computes over the same enumeration.

type graphemeKind struct {
	name   string
	scalar uint32
	gcb    int
	incb   int
	pict   bool
}

const (
	gcbOther = iota
	gcbCR
	gcbLF
	gcbControl
	gcbExtend
	gcbZWJ
	gcbRI
	gcbPrepend
	gcbSpacingMark
	gcbL
	gcbV
	gcbT
	gcbLV
	gcbLVT
)

const (
	incbNone = iota
	incbConsonant
	incbExtend
	incbLinker
)

// One representative scalar per distinguishable symbol shape (Unicode 17.0.0).
var graphemeKinds = []graphemeKind{
	{"other", 0x61, gcbOther, incbNone, false},
	{"cr", 0x0D, gcbCR, incbNone, false},
	{"lf", 0x0A, gcbLF, incbNone, false},
	{"control", 0x01, gcbControl, incbNone, false},
	{"extend", 0x200C, gcbExtend, incbNone, false},
	{"extend_incb", 0x0300, gcbExtend, incbExtend, false},
	{"linker", 0x094D, gcbExtend, incbLinker, false},
	{"zwj", 0x200D, gcbZWJ, incbExtend, false},
	{"ri", 0x1F1E6, gcbRI, incbNone, false},
	{"prepend", 0x0600, gcbPrepend, incbNone, false},
	{"spacing_mark", 0x0903, gcbSpacingMark, incbNone, false},
	{"l", 0x1100, gcbL, incbNone, false},
	{"v", 0x1160, gcbV, incbNone, false},
	{"t", 0x11A8, gcbT, incbNone, false},
	{"lv", 0xAC00, gcbLV, incbNone, false},
	{"lvt", 0xAC01, gcbLVT, incbNone, false},
	{"pictographic", 0x1F600, gcbOther, incbNone, true},
	{"consonant", 0x0915, gcbOther, incbConsonant, false},
}

func gcbIsControl(g int) bool { return g == gcbControl || g == gcbCR || g == gcbLF }

// ruleBreak is UAX #29 read as scans: history is the preceding text, most
// recent first (Lean: ruleBreak).
func ruleBreak(history []graphemeKind, cur graphemeKind) bool {
	if len(history) == 0 {
		return true // GB1
	}
	prev := history[0]
	switch {
	case prev.gcb == gcbCR && cur.gcb == gcbLF:
		return false // GB3
	case gcbIsControl(prev.gcb):
		return true // GB4
	case gcbIsControl(cur.gcb):
		return true // GB5
	case prev.gcb == gcbL && (cur.gcb == gcbL || cur.gcb == gcbV || cur.gcb == gcbLV || cur.gcb == gcbLVT):
		return false // GB6
	case (prev.gcb == gcbLV || prev.gcb == gcbV) && (cur.gcb == gcbV || cur.gcb == gcbT):
		return false // GB7
	case (prev.gcb == gcbLVT || prev.gcb == gcbT) && cur.gcb == gcbT:
		return false // GB8
	case cur.gcb == gcbExtend || cur.gcb == gcbZWJ:
		return false // GB9
	case cur.gcb == gcbSpacingMark:
		return false // GB9a
	case prev.gcb == gcbPrepend:
		return false // GB9b
	case conjLinked(history) && cur.incb == incbConsonant:
		return false // GB9c
	case pictZwj(history) && cur.pict:
		return false // GB11
	case prev.gcb == gcbRI && cur.gcb == gcbRI && riRun(history)%2 == 1:
		return false // GB12, GB13
	}
	return true // GB999
}

func riRun(history []graphemeKind) int {
	n := 0
	for _, s := range history {
		if s.gcb != gcbRI {
			break
		}
		n++
	}
	return n
}

func pictBase(history []graphemeKind) bool {
	i := 0
	for i < len(history) && history[i].gcb == gcbExtend {
		i++
	}
	return i < len(history) && history[i].pict
}

func pictZwj(history []graphemeKind) bool {
	return len(history) > 0 && history[0].gcb == gcbZWJ && pictBase(history[1:])
}

func conjLinked(history []graphemeKind) bool {
	seen := false
	for _, s := range history {
		switch s.incb {
		case incbLinker:
			seen = true
		case incbExtend:
		case incbConsonant:
			return seen
		default:
			return false
		}
	}
	return false
}

// graphemeLawChecksum folds every decision of every 5-symbol sequence that
// starts with kind `first` (positions 1..4) into one number, in the order
// the Oak program uses: the sequence is a base-18 counter over the trailing
// four positions, positions ascending inside a sequence.
func graphemeLawChecksum(first int) uint64 {
	const modulus = 1000000007
	var hash uint64
	k := len(graphemeKinds)
	seq := make([]graphemeKind, 5)
	for k2 := 0; k2 < k; k2++ {
		for k3 := 0; k3 < k; k3++ {
			for k4 := 0; k4 < k; k4++ {
				for k5 := 0; k5 < k; k5++ {
					seq[0], seq[1], seq[2], seq[3], seq[4] = graphemeKinds[first], graphemeKinds[k2], graphemeKinds[k3], graphemeKinds[k4], graphemeKinds[k5]
					for i := 1; i < 5; i++ {
						history := make([]graphemeKind, i)
						for j := 0; j < i; j++ {
							history[j] = seq[i-1-j]
						}
						bit := uint64(1)
						if ruleBreak(history, seq[i]) {
							bit = 2
						}
						hash = (hash*3 + bit) % modulus
					}
				}
			}
		}
	}
	return hash
}

func TestE2EStdlibGraphemeLaws(t *testing.T) {
	// The table must have the shape the Lean model assumes (Sym.WF) and the
	// representative scalars must carry the classes the oracle assigns.
	tablePath := filepath.Join("..", "stdlib", "unicode17_grapheme.json")
	raw, err := os.ReadFile(tablePath)
	if err != nil {
		t.Fatal(err)
	}
	var extract struct {
		Version string     `json:"version"`
		Ranges  [][3]int64 `json:"ranges"`
	}
	if err := json.Unmarshal(raw, &extract); err != nil {
		t.Fatal(err)
	}
	if extract.Version != "17.0.0" {
		t.Fatalf("unexpected Unicode version %q", extract.Version)
	}
	classOf := func(scalar uint32) int64 {
		for _, r := range extract.Ranges {
			if int64(scalar) >= r[0] && int64(scalar) <= r[1] {
				return r[2]
			}
		}
		return 0
	}
	for i, r := range extract.Ranges {
		gcb, incb, pict := r[2]&255, (r[2]>>8)&3, r[2]>>10
		if pict == 1 && gcb != gcbOther {
			t.Fatalf("range %d: pictographic scalar with class %d", i, gcb)
		}
		if incb == incbConsonant && gcb != gcbOther {
			t.Fatalf("range %d: consonant with class %d", i, gcb)
		}
		if incb == incbLinker && gcb != gcbExtend {
			t.Fatalf("range %d: linker with class %d", i, gcb)
		}
		if incb == incbExtend && gcb != gcbExtend && gcb != gcbZWJ {
			t.Fatalf("range %d: InCB=Extend with class %d", i, gcb)
		}
		if i > 0 && r[0] <= extract.Ranges[i-1][1] {
			t.Fatalf("range %d overlaps or is unsorted", i)
		}
	}
	for _, kind := range graphemeKinds {
		props := classOf(kind.scalar)
		pict := props>>10 == 1
		if int(props&255) != kind.gcb || int((props>>8)&3) != kind.incb || pict != kind.pict {
			t.Fatalf("%s U+%04X: table says %d, oracle expects gcb %d incb %d pict %v", kind.name, kind.scalar, props, kind.gcb, kind.incb, kind.pict)
		}
	}

	// The Oak program: enumerate 18^4 tails per leading kind and compare
	// each checksum with the oracle's.
	var scalars, expected []string
	for i, kind := range graphemeKinds {
		scalars = append(scalars, fmt.Sprintf("%d", kind.scalar))
		expected = append(expected, fmt.Sprintf("%d", graphemeLawChecksum(i)))
	}
	n := len(graphemeKinds)
	src := fmt.Sprintf(`import(std)

put: (dst: [*]u8, at: u32, value: u32): u32 {
  written: u32 = text_result_value(utf8_encode(dst, at, value))
  at + written
}

// checksum_for: every decision of every five-symbol sequence starting with
// kind first, positions 1..4, folded as hash = hash * 3 + (break ? 2 : 1)
// modulo 1000000007.
checksum_for: (kinds: []u32, first: u32): u64 {
  buffer: [24]u8
  hash: u64 = 0
  k2: u32 = 0
  while k2 < u32(%[1]d) {
    k3: u32 = 0
    while k3 < u32(%[1]d) {
      k4: u32 = 0
      while k4 < u32(%[1]d) {
        k5: u32 = 0
        while k5 < u32(%[1]d) {
          off1: u32 = 0
          off2: u32 = 0
          off3: u32 = 0
          off4: u32 = 0
          total: u32 = 0
          true ? {
            dst: [*]u8 = span(&buffer)
            off1 = put(dst, u32(0), kinds[first])
            off2 = put(dst, off1, kinds[k2])
            off3 = put(dst, off2, kinds[k3])
            off4 = put(dst, off3, kinds[k4])
            total = put(dst, off4, kinds[k5])
          }
          mask: u32 = 0
          true ? {
            whole: []u8 = view(&buffer)
            text: []u8 = whole[u32(0):total]
            pos: u32 = 0
            while pos < total {
              pos = grapheme_next(text, pos)
              mask = mask | (u32(1) << pos)
            }
          }
          hash = (hash * u64(3) + u64(((mask >> off1) & u32(1)) + u32(1))) %% u64(1000000007)
          hash = (hash * u64(3) + u64(((mask >> off2) & u32(1)) + u32(1))) %% u64(1000000007)
          hash = (hash * u64(3) + u64(((mask >> off3) & u32(1)) + u32(1))) %% u64(1000000007)
          hash = (hash * u64(3) + u64(((mask >> off4) & u32(1)) + u32(1))) %% u64(1000000007)
          k5 = k5 + u32(1)
        }
        k4 = k4 + u32(1)
      }
      k3 = k3 + u32(1)
    }
    k2 = k2 + u32(1)
  }
  hash
}

main: (): i32 {
  kinds: [%[1]d]u32 = [%[1]d]u32{ %[2]s }
  expected: [%[1]d]u64 = [%[1]d]u64{ %[3]s }
  fail: u32 = 0
  first: u32 = 0
  while first < u32(%[1]d) {
    actual: u64 = checksum_for(view(&kinds), first)
    fail == u32(0) && actual != expected[first] ? { fail = first + u32(100) }
    first = first + u32(1)
  }
  fail == u32(0) ? { 42 } | { i32_bits_u32(fail) }
}
`, n, strings.Join(scalars, ", "), strings.Join(expected, ", "))
	code, abnormal := buildAndRun(t, "stdlib_grapheme_laws", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v): exit-100 is the leading kind whose checksum diverged from the rule oracle", code, abnormal)
	}
}
