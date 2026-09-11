package main

import (
	"encoding/json"
	"os"
	"sort"
	"unicode/utf8"
)

// The Go reference for the normalize workloads is a straightforward Go
// normalizer over the same Unicode 17.0.0 extract the Oak tables come from
// (stdlib/unicode17_normalize.json): full decomposition with the Hangul
// algorithm, a stable sort of each run of non-starters by ccc, and canonical
// composition with the blocking rule. Go's standard library has no
// normalizer and the module takes no dependency, so this is a plain,
// allocation-per-call implementation rather than a tuned one; RESULTS.md says
// so where the numbers are read.

type normTables struct {
	ccc   map[rune]int
	nfd   map[rune][]rune
	pairs map[[2]rune]rune
}

var norm *normTables
var normText, normOut, normASCII []byte

const (
	normSBase, normLBase, normVBase, normTBase = 0xAC00, 0x1100, 0x1161, 0x11A7
	normLCount, normVCount, normTCount         = 19, 21, 28
	normNCount                                 = normVCount * normTCount
	normSCount                                 = normLCount * normNCount
)

func loadNormTables() *normTables {
	data, err := os.ReadFile("stdlib/unicode17_normalize.json")
	if err != nil {
		panic(err)
	}
	var raw struct {
		Props [][3]int `json:"props"`
		NFD   [][3]int `json:"nfd"`
		Pairs [][3]int `json:"pairs"`
		Pool  []int    `json:"pool"`
	}
	if err := json.Unmarshal(data, &raw); err != nil {
		panic(err)
	}
	t := &normTables{ccc: map[rune]int{}, nfd: map[rune][]rune{}, pairs: map[[2]rune]rune{}}
	for _, r := range raw.Props {
		if c := r[2] & 255; c != 0 {
			for cp := r[0]; cp <= r[1]; cp++ {
				t.ccc[rune(cp)] = c
			}
		}
	}
	for _, e := range raw.NFD {
		seq := make([]rune, e[2])
		for i := range seq {
			seq[i] = rune(raw.Pool[e[1]+i])
		}
		t.nfd[rune(e[0])] = seq
	}
	for _, p := range raw.Pairs {
		t.pairs[[2]rune{rune(p[0]), rune(p[1])}] = rune(p[2])
	}
	return t
}

func (t *normTables) decompose(dst []rune, r rune) []rune {
	if r >= normSBase && r < normSBase+normSCount {
		index := int(r - normSBase)
		dst = append(dst, normLBase+rune(index/normNCount), normVBase+rune((index%normNCount)/normTCount))
		if index%normTCount != 0 {
			dst = append(dst, normTBase+rune(index%normTCount))
		}
		return dst
	}
	if d, ok := t.nfd[r]; ok {
		return append(dst, d...)
	}
	return append(dst, r)
}

func (t *normTables) composePair(a, b rune) (rune, bool) {
	if a >= normLBase && a < normLBase+normLCount && b >= normVBase && b < normVBase+normVCount {
		return normSBase + ((a-normLBase)*normVCount+(b-normVBase))*normTCount, true
	}
	if a >= normSBase && a < normSBase+normSCount && (a-normSBase)%normTCount == 0 && b > normTBase && b < normTBase+normTCount {
		return a + (b - normTBase), true
	}
	c, ok := t.pairs[[2]rune{a, b}]
	return c, ok
}

func (t *normTables) normalize(text []byte, compose bool, out []byte) []byte {
	var d []rune
	for at := 0; at < len(text); {
		r, width := utf8.DecodeRune(text[at:])
		if r == utf8.RuneError && width <= 1 {
			return out[:0]
		}
		d = t.decompose(d, r)
		at += width
	}
	for i := 0; i < len(d); {
		if t.ccc[d[i]] == 0 {
			i++
			continue
		}
		j := i
		for j < len(d) && t.ccc[d[j]] != 0 {
			j++
		}
		run := d[i:j]
		sort.SliceStable(run, func(a, b int) bool { return t.ccc[run[a]] < t.ccc[run[b]] })
		i = j
	}
	if compose && len(d) > 0 {
		kept := d[:0]
		starter := -1
		lastClass := -1
		for _, c := range d {
			cc := t.ccc[c]
			if starter >= 0 && (lastClass == -1 || lastClass < cc) {
				if composite, ok := t.composePair(kept[starter], c); ok {
					kept[starter] = composite
					continue
				}
			}
			kept = append(kept, c)
			if cc == 0 {
				starter = len(kept) - 1
				lastClass = -1
			} else {
				lastClass = cc
			}
		}
		d = kept
	}
	out = out[:0]
	for _, r := range d {
		out = utf8.AppendRune(out, r)
	}
	return out
}

func normalizeSetup(scale float64) {
	if norm == nil {
		norm = loadNormTables()
	}
	normText = fillUTF8(scaled(scale, 8<<20), 8)
	normOut = make([]byte, 0, len(normText)*4)
	values := fillDecimals(scaled(scale, 1000000), 9)
	normASCII = writeDecimals(values)
	for _, w := range workloads {
		switch w.name {
		case "normalize/nfc", "normalize/nfd":
			w.items, w.bytes = uint64(len(normText)), uint64(len(normText))
		case "normalize/is_nfc_ascii":
			w.items, w.bytes = uint64(len(normASCII)), uint64(len(normASCII))
		}
	}
}

func normalizeNFC() uint64 {
	normOut = norm.normalize(normText, true, normOut)
	return fnvBytes(normOut)
}

func normalizeNFD() uint64 {
	normOut = norm.normalize(normText, false, normOut)
	return fnvBytes(normOut)
}

// The quick check on ASCII: every byte below 128 is a starter with NFC_QC=Y.
func normalizeIsNFCASCII() uint64 {
	for _, b := range normASCII {
		if b >= 0x80 {
			return 0
		}
	}
	return 1
}
