package main

import (
	"crypto/sha256"
	"encoding/base64"
	"encoding/binary"
	"encoding/hex"
	"hash/crc32"
	"math/bits"
	"math/rand/v2"
	"net/url"
	"slices"
	"strconv"
	"time"
	"unicode/utf8"
)

// A workload mirrors one entry of a C bridge's table: the same name, the
// same corpus, the same checksum, computed with Go's standard library.
type workload struct {
	name    string
	backend string
	setup   func(scale float64)
	run     func() uint64
	items   uint64
	bytes   uint64
}

var workloads []*workload

func register(name, backend string, setup func(float64), run func() uint64) *workload {
	w := &workload{name: name, backend: backend, setup: setup, run: run}
	workloads = append(workloads, w)
	return w
}

// ---- sort ------------------------------------------------------------------

var sortRandom, sortSorted, sortReversed, sortWork []uint32

func sortSetup(scale float64) {
	n := scaled(scale, 100000)
	sortRandom = fillU32(n, 1)
	sortSorted = slices.Clone(sortRandom)
	slices.Sort(sortSorted)
	sortReversed = make([]uint32, n)
	for i := range sortReversed {
		sortReversed[i] = sortSorted[n-1-i]
	}
	sortWork = make([]uint32, n)
	for _, w := range workloads {
		if len(w.name) > 5 && w.name[:5] == "sort/" {
			w.items, w.bytes = uint64(n), uint64(n)*4
		}
	}
}

func sortRun(input []uint32) uint64 {
	copy(sortWork, input)
	slices.Sort(sortWork)
	return fnvU32(sortWork)
}

// ---- varint ----------------------------------------------------------------

var varintValues, varintDecoded []uint64
var varintBytes, varintReference []byte

func varintSetup(scale float64) {
	n := scaled(scale, 1000000)
	varintValues = fillVarints(n, 2)
	varintDecoded = make([]uint64, n)
	varintBytes = make([]byte, n*10)
	varintReference = make([]byte, 0, n*10)
	for _, v := range varintValues {
		varintReference = binary.AppendUvarint(varintReference, v)
	}
	for _, w := range workloads {
		if len(w.name) > 7 && w.name[:7] == "varint/" {
			w.items, w.bytes = uint64(n), uint64(len(varintReference))
		}
	}
}

func varintEncode() uint64 {
	at := 0
	for _, v := range varintValues {
		at += binary.PutUvarint(varintBytes[at:], v)
	}
	return fnvBytes(varintBytes[:at])
}

func varintDecode() uint64 {
	at := 0
	for i := range varintDecoded {
		v, n := binary.Uvarint(varintReference[at:])
		if n <= 0 {
			return 0
		}
		varintDecoded[i] = v
		at += n
	}
	if at != len(varintReference) {
		return 0
	}
	return fnvU64(varintDecoded)
}

// ---- encoding --------------------------------------------------------------

var raw, base64Text, hexText, decoded, percentRaw []byte
var percentText string

func encodingSetup(scale float64) {
	n := scaled(scale, 16<<20)
	m := scaled(scale, 4<<20)
	raw = fillBytes(n, 3)
	base64Text = make([]byte, base64.StdEncoding.EncodedLen(n))
	base64.StdEncoding.Encode(base64Text, raw)
	hexText = make([]byte, hex.EncodedLen(n))
	hex.Encode(hexText, raw)
	decoded = make([]byte, n)
	percentRaw = fillPercent(m, 4)
	for _, w := range workloads {
		if len(w.name) > 9 && w.name[:9] == "encoding/" {
			w.items, w.bytes = uint64(n), uint64(n)
			if w.name == "encoding/percent_encode" {
				w.items, w.bytes = uint64(m), uint64(m)
			}
		}
	}
}

func base64Encode() uint64 {
	base64.StdEncoding.Encode(base64Text, raw)
	return fnvBytes(base64Text)
}

func base64Decode() uint64 {
	n, err := base64.StdEncoding.Decode(decoded, base64Text)
	if err != nil {
		return 0
	}
	return fnvBytes(decoded[:n])
}

func hexEncode() uint64 {
	hex.Encode(hexText, raw)
	return fnvBytes(hexText)
}

func hexDecode() uint64 {
	n, err := hex.Decode(decoded, hexText)
	if err != nil {
		return 0
	}
	return fnvBytes(decoded[:n])
}

func percentEncode() uint64 {
	// QueryEscape allocates its result; the Oak side writes into caller
	// storage. The allocation is part of what Go users pay.
	percentText = url.QueryEscape(string(percentRaw))
	return fnvBytes([]byte(percentText))
}

// ---- hash ------------------------------------------------------------------

var hashInput []byte
var castagnoli = crc32.MakeTable(crc32.Castagnoli)

func hashSetup(scale float64) {
	n := scaled(scale, 32<<20)
	hashInput = fillBytes(n, 5)
	for _, w := range workloads {
		if len(w.name) > 5 && w.name[:5] == "hash/" {
			w.items, w.bytes = uint64(n), uint64(n)
		}
	}
}

func sha256Run() uint64 {
	digest := sha256.Sum256(hashInput)
	return fnvBytes(digest[:])
}

func crc32cRun() uint64 { return uint64(crc32.Checksum(hashInput, castagnoli)) }

// ---- random ----------------------------------------------------------------

var drawCount uint64

type xoshiro struct{ s0, s1, s2, s3 uint64 }

func splitmix64Next(state uint64) uint64 {
	z := state + 11400714819323198485
	z = (z ^ (z >> 30)) * 13787848793156543929
	z = (z ^ (z >> 27)) * 10723151780598845931
	return z ^ (z >> 31)
}

func seedXoshiro(seed uint64) xoshiro {
	golden := uint64(11400714819323198485)
	a := seed + golden
	return xoshiro{splitmix64Next(seed), splitmix64Next(a), splitmix64Next(a + golden), splitmix64Next(a + golden + golden)}
}

func (x *xoshiro) next() uint64 {
	result := bits.RotateLeft64(x.s1*5, 7) * 9
	t := x.s1 << 17
	x.s2 ^= x.s0
	x.s3 ^= x.s1
	x.s1 ^= x.s2
	x.s0 ^= x.s3
	x.s2 ^= t
	x.s3 = bits.RotateLeft64(x.s3, 45)
	return result
}

func randomSetup(scale float64) {
	drawCount = uint64(scaled(scale, 100000000))
	for _, w := range workloads {
		if len(w.name) > 7 && w.name[:7] == "random/" {
			w.items, w.bytes = drawCount, drawCount*8
		}
	}
}

func xoshiroRun() uint64 {
	state := seedXoshiro(6)
	var acc uint64
	for i := uint64(0); i < drawCount; i++ {
		acc ^= state.next()
	}
	return acc
}

func pcgRun() uint64 {
	state := rand.NewPCG(6, 6)
	var acc uint64
	for i := uint64(0); i < drawCount; i++ {
		acc ^= state.Uint64()
	}
	return acc
}

// ---- uuid ------------------------------------------------------------------

var uuidCount int
var uuidText []byte

func uuidSetup(scale float64) {
	uuidCount = scaled(scale, 1000000)
	uuidText = make([]byte, uuidCount*36)
	for _, w := range workloads {
		if w.name == "uuid/v7_format" {
			w.items, w.bytes = uint64(uuidCount), uint64(uuidCount)*36
		}
	}
}

const lowerHex = "0123456789abcdef"

// The same layout as stdlib/uuid.oak: 48-bit millisecond timestamp, eight
// bytes then two bytes of xoshiro output written big-endian, version 7 and
// the RFC variant stamped afterwards.
func uuidV7Format() uint64 {
	state := seedXoshiro(7)
	var raw [16]byte
	at := 0
	for i := 0; i < uuidCount; i++ {
		millis := uint64(1700000000000) + uint64(i)
		for j := 0; j < 6; j++ {
			raw[j] = byte(millis >> (8 * (5 - j)))
		}
		binary.BigEndian.PutUint64(raw[6:14], state.next())
		binary.BigEndian.PutUint16(raw[14:16], uint16(state.next()))
		raw[6] = raw[6]&0x0F | 0x70
		raw[8] = raw[8]&0x3F | 0x80
		for j := 0; j < 16; j++ {
			uuidText[at] = lowerHex[raw[j]>>4]
			uuidText[at+1] = lowerHex[raw[j]&15]
			at += 2
			if j == 3 || j == 5 || j == 7 || j == 9 {
				uuidText[at] = '-'
				at++
			}
		}
	}
	return fnvBytes(uuidText[:at])
}

// ---- strings ---------------------------------------------------------------

var utf8Text, decimalText, decimalOut []byte
var decimalValues []uint64

func stringsSetup(scale float64) {
	utf8Text = fillUTF8(scaled(scale, 32<<20), 8)
	n := scaled(scale, 1000000)
	decimalValues = fillDecimals(n, 9)
	decimalText = writeDecimals(decimalValues)
	decimalOut = make([]byte, 0, n*21)
	for _, w := range workloads {
		switch w.name {
		case "strings/utf8_validate", "strings/utf8_scan":
			w.items, w.bytes = uint64(len(utf8Text)), uint64(len(utf8Text))
		case "strings/parse_u64", "strings/append_u64":
			w.items, w.bytes = uint64(n), uint64(len(decimalText))
		}
	}
}

func utf8Validate() uint64 {
	if utf8.Valid(utf8Text) {
		return 1
	}
	return 0
}

func utf8Scan() uint64 {
	var acc uint64
	for at := 0; at < len(utf8Text); {
		r, width := utf8.DecodeRune(utf8Text[at:])
		if r == utf8.RuneError && width <= 1 {
			return 0
		}
		acc += uint64(r)
		at += width
	}
	return acc
}

func parseU64() uint64 {
	acc := uint64(fnvOffset)
	start := 0
	for at := 0; at < len(decimalText); at++ {
		if decimalText[at] == '\n' {
			v, err := strconv.ParseUint(string(decimalText[start:at]), 10, 64)
			if err != nil {
				v = 0
			}
			acc = (acc ^ v) * fnvPrime
			start = at + 1
		}
	}
	return acc
}

func appendU64() uint64 {
	decimalOut = decimalOut[:0]
	for _, v := range decimalValues {
		decimalOut = strconv.AppendUint(decimalOut, v, 10)
		decimalOut = append(decimalOut, '\n')
	}
	return fnvBytes(decimalOut)
}

// ---- time ------------------------------------------------------------------

const rfcLayout = "2006-01-02T15:04:05.000000000Z07:00"

var instants []int64
var rfcText, rfcReference []byte

func timeSetup(scale float64) {
	n := scaled(scale, 1000000)
	instants = fillInstants(n, 10)
	rfcText = make([]byte, 0, n*30)
	rfcReference = make([]byte, 0, n*30)
	for _, nanos := range instants {
		rfcReference = time.Unix(0, nanos).UTC().AppendFormat(rfcReference, rfcLayout)
	}
	for _, w := range workloads {
		if len(w.name) > 5 && w.name[:5] == "time/" {
			w.items, w.bytes = uint64(n), uint64(len(rfcReference))
		}
	}
}

func formatRFC3339() uint64 {
	rfcText = rfcText[:0]
	for _, nanos := range instants {
		rfcText = time.Unix(0, nanos).UTC().AppendFormat(rfcText, rfcLayout)
	}
	return fnvBytes(rfcText)
}

func parseRFC3339() uint64 {
	acc := uint64(fnvOffset)
	for at := 0; at+30 <= len(rfcReference); at += 30 {
		t, err := time.Parse(time.RFC3339Nano, string(rfcReference[at:at+30]))
		if err != nil {
			return 0
		}
		acc = (acc ^ uint64(t.UnixNano())) * fnvPrime
	}
	return acc
}

func init() {
	register("sort/random", "go", sortSetup, func() uint64 { return sortRun(sortRandom) })
	register("sort/sorted", "go", sortSetup, func() uint64 { return sortRun(sortSorted) })
	register("sort/reversed", "go", sortSetup, func() uint64 { return sortRun(sortReversed) })
	register("varint/encode", "go", varintSetup, varintEncode)
	register("varint/decode", "go", varintSetup, varintDecode)
	register("encoding/base64_encode", "go", encodingSetup, base64Encode)
	register("encoding/base64_decode", "go", encodingSetup, base64Decode)
	register("encoding/hex_encode", "go", encodingSetup, hexEncode)
	register("encoding/hex_decode", "go", encodingSetup, hexDecode)
	register("encoding/percent_encode", "go", encodingSetup, percentEncode)
	register("hash/sha256", "go", hashSetup, sha256Run)
	register("hash/crc32c", "go", hashSetup, crc32cRun)
	register("random/xoshiro", "go", randomSetup, xoshiroRun)
	register("random/pcg", "go", randomSetup, pcgRun)
	register("uuid/v7_format", "go", uuidSetup, uuidV7Format)
	register("strings/utf8_validate", "go", stringsSetup, utf8Validate)
	register("strings/utf8_scan", "go", stringsSetup, utf8Scan)
	register("strings/parse_u64", "go", stringsSetup, parseU64)
	register("strings/append_u64", "go", stringsSetup, appendU64)
	register("time/format_rfc3339", "go", timeSetup, formatRFC3339)
	register("time/parse_rfc3339", "go", timeSetup, parseRFC3339)
}
