package compiler

import (
	"bytes"
	"crypto/hkdf"
	"crypto/hmac"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"math/rand"
	"strings"
	"testing"
)

// Expected RFC outputs are literal public vectors, independent of the Go
// differential oracle. Both the interpreter and compiled Oak must match.
// Sources: https://www.rfc-editor.org/rfc/rfc4231#section-4
//
//	https://www.rfc-editor.org/rfc/rfc5869#appendix-A
func cryptoHex(t *testing.T, s string) []byte {
	t.Helper()
	b, err := hex.DecodeString(s)
	if err != nil {
		t.Fatal(err)
	}
	return b
}

func cryptoSequence(start, count int) []byte {
	b := make([]byte, count)
	for i := range b {
		b[i] = byte(start + i)
	}
	return b
}

type cryptoMACVector struct{ key, message, tag []byte }

func cryptoMACProgram(vectors []cryptoMACVector) string {
	var s strings.Builder
	s.WriteString("import(\"crypto/hmac\")\nimport(\"crypto/subtle\")\nprefix_equal: (a: []u8, b: []u8): Bool = subtle.equal(subslice(a, u32(0), len(b)), b)\nmain: (): i32 {\n")
	for _, v := range vectors {
		s.WriteString("true ? {\n")
		writeBytes(&s, "key", v.key)
		writeBytes(&s, "message", v.message)
		writeBytes(&s, "want", v.tag)
		s.WriteString("out: [33]u8\nout[32] = u8(91)\nassert(hmac.sum256(key, message, span(&out)))\n")
		s.WriteString("assert(prefix_equal(view(&out), want))\n")
		s.WriteString("assert(out[32] == u8(91))\ntrue ? { out_view: []u8 = view(&out)\nassert(hmac.verify256(key, message, subslice(out_view, u32(0), u32(32)))) }\n")
		s.WriteString("out[31] = out[31] ^ u8(1)\ntrue ? { out_view: []u8 = view(&out)\nassert(!hmac.verify256(key, message, subslice(out_view, u32(0), u32(32)))) }\n")
		s.WriteString("true ? { out_view: []u8 = view(&out)\nassert(!hmac.verify256(key, message, subslice(out_view, u32(0), u32(31)))) }\nassert(!hmac.verify256(key, message, view(&out)))\n")
		a, b := len(v.message)/3, 2*len(v.message)/3
		fmt.Fprintf(&s, "assert(hmac.sum256_parts(key, subslice(message, u32(0), u32(%d)), subslice(message, u32(%d), u32(%d)), subslice(message, u32(%d), u32(%d)), span(&out)))\n", a, a, b-a, b, len(v.message)-b)
		s.WriteString("assert(prefix_equal(view(&out), want))\n")
		s.WriteString("small: [31]u8\ni: u32 = 0\nwhile i < u32(31) { small[i] = u8(91)\ni = i + u32(1) }\nassert(!hmac.sum256(key, message, span(&small)))\ni = u32(0)\nwhile i < u32(31) { assert(small[i] == u8(91))\ni = i + u32(1) }\n}\n")
	}
	s.WriteString("42\n}\n")
	return s.String()
}

func TestE2ECryptoHMACRFC4231(t *testing.T) {
	repeat := func(b byte, n int) []byte { return bytes.Repeat([]byte{b}, n) }
	v := []cryptoMACVector{
		{repeat(0x0b, 20), []byte("Hi There"), cryptoHex(t, "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7")},
		{[]byte("Jefe"), []byte("what do ya want for nothing?"), cryptoHex(t, "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843")},
		{repeat(0xaa, 20), repeat(0xdd, 50), cryptoHex(t, "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe")},
		{cryptoSequence(1, 25), repeat(0xcd, 50), cryptoHex(t, "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b")},
		{repeat(0x0c, 20), []byte("Test With Truncation"), cryptoHex(t, "a3b6167473100ee06e0c796c2955552b")},
		{repeat(0xaa, 131), []byte("Test Using Larger Than Block-Size Key - Hash Key First"), cryptoHex(t, "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54")},
		{repeat(0xaa, 131), []byte("This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm."), cryptoHex(t, "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2")},
	}
	runHashProgram(t, "crypto_hmac_rfc4231", cryptoMACProgram(v))
}

func TestE2ECryptoHMACDifferential(t *testing.T) {
	rng := rand.New(rand.NewSource(4231))
	var v []cryptoMACVector
	for i, n := range []int{0, 1, 31, 32, 55, 56, 63, 64, 65, 127, 128, 129} {
		key := make([]byte, []int{0, 1, 32, 63, 64, 65, 131}[i%7])
		message := make([]byte, n)
		rng.Read(key)
		rng.Read(message)
		oracle := hmac.New(sha256.New, key)
		oracle.Write(message)
		v = append(v, cryptoMACVector{key, message, oracle.Sum(nil)})
	}
	runHashProgram(t, "crypto_hmac_go", cryptoMACProgram(v))
}

type cryptoKDFVector struct{ ikm, salt, info, prk, okm []byte }

func cryptoKDFProgram(vectors []cryptoKDFVector) string {
	var s strings.Builder
	s.WriteString("import(\"crypto/hkdf\")\nimport(\"crypto/subtle\")\nprefix_equal: (a: []u8, b: []u8): Bool = subtle.equal(subslice(a, u32(0), len(b)), b)\nmain: (): i32 {\n")
	for _, v := range vectors {
		s.WriteString("true ? {\n")
		writeBytes(&s, "ikm", v.ikm)
		writeBytes(&s, "salt", v.salt)
		writeBytes(&s, "info", v.info)
		writeBytes(&s, "want_prk", v.prk)
		writeBytes(&s, "want_okm", v.okm)
		s.WriteString("prk: [33]u8\nprk[32] = u8(91)\nassert(hkdf.extract256(salt, ikm, span(&prk)))\nassert(prk[32] == u8(91))\nassert(prefix_equal(view(&prk), want_prk))\nprk_view: []u8 = view(&prk)\n")
		fmt.Fprintf(&s, "out: [%d]u8\nassert(hkdf.expand256(subslice(prk_view, u32(0), u32(32)), info, span(&out)))\nassert(subtle.equal(view(&out), want_okm))\n", len(v.okm))
		s.WriteString("assert(hkdf.key256(salt, ikm, info, span(&out)))\nassert(subtle.equal(view(&out), want_okm))\n}\n")
	}
	s.WriteString("42\n}\n")
	return s.String()
}

func TestE2ECryptoHKDFRFC5869(t *testing.T) {
	ikm := bytes.Repeat([]byte{0x0b}, 22)
	v := []cryptoKDFVector{
		{ikm, cryptoSequence(0, 13), cryptoSequence(0xf0, 10), cryptoHex(t, "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5"), cryptoHex(t, "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865")},
		{cryptoSequence(0, 80), cryptoSequence(0x60, 80), cryptoSequence(0xb0, 80), cryptoHex(t, "06a6b88c5853361a06104c9ceb35b45cef760014904671014a193f40c15fc244"), cryptoHex(t, "b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71cc30c58179ec3e87c14c01d5c1f3434f1d87")},
		{ikm, nil, nil, cryptoHex(t, "19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04"), cryptoHex(t, "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8")},
	}
	runHashProgram(t, "crypto_hkdf_rfc5869", cryptoKDFProgram(v))
}

func TestE2ECryptoHKDFLimits(t *testing.T) {
	// Exercise the 255-block boundary in compiled Oak and compare every byte
	// with Go. The smaller RFC cases also execute in the interpreter.
	prk := cryptoSequence(0, 32)
	var s strings.Builder
	s.WriteString("import(\"crypto/hkdf\")\nmain: (): i32 {\n")
	writeBytes(&s, "prk", prk)
	s.WriteString("empty: []u8 = subslice(prk, u32(0), u32(0))\n")
	for _, n := range []int{0, 1, 31, 32, 33, 8160} {
		want, err := hkdf.Expand(sha256.New, prk, "", n)
		if err != nil {
			t.Fatal(err)
		}
		fmt.Fprintf(&s, "true ? {\nout: [%d]u8\nout[%d] = u8(91)\nassert(hkdf.expand256(prk, empty, span(&out)[u32(0):u32(%d)]))\nassert(out[%d] == u8(91))\n", n+1, n, n, n)
		// A generated expected array keeps the final full-length comparison a
		// loop rather than thousands of control-flow nodes.
		writeBytes(&s, "want", want)
		s.WriteString("i: u32 = 0\nwhile i < len(want) { assert(out[i] == want[i])\ni = i + u32(1) }\n}\n")
	}
	s.WriteString(`
too_long: [8161]u8
i: u32 = 0
while i < u32(8161) { too_long[i] = u8(91)
i = i + u32(1) }
assert(!hkdf.expand256(prk, empty, span(&too_long)))
assert(!hkdf.key256(empty, prk, empty, span(&too_long)))
i = u32(0)
while i < u32(8161) { assert(too_long[i] == u8(91))
i = i + u32(1) }
small: [31]u8
i = u32(0)
while i < u32(31) { small[i] = u8(91)
i = i + u32(1) }
assert(!hkdf.extract256(empty, prk, span(&small)))
assert(!hkdf.expand256(subslice(prk, u32(0), u32(31)), empty, span(&small)))
assert(!hkdf.expand256(empty, empty, span(&small)[u32(0):u32(0)]))
i = u32(0)
while i < u32(31) { assert(small[i] == u8(91))
i = i + u32(1) }
42
}
`)
	root := writeModule(t, map[string]string{"oak.mod": "module example.com/crypto_limits\noak 0.1.0\n", "main.oak": "package main\n" + s.String()})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("crypto boundary program exited %d, abnormal=%v", code, abnormal)
	}
}

func TestE2ECryptoSubtle(t *testing.T) {
	runHashProgram(t, "crypto_subtle", `import("crypto/subtle")
main: (): i32 {
a: [32]u8
b: [32]u8
assert(subtle.equal(view(&a), view(&b)))
true ? {
av: []u8 = view(&a)
bv: []u8 = view(&b)
assert(subtle.equal(subslice(av, u32(0), u32(0)), subslice(bv, u32(0), u32(0))))
assert(!subtle.equal(av, subslice(bv, u32(0), u32(31))))
}
i: u32 = 0
while i < u32(32) {
  b[i] = u8(128)
  assert(!subtle.equal(view(&a), view(&b)))
  b[i] = u8(0)
  i = i + u32(1)
}
42
}`)
}
