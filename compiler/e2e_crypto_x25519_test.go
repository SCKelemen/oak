package compiler

import (
	"crypto/ecdh"
	"crypto/hkdf"
	"crypto/sha256"
	"fmt"
	"github.com/SCKelemen/oak/stdlib"
	"math/big"
	"math/rand"
	"strings"
	"testing"
)

type x25519Vector struct{ key, peer, want []byte }

func x25519Program(vectors []x25519Vector) string {
	var s strings.Builder
	s.WriteString("import(\"crypto/x25519\")\nimport(\"crypto/subtle\")\nmain: (): i32 {\n")
	for _, v := range vectors {
		s.WriteString("true ? {\n")
		writeBytes(&s, "key", v.key)
		writeBytes(&s, "peer", v.peer)
		s.WriteString("out: [33]u8\ni: u32 = 0\nwhile i < u32(33) { out[i] = u8(91)\ni = i + u32(1) }\n")
		if v.want == nil {
			s.WriteString("assert(!x25519.shared(key, peer, span(&out)))\ni = u32(0)\nwhile i < u32(33) { assert(out[i] == u8(91))\ni = i + u32(1) }\n")
		} else {
			writeBytes(&s, "want", v.want)
			s.WriteString("assert(x25519.shared(key, peer, span(&out)))\nassert(out[32] == u8(91))\nout_view: []u8 = view(&out)\nassert(subtle.equal(subslice(out_view,u32(0),u32(32)),want))\n")
		}
		s.WriteString("}\n")
	}
	s.WriteString("42\n}\n")
	return s.String()
}

func runX25519Compiled(t *testing.T, name, src string) {
	t.Helper()
	root := writeModule(t, map[string]string{"oak.mod": "module example.com/" + name + "\noak 0.1.0\n", "main.oak": "package main\n" + src})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("X25519 program exited %d, abnormal=%v", code, abnormal)
	}
}

// Literal expected bytes from RFC 7748 sections 5.2 and 6.1.
func TestE2ECryptoX25519RFC7748(t *testing.T) {
	h := func(s string) []byte { return cryptoHex(t, s) }
	base := make([]byte, 32)
	base[0] = 9
	alice := h("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a")
	bob := h("5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb")
	ap := h("8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a")
	bp := h("de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f")
	shared := h("4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742")
	v := []x25519Vector{
		{h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4"), h("e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"), h("c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552")},
		{h("4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d"), h("e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493"), h("95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957")},
		{alice, base, ap}, {bob, base, bp}, {alice, bp, shared}, {bob, ap, shared},
		{base, base, h("422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079")},
	}
	// Every public vector compiled; one full ladder also interpreted.
	runHashProgram(t, "x25519_rfc7748", x25519Program(v), x25519Program(v[:1]))
}

func TestE2ECryptoX25519Differential(t *testing.T) {
	rng := rand.New(rand.NewSource(7748))
	var v []x25519Vector
	oracle := func(k, p []byte) {
		private, err := ecdh.X25519().NewPrivateKey(k)
		if err != nil {
			t.Fatal(err)
		}
		public, err := ecdh.X25519().NewPublicKey(p)
		if err != nil {
			t.Fatal(err)
		}
		want, err := private.ECDH(public)
		if err != nil {
			want = nil
		}
		v = append(v, x25519Vector{k, p, want})
	}
	for i := 0; i < 64; i++ {
		k, p := make([]byte, 32), make([]byte, 32)
		rng.Read(k)
		rng.Read(p)
		oracle(k, p)
	}
	// All noncanonical encodings p through 2^255-1, both top-bit variants.
	for n := 0; n < 19; n++ {
		for _, top := range []byte{0x7f, 0xff} {
			p := make([]byte, 32)
			for i := range p {
				p[i] = 255
			}
			p[0] = byte(237 + n)
			p[31] = top
			oracle(cryptoSequence(0, 32), p)
		}
	}
	// Small-order representatives and their masked-top-bit aliases.
	for _, s := range []string{
		"0000000000000000000000000000000000000000000000000000000000000000",
		"0100000000000000000000000000000000000000000000000000000000000000",
		"e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800",
		"5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157",
		"ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
	} {
		p := cryptoHex(t, s)
		oracle(cryptoSequence(0, 32), p)
		q := append([]byte(nil), p...)
		q[31] |= 128
		oracle(cryptoSequence(0, 32), q)
	}
	runX25519Compiled(t, "x25519_go", x25519Program(v))
}

func TestE2ECryptoX25519ContractsAndHKDF(t *testing.T) {
	key := cryptoSequence(0, 32)
	other := cryptoSequence(32, 32)
	a, _ := ecdh.X25519().NewPrivateKey(key)
	b, _ := ecdh.X25519().NewPrivateKey(other)
	secret, err := a.ECDH(b.PublicKey())
	if err != nil {
		t.Fatal(err)
	}
	// Protocol chooses an explicit ordered-public-key transcript as HKDF info.
	info := append([]byte("Oak X25519 test v1"), a.PublicKey().Bytes()...)
	info = append(info, b.PublicKey().Bytes()...)
	want, err := hkdf.Key(sha256.New, secret, nil, string(info), 32)
	if err != nil {
		t.Fatal(err)
	}
	var s strings.Builder
	s.WriteString("import(\"crypto/x25519\")\nimport(\"crypto/hkdf\")\nimport(\"crypto/subtle\")\nmain: (): i32 {\n")
	writeBytes(&s, "key", key)
	writeBytes(&s, "other", other)
	writeBytes(&s, "peer", b.PublicKey().Bytes())
	writeBytes(&s, "public_want", a.PublicKey().Bytes())
	writeBytes(&s, "info", info)
	writeBytes(&s, "want", want)
	s.WriteString(`public: [32]u8
assert(x25519.public_key(key,span(&public)))
assert(subtle.equal(view(&public),public_want))
secret: [32]u8
reverse: [32]u8
assert(x25519.shared(key,peer,span(&secret)))
assert(x25519.shared(other,view(&public),span(&reverse)))
assert(subtle.equal(view(&secret),view(&reverse)))
out: [32]u8
assert(hkdf.key256(subslice(key,u32(0),u32(0)),view(&secret),info,span(&out)))
assert(subtle.equal(view(&out),want))
`)
	for _, n := range []int{0, 1, 31, 33, 64} {
		writeBytes(&s, fmt.Sprintf("bad%d", n), make([]byte, n))
		fmt.Fprintf(&s, "assert(!x25519.shared(bad%d,peer,span(&out)))\nassert(!x25519.shared(key,bad%d,span(&out)))\nassert(!x25519.public_key(bad%d,span(&out)))\nassert(subtle.equal(view(&out),want))\n", n, n, n)
	}
	s.WriteString("assert(!x25519.shared(key,peer,span(&out)[u32(0):u32(31)]))\nassert(!x25519.public_key(key,span(&out)[u32(0):u32(0)]))\nassert(subtle.equal(view(&out),want))\n42\n}\n")
	runX25519Compiled(t, "x25519_hkdf", s.String())
}

func TestE2ECryptoX25519Iterated(t *testing.T) {
	var s strings.Builder
	s.WriteString(`import("crypto/x25519")
import("crypto/subtle")
main: (): i32 {
k: [32]u8
u: [32]u8
k[0] = u8(9)
u[0] = u8(9)
i: u32 = 0
while i < u32(1000) {
 next: [32]u8
 assert(x25519.shared(view(&k),view(&u),span(&next)))
 u = k
 k = next
 i = i + u32(1)
}
`)
	writeBytes(&s, "want", cryptoHex(t, "684cf59ba83309552800ef566f2f4d3c1c3887c49360e3875f2eb94d99532c51"))
	s.WriteString("assert(subtle.equal(view(&k),want))\n42\n}\n")
	runX25519Compiled(t, "x25519_iterated", s.String())
}

// Check the actual private field helpers against independent arbitrary-precision
// arithmetic. The package source is embedded into this test's Oak module so
// these helpers do not become part of the public crypto API.
func TestE2ECryptoX25519Field(t *testing.T) {
	modulus := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 255), big.NewInt(19))
	limit := new(big.Int).Lsh(big.NewInt(1), 255)
	rng := rand.New(rand.NewSource(25519))
	values := []*big.Int{big.NewInt(0), big.NewInt(1), big.NewInt(32767), big.NewInt(32768), new(big.Int).Sub(modulus, big.NewInt(1)), new(big.Int).Set(modulus), new(big.Int).Sub(limit, big.NewInt(1))}
	for i := 0; i < 17; i++ {
		values = append(values, new(big.Int).Lsh(big.NewInt(32767), uint(15*i)))
	}
	for i := 0; i < 32; i++ {
		values = append(values, new(big.Int).Rand(rng, limit))
	}
	var s strings.Builder
	s.WriteString(strings.Replace(stdlib.Packages["crypto/x25519"], "package x25519", "", 1))
	s.WriteString(`
field_equal: (a: [17]u64,b: [17]u64): Bool {
 // Canonicalize a bounded residue before comparing with the Go oracle.
 candidate: [17]u64
 carry: u64 = 19
 i: u32 = 0
 while i < u32(17) {
  assert(a[i] < u64(32768))
  carry = carry + a[i]
  candidate[i] = carry & u64(32767)
  carry = carry >> u64(15)
  i = i + u32(1)
 }
 canonical: [17]u64 = select(a,candidate,carry)
 same: Bool = true
 i = u32(0)
 while i < u32(17) { same = same && canonical[i] == b[i]
 i = i + u32(1) }
 same
}
main: (): i32 {
`)
	writeField := func(name string, n *big.Int) {
		fmt.Fprintf(&s, "%s: [17]u64\n", name)
		x := new(big.Int).Set(n)
		for i := 0; i < 17; i++ {
			fmt.Fprintf(&s, "%s[%d] = u64(%d)\n", name, i, new(big.Int).And(x, big.NewInt(32767)).Uint64())
			x.Rsh(x, 15)
		}
	}
	for i, a := range values {
		b := values[len(values)-1-i]
		// Pair each sample with itself as well to exercise maximal convolution.
		for _, b := range []*big.Int{b, a} {
			s.WriteString("true ? {\n")
			writeField("a", a)
			writeField("b", b)
			for _, op := range []string{"add", "sub", "mul"} {
				want := new(big.Int)
				switch op {
				case "add":
					want.Add(a, b)
				case "sub":
					want.Sub(a, b)
				case "mul":
					want.Mul(a, b)
				}
				want.Mod(want, modulus)
				writeField("want_"+op, want)
				fmt.Fprintf(&s, "assert(field_equal(%s(a,b),want_%s))\n", op, op)
			}
			s.WriteString("}\n")
		}
	}
	s.WriteString("42\n}\n")
	runX25519Compiled(t, "x25519_field", s.String())
}
