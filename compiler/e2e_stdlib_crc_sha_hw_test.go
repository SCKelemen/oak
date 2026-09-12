package compiler

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"hash/crc32"
	"strings"
	"testing"
)

// The hash package's AArch64 units (stdlib/hash.arm64.oakasm) realize
// crc32c_step7 and sha256_block_hw through the CRC and SHA-2 instructions;
// their Oak bodies are the portable definition. These tests are the oracle
// that ties the two together: the same program is built with the units
// (the default on this host) and with -DOAK_PORTABLE_INTRINSICS (the Oak
// bodies), both outputs must agree byte for byte, and both must agree with
// Go's crypto/sha256 and hash/crc32 (Castagnoli) on the same corpus.

// crcShaLengths are the corpus lengths: the empty input, single bytes, both
// sides of the 56-byte CRC chunk and the 64-byte SHA-256 block, a
// multi-block run, and a long tail.
var crcShaLengths = []int{0, 1, 7, 55, 56, 57, 63, 64, 65, 111, 112, 113, 119, 120, 127, 128, 129, 1000, 4096}

// crcShaCorpus reproduces the program's byte generator: a 64-bit LCG whose
// top byte is the next corpus byte, seeded once and advanced across every
// length in order.
func crcShaCorpus() [][]byte {
	x := uint64(0x9E3779B97F4A7C15)
	var out [][]byte
	for _, n := range crcShaLengths {
		buf := make([]byte, n)
		for i := range buf {
			x = x*6364136223846793005 + 1442695040888963407
			buf[i] = byte(x >> 56)
		}
		out = append(out, buf)
	}
	return out
}

const crcShaProgram = `package main
import("hash")
import("encoding")

write: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern("write")

// The corpus generator: a 64-bit LCG, top byte out.
lcg_fill: (buf: [*]u8, count: u32, seed: u64): u64 {
  x: u64 = seed
  i: u32 = 0
  while i < count {
    x = x * u64(6364136223846793005) + u64(1442695040888963407)
    buf[i] = u8_trunc_u64(x >> u64(56))
    i = i + u32(1)
  }
  x
}

// One line of lowercase hex.
emit_hex: (bytes: []u8): () {
  text: [80]u8
  written: u32 = 0
  true ? {
    t: [*]u8 = span(&text)
    written = encoding.encoding_value(encoding.hex_encode(t, bytes, false))
  }
  text[written] = u8(10)
  whole: []u8 = view(&text)
  line: []u8 = whole[u32(0):written + u32(1)]
  _ = write(c.Int(1), c.span_of(line))
}

emit_u32: (value: u32): () {
  word: [4]u8 = [4]u8{ u8_trunc_u32(value >> u32(24)), u8_trunc_u32(value >> u32(16)), u8_trunc_u32(value >> u32(8)), u8_trunc_u32(value) }
  emit_hex(view(&word))
}

main: (): i32 {
  lengths: [19]u32 = [19]u32{ 0, 1, 7, 55, 56, 57, 63, 64, 65, 111, 112, 113, 119, 120, 127, 128, 129, 1000, 4096 }
  buf: [4096]u8
  seed: u64 = u64(11400714819323198485)
  case: u32 = 0
  while case < u32(19) {
    count: u32 = lengths[case]
    true ? {
      b: [*]u8 = span(&buf)
      seed = lcg_fill(b, count, seed)
    }
    whole: []u8 = view(&buf)
    data: []u8 = whole[u32(0):count]
    // One-shot digest and checksum.
    digest: [32]u8
    true ? {
      d: [*]u8 = span(&digest)
      assert(hash.sha256(data, d))
    }
    emit_hex(view(&digest))
    emit_u32(hash.crc32c(data))
    // Incremental: 17-byte pieces exercise the partial block and the bulk
    // path together; the checksum splits once near the chunk boundary.
    state: hash.Sha256State = hash.sha256_init()
    at: u32 = 0
    while at < count {
      piece: u32 = count - at < u32(17) ? count - at | u32(17)
      state = hash.sha256_update(state, data[at:at + piece])
      at = at + piece
    }
    again: [32]u8
    true ? {
      a: [*]u8 = span(&again)
      assert(hash.sha256_final(state, a))
    }
    emit_hex(view(&again))
    split: u32 = count / u32(3)
    emit_u32(hash.crc32c_update(hash.crc32c_update(u32(0), data[u32(0):split]), data[split:count]))
    case = case + u32(1)
  }
  42
}
`

func crcShaExpected() string {
	var b strings.Builder
	for _, data := range crcShaCorpus() {
		digest := sha256.Sum256(data)
		crc := crc32.Checksum(data, crc32.MakeTable(crc32.Castagnoli))
		fmt.Fprintf(&b, "%s\n%08x\n%s\n%08x\n", hex.EncodeToString(digest[:]), crc, hex.EncodeToString(digest[:]), crc)
	}
	return b.String()
}

// Both builds must print the same lines, and those lines must be Go's.
func TestE2EStdlibCrcShaHardwareMatchesPortable(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/crc_sha_hw\noak 0.1.0\n",
		"main.oak": crcShaProgram,
	})
	want := crcShaExpected()
	for _, flags := range [][]string{nil, {"-DOAK_PORTABLE_INTRINSICS"}} {
		stdout, code, abnormal := buildAndRunFrom(t, "crc_sha_hw", New().WithPackageDir(root), flags...)
		if abnormal || code != 42 {
			t.Fatalf("flags %v: exit = (%d, abnormal=%v), want 42", flags, code, abnormal)
		}
		if stdout != want {
			t.Fatalf("flags %v: digests differ from Go's\n got:\n%s\nwant:\n%s", flags, stdout, want)
		}
	}
}

// The known answers hold on both paths: FIPS 180-4 "abc" and the RFC 3720
// CRC-32C check value for "123456789".
func TestE2EStdlibCrcShaVectorsBothPaths(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/crc_sha_vectors\noak 0.1.0\n",
		"main.oak": `package main
import("hash")
main: (): i32 {
  abc: [3]u8 = [3]u8{ 97, 98, 99 }
  digest: [32]u8
  true ? {
    d: [*]u8 = span(&digest)
    assert(hash.sha256(view(&abc), d))
  }
  assert(digest[0] == u8(186) && digest[1] == u8(120) && digest[2] == u8(22) && digest[3] == u8(191) && digest[31] == u8(173))
  digits: [9]u8 = [9]u8{ 49, 50, 51, 52, 53, 54, 55, 56, 57 }
  assert(hash.crc32c(view(&digits)) == u32(3808858755))
  // A 56-byte input takes the seven-word step exactly once with no tail.
  block: [56]u8
  i: u32 = 0
  while i < u32(56) { block[i] = u8_trunc_u32(i)
    i = i + u32(1)
  }
  assert(hash.crc32c(view(&block)) == hash.crc32c_update(hash.crc32c_update(u32(0), view(&block)[u32(0):u32(20)]), view(&block)[u32(20):u32(56)]))
  42
}
`,
	})
	for _, flags := range [][]string{nil, {"-DOAK_PORTABLE_INTRINSICS"}} {
		_, code, abnormal := buildAndRunFrom(t, "crc_sha_vectors", New().WithPackageDir(root), flags...)
		if abnormal || code != 42 {
			t.Fatalf("flags %v: exit = (%d, abnormal=%v), want 42", flags, code, abnormal)
		}
	}
}
