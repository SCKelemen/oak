#!/usr/bin/env python3
"""Regenerate the lookup tables and the unrolled SHA-256 rounds in
stdlib/encoding.oak and stdlib/hash.oak.

Each file carries one region delimited by

    // BEGIN GENERATED (stdlib/generate_codec_tables.py)
    ...
    // END GENERATED

whose contents this script rewrites in place. CI runs the script and fails
on a diff, so the committed tables are exactly what the code below
produces. Nothing is downloaded; every table is computed from its
definition (RFC 4648 alphabets, RFC 3986 hex digits, the CRC-32C
polynomial 0x82F63B78 reflected, FIPS 180-4 section 6.2.2).
"""

from __future__ import annotations

import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent
BEGIN = "// BEGIN GENERATED (stdlib/generate_codec_tables.py)"
END = "// END GENERATED"


def oak_array(name: str, element: str, values: list[int], per_line: int) -> str:
    lines = [f"{name}: [{len(values)}]{element} = [{len(values)}]{element}{{"]
    for start in range(0, len(values), per_line):
        chunk = values[start : start + per_line]
        lines.append("  " + ", ".join(str(v) for v in chunk) + ",")
    lines[-1] = lines[-1].rstrip(",")
    lines.append("}")
    return "\n".join(lines)


def value_table(alphabet: bytes, sentinel: int, lowercase: bool = False) -> list[int]:
    table = [sentinel] * 256
    for value, unit in enumerate(alphabet):
        table[unit] = value
        if lowercase and 65 <= unit <= 90:
            table[unit + 32] = value
    return table


def encoding_region() -> str:
    hex_lower = b"0123456789abcdef"
    hex_upper = b"0123456789ABCDEF"
    hex_values = value_table(hex_upper, 16, lowercase=True)
    b64_std = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
    b64_url = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"
    b32_std = b"ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"
    b32_hex = b"0123456789ABCDEFGHIJKLMNOPQRSTUV"
    parts = [
        "// Per-symbol tables. A `_SYMBOLS` table maps a value to its character; a",
        "// `_VALUES` table maps every byte to its value or to the sentinel one past",
        "// the alphabet (16, 64, 32), which sets a bit no valid value has, so the OR",
        "// of a run of table values is below the sentinel exactly when every byte",
        "// was in the alphabet. Base32 accepts lowercase letters.",
        oak_array("HEX_LOWER_SYMBOLS", "u8", list(hex_lower), 16),
        oak_array("HEX_UPPER_SYMBOLS", "u8", list(hex_upper), 16),
        oak_array("HEX_VALUES", "u8", hex_values, 16),
        oak_array("BASE64_STD_SYMBOLS", "u8", list(b64_std), 16),
        oak_array("BASE64_URL_SYMBOLS", "u8", list(b64_url), 16),
        oak_array("BASE64_STD_VALUES", "u8", value_table(b64_std, 64), 16),
        oak_array("BASE64_URL_VALUES", "u8", value_table(b64_url, 64), 16),
        oak_array("BASE32_STD_SYMBOLS", "u8", list(b32_std), 16),
        oak_array("BASE32_HEX_SYMBOLS", "u8", list(b32_hex), 16),
        oak_array("BASE32_STD_VALUES", "u8", value_table(b32_std, 32, lowercase=True), 16),
        oak_array("BASE32_HEX_VALUES", "u8", value_table(b32_hex, 32, lowercase=True), 16),
    ]
    return "\n".join(parts)


def crc32c_table() -> list[int]:
    poly = 0x82F63B78
    first = []
    for unit in range(256):
        crc = unit
        for _ in range(8):
            crc = (crc >> 1) ^ (poly if crc & 1 else 0)
        first.append(crc)
    tables = [first]
    for _ in range(1, 8):
        prev = tables[-1]
        tables.append([(prev[b] >> 8) ^ first[prev[b] & 0xFF] for b in range(256)])
    return [v for table in tables for v in table]


def sha256_compress() -> str:
    lines = [
        "// One compression of the 64-byte block at `at` in `block` into the eight",
        "// working words (FIPS 180-4 section 6.2.2). Fully unrolled: every schedule",
        "// and round-constant index is a literal the C compiler bounds-checks at",
        "// compile time, so only the sixty-four block loads carry a runtime check.",
        "// The eight working variables rotate roles each round instead of moving.",
        "sha256_compress: (h: [8]u32, block: []u8, at: u32): [8]u32 {",
        "  w: [64]u32",
    ]
    for i in range(16):
        a = i * 4
        lines.append(
            f"  w[{i}] = (u32(block[at + u32({a})]) << u32(24)) | (u32(block[at + u32({a + 1})]) << u32(16))"
            f" | (u32(block[at + u32({a + 2})]) << u32(8)) | u32(block[at + u32({a + 3})])"
        )
    for i in range(16, 64):
        lines.append(f"  s0_{i}: u32 = rotr32(w[{i - 15}], u32(7)) ^ rotr32(w[{i - 15}], u32(18)) ^ (w[{i - 15}] >> u32(3))")
        lines.append(f"  s1_{i}: u32 = rotr32(w[{i - 2}], u32(17)) ^ rotr32(w[{i - 2}], u32(19)) ^ (w[{i - 2}] >> u32(10))")
        lines.append(f"  w[{i}] = w[{i - 16}] + s0_{i} + w[{i - 7}] + s1_{i}")
    names = ["a", "b", "c", "d", "e", "f", "g", "hh"]
    for k, name in enumerate(names):
        lines.append(f"  {name}: u32 = h[{k}]")
    for i in range(64):
        A, B, C, D, E, F, G, H = (names[(k - i) % 8] for k in range(8))
        lines.append(
            f"  t1_{i}: u32 = {H} + (rotr32({E}, u32(6)) ^ rotr32({E}, u32(11)) ^ rotr32({E}, u32(25)))"
            f" + (({E} & {F}) ^ ((^{E}) & {G})) + SHA256_K[{i}] + w[{i}]"
        )
        lines.append(
            f"  t2_{i}: u32 = (rotr32({A}, u32(2)) ^ rotr32({A}, u32(13)) ^ rotr32({A}, u32(22)))"
            f" + (({A} & {B}) ^ ({A} & {C}) ^ ({B} & {C}))"
        )
        lines.append(f"  {D} = {D} + t1_{i}")
        lines.append(f"  {H} = t1_{i} + t2_{i}")
    lines.append("  [8]u32{ h[0] + a, h[1] + b, h[2] + c, h[3] + d, h[4] + e, h[5] + f, h[6] + g, h[7] + hh }")
    lines.append("}")
    return "\n".join(lines)


def hash_region() -> str:
    parts = [
        sha256_compress(),
        "",
        "// CRC-32C slicing-by-8: table k (at offset k * 256) is the CRC of a byte",
        "// followed by k zero bytes, so eight table reads advance the checksum by",
        "// eight input bytes (Kounavis and Berry, 2005). 8 KiB of constants.",
        oak_array("CRC32C_TABLE", "u32", crc32c_table(), 8),
    ]
    return "\n".join(parts)


def rewrite(path: pathlib.Path, region: str) -> bool:
    text = path.read_text()
    begin = text.index(BEGIN) + len(BEGIN)
    end = text.index(END, begin)
    updated = text[:begin] + "\n" + region + "\n" + text[end:]
    if updated != text:
        path.write_text(updated)
        return True
    return False


def main() -> int:
    changed = False
    changed |= rewrite(ROOT / "encoding.oak", encoding_region())
    changed |= rewrite(ROOT / "hash.oak", hash_region())
    if changed:
        print("regenerated")
    return 0


if __name__ == "__main__":
    sys.exit(main())
