#!/usr/bin/env python3
"""Regenerate the per-symbol lookup tables in stdlib/encoding.oak.

The file carries one region delimited by

    // BEGIN GENERATED (stdlib/generate_codec_tables.py)
    ...
    // END GENERATED

whose contents this script rewrites in place. CI runs the script and fails
on a diff, so the committed tables are exactly what the code below
produces. Nothing is downloaded; every table is computed from its
definition (the RFC 4648 base64 and base32 alphabets and the hexadecimal
digits).
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
    if rewrite(ROOT / "encoding.oak", encoding_region()):
        print("regenerated")
    return 0


if __name__ == "__main__":
    sys.exit(main())
