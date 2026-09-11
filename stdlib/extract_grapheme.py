"""Extract the Unicode 17.0.0 grapheme-segmentation properties into unicode17_grapheme.json.

Reads the UCD files below from a directory (they are not committed; only the
extract is) and writes the compact extract that generate_grapheme.py turns into
the range table in grapheme.oak. Run from any working directory:

  python stdlib/extract_grapheme.py <directory holding the UCD files>

  https://www.unicode.org/Public/17.0.0/ucd/auxiliary/GraphemeBreakProperty.txt
  https://www.unicode.org/Public/17.0.0/ucd/emoji/emoji-data.txt
  https://www.unicode.org/Public/17.0.0/ucd/DerivedCoreProperties.txt
  https://www.unicode.org/Public/17.0.0/ucd/auxiliary/GraphemeBreakTest.txt
    (checked in verbatim as testdata/GraphemeBreakTest-17.0.0.txt)

One combined range table: each scalar's value is

  gcb | (incb << 8) | (pictographic << 10)

with gcb the Grapheme_Cluster_Break value (UAX #29 Table 2, numbered below),
incb the Indic_Conjunct_Break value (0 None, 1 Consonant, 2 Extend, 3 Linker)
and pictographic the Extended_Pictographic flag. Scalars whose value is 0
(Other, no InCB, not pictographic) are omitted, so the table is the set of
scalars that any segmentation rule can tell apart from a plain letter.
"""
import json
import sys
from pathlib import Path

GCB = {'Other': 0, 'CR': 1, 'LF': 2, 'Control': 3, 'Extend': 4, 'ZWJ': 5,
       'Regional_Indicator': 6, 'Prepend': 7, 'SpacingMark': 8, 'L': 9, 'V': 10,
       'T': 11, 'LV': 12, 'LVT': 13}
INCB = {'None': 0, 'Consonant': 1, 'Extend': 2, 'Linker': 3}
VERSION = '17.0.0'


def ranges(path, want=None):
    for line in Path(path).read_text().splitlines():
        line = line.split('#', 1)[0].strip()
        if not line:
            continue
        fields = [f.strip() for f in line.split(';')]
        span, values = fields[0], fields[1:]
        if want is not None and values[:len(want)] != want:
            continue
        lo, _, hi = span.partition('..')
        yield int(lo, 16), int(hi or lo, 16), values


def main(directory):
    directory = Path(directory)
    header = (directory / 'GraphemeBreakProperty.txt').read_text().splitlines()[0]
    assert VERSION in header, header
    value = [0] * 0x110000
    for lo, hi, (gcb,) in ranges(directory / 'GraphemeBreakProperty.txt'):
        for cp in range(lo, hi + 1):
            value[cp] |= GCB[gcb]
    for lo, hi, (_, incb) in ranges(directory / 'DerivedCoreProperties.txt', ['InCB']):
        for cp in range(lo, hi + 1):
            value[cp] |= INCB[incb] << 8
    for lo, hi, _ in ranges(directory / 'emoji-data.txt', ['Extended_Pictographic']):
        for cp in range(lo, hi + 1):
            value[cp] |= 1 << 10
    table = []
    start = None
    for cp in range(0x110000 + 1):
        current = value[cp] if cp < 0x110000 else 0
        if start is not None and current != value[start]:
            table.append([start, cp - 1, value[start]])
            start = None
        if start is None and current != 0:
            start = cp
    out = {'version': VERSION, 'encoding': 'gcb | incb << 8 | pictographic << 10',
           'gcb': GCB, 'incb': INCB, 'ranges': table}
    target = Path(__file__).resolve().parent / 'unicode17_grapheme.json'
    target.write_text(json.dumps(out, separators=(',', ':')) + '\n')
    print(len(table), 'ranges written to', target)


if __name__ == '__main__':
    main(sys.argv[1])
