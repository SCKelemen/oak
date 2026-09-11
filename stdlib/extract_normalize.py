"""Extract the Unicode 17.0.0 normalization data into unicode17_normalize.json.

Reads the UCD files below from a directory (they are not committed; only the
extract is) and writes the compact extract that generate_normalize.py turns
into the tables in normalize.oak. Run from any working directory:

  python stdlib/extract_normalize.py <directory holding the UCD files>

  https://www.unicode.org/Public/17.0.0/ucd/UnicodeData.txt
  https://www.unicode.org/Public/17.0.0/ucd/DerivedNormalizationProps.txt
  https://www.unicode.org/Public/17.0.0/ucd/NormalizationTest.txt
    (checked in verbatim as testdata/NormalizationTest-17.0.0.txt)

Five tables (UAX #15, Unicode 17.0.0):

  props    sorted ranges (first, last, ccc | flags << 8) where flags are
           1 NFD_QC=N, 2 NFKD_QC=N, 4 NFC_QC=N, 8 NFC_QC=M, 16 NFKC_QC=N,
           32 NFKC_QC=M; scalars whose value is 0 are omitted.
  nfd      sorted (scalar, pool offset, length): the FULL canonical
           decomposition (recursive) of every scalar that has one, Hangul
           syllables excluded (they decompose algorithmically).
  nfkd     sorted (scalar, pool offset, length): the FULL compatibility
           decomposition of every scalar whose NFKD differs from its NFD
           (so a lookup falls back to the nfd table).
  pairs    sorted (first, second, composite): the primary composites — every
           scalar with a two-scalar canonical mapping that is not
           Full_Composition_Exclusion; canonical composition looks the raw
           mapping up by its two scalars.
  pool     the scalar sequences the nfd/nfkd entries index into.
  blocks   one flag per 256-scalar block (scalar >> 8): 1 when the block
           holds a scalar with a nonzero property, a decomposition, or a
           Hangul syllable; a scalar in a 0 block is its own normalization.
"""
import json
import sys
from pathlib import Path

VERSION = '17.0.0'
S_BASE, L_BASE, V_BASE, T_BASE = 0xAC00, 0x1100, 0x1161, 0x11A7
L_COUNT, V_COUNT, T_COUNT = 19, 21, 28
N_COUNT = V_COUNT * T_COUNT
S_COUNT = L_COUNT * N_COUNT

QC_FLAGS = {('NFD_QC', 'N'): 1, ('NFKD_QC', 'N'): 2, ('NFC_QC', 'N'): 4, ('NFC_QC', 'M'): 8,
            ('NFKC_QC', 'N'): 16, ('NFKC_QC', 'M'): 32}


def hangul_decomposition(cp):
    index = cp - S_BASE
    if not 0 <= index < S_COUNT:
        return None
    l = L_BASE + index // N_COUNT
    v = V_BASE + (index % N_COUNT) // T_COUNT
    t = T_BASE + index % T_COUNT
    return [l, v] if t == T_BASE else [l, v, t]


def props_lines(path):
    for line in Path(path).read_text().splitlines():
        line = line.split('#', 1)[0].strip()
        if not line:
            continue
        fields = [f.strip() for f in line.split(';')]
        lo, _, hi = fields[0].partition('..')
        yield int(lo, 16), int(hi or lo, 16), fields[1:]


def main(directory):
    directory = Path(directory)
    header = (directory / 'DerivedNormalizationProps.txt').read_text().splitlines()[0]
    assert VERSION in header, header
    ccc = {}
    canon = {}
    compat = {}
    for line in (directory / 'UnicodeData.txt').read_text().splitlines():
        fields = line.split(';')
        cp = int(fields[0], 16)
        if fields[3] != '0':
            ccc[cp] = int(fields[3])
        mapping = fields[5]
        if not mapping:
            continue
        if mapping.startswith('<'):
            compat[cp] = [int(x, 16) for x in mapping.split('>', 1)[1].split()]
        else:
            canon[cp] = [int(x, 16) for x in mapping.split()]
    excluded = set()
    flags = {}
    for lo, hi, values in props_lines(directory / 'DerivedNormalizationProps.txt'):
        if values[0] == 'Full_Composition_Exclusion':
            excluded.update(range(lo, hi + 1))
        elif len(values) >= 2 and (values[0], values[1]) in QC_FLAGS:
            bit = QC_FLAGS[(values[0], values[1])]
            for cp in range(lo, hi + 1):
                flags[cp] = flags.get(cp, 0) | bit

    def full(cp, use_compat, memo):
        if cp in memo:
            return memo[cp]
        hangul = hangul_decomposition(cp)
        if hangul is not None:
            mapping = hangul
        elif cp in canon:
            mapping = canon[cp]
        elif use_compat and cp in compat:
            mapping = compat[cp]
        else:
            memo[cp] = [cp]
            return memo[cp]
        out = []
        for x in mapping:
            out.extend(full(x, use_compat, memo))
        memo[cp] = out
        return out

    nfd_memo, nfkd_memo = {}, {}
    nfd_entries = {}
    for cp in sorted(canon):
        if hangul_decomposition(cp) is None:
            nfd_entries[cp] = full(cp, False, nfd_memo)
    nfkd_entries = {}
    for cp in sorted(set(canon) | set(compat)):
        if hangul_decomposition(cp) is not None:
            continue
        k = full(cp, True, nfkd_memo)
        if k != nfd_entries.get(cp, [cp]):
            nfkd_entries[cp] = k
    pool = []
    offsets = {}

    def intern(seq):
        key = tuple(seq)
        if key not in offsets:
            offsets[key] = len(pool)
            pool.extend(seq)
        return offsets[key]

    nfd = [[cp, intern(seq), len(seq)] for cp, seq in sorted(nfd_entries.items())]
    nfkd = [[cp, intern(seq), len(seq)] for cp, seq in sorted(nfkd_entries.items())]
    pairs = sorted([m[0], m[1], cp] for cp, m in canon.items()
                   if len(m) == 2 and cp not in excluded and hangul_decomposition(cp) is None)
    value = [0] * 0x110000
    for cp, c in ccc.items():
        value[cp] |= c
    for cp, f in flags.items():
        value[cp] |= f << 8
    table = []
    start = None
    for cp in range(0x110000 + 1):
        current = value[cp] if cp < 0x110000 else 0
        if start is not None and current != value[start]:
            table.append([start, cp - 1, value[start]])
            start = None
        if start is None and current != 0:
            start = cp
    # Blocks (scalar >> 8) holding any scalar the algorithm must look at: a
    # nonzero property, a decomposition, or a Hangul syllable. A scalar in an
    # unmarked block is a plain starter that is its own normalization.
    marked = set()
    for cp in list(ccc) + list(flags) + list(nfd_entries) + list(nfkd_entries):
        marked.add(cp >> 8)
    for cp in range(S_BASE, S_BASE + S_COUNT):
        marked.add(cp >> 8)
    blocks = [1 if b in marked else 0 for b in range(max(marked) + 1)]
    out = {'version': VERSION, 'blocks': blocks,
           'encoding': 'ccc | flags << 8; flags 1 NFD_QC=N 2 NFKD_QC=N 4 NFC_QC=N 8 NFC_QC=M 16 NFKC_QC=N 32 NFKC_QC=M',
           'props': table, 'nfd': nfd, 'nfkd': nfkd, 'pairs': pairs, 'pool': pool}
    target = Path(__file__).resolve().parent / 'unicode17_normalize.json'
    target.write_text(json.dumps(out, separators=(',', ':')) + '\n')
    print(len(table), 'prop ranges;', len(nfd), 'nfd;', len(nfkd), 'nfkd;', len(pairs), 'pairs;',
          len(pool), 'pool scalars ->', target)
    longest = max(len(s) for s in list(nfd_entries.values()) + list(nfkd_entries.values()))
    print('longest decomposition', longest)


if __name__ == '__main__':
    main(sys.argv[1])
