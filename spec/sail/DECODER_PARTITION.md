# Complete original Arm source byte partition

`Oak.ArmDecoderPartition.Data.complete_source` relates an independently copied
complete input to the same 917 `CheckedRow` entries used by the classifier:

- Complete input: 833,374 bytes.
- Prefix: 400,975 bytes.
- Clause bodies: 431,483 bytes.
- Separators: 916 single LF bytes, with no final separator or extra suffix.
- The resulting suffix is 432,399 bytes, including its separators.

The original file is `arm-v8.5-a/model/aarch_decode.sail` at
[rems-project/sail-arm 1bf2e557](https://github.com/rems-project/sail-arm/blob/1bf2e5574ba9d704639a28401b6a387dcb113cae/arm-v8.5-a/model/aarch_decode.sail),
SHA256 `61a57876f4ac9b10849bf90bcd9bb74f6336737015cb3a5b1e1ebd85f11e6ae7`.
The original licensed file remains in `decoder_classification_source.sail`.

## Independent input and kernel binding

`copy_decoder_source_pages.py` reads the original file directly, without
importing the clause inventory or reconstructing clauses. It divides bytes into
fixed 1 KiB pages and fixed 128-byte little-endian natural literals. Lean's
fixed `unpack` definition interprets those literals as octets. A separate exact
comparison decodes every literal back to the original bytes, checks page order,
word range and zero padding, and rejects missing or additional input modules.
The external-file-to-literal acquisition, byte comparison and source pin remain
explicit executable checks, not a Lean theorem about an external filesystem or
a cryptographic hash oracle.

The untrusted partition generator proposes page cuts and existing-clause links.
`cutBytes_cover` retains the entire final tail. Page equations prove exact
coverage of the independently copied pages. Clause equations bind those same
cells to the existing raw chunks' UTF-8 bytes. The complete ordered cell-list
equality and generic append/flatten laws prove the full input is exactly the
prefix followed by the 917 raw clauses with the prescribed separators. The
prefix length fixes the boundary. No gap, duplicated occurrence, omitted byte,
or trailing suffix can be accepted unless that exact concatenation still equals
the complete input. These are byte-concatenation facts, not a separate claim
about identities of equal-valued byte positions.

`same_entries` binds the sequence directly to the existing `embedded` value;
`same_table` derives the existing classifier table. The existing exact eight-byte
function artifact and its classification are retained. A required actual
compiler/ELF byte pin imports this complete-source proof graph. The prior 917
semantic certificates are reused, without restating their checker or grammar.

## Prefix text and remaining semantic limits

The prefix contains exactly one raw ASCII `decode64` occurrence, in the original
newline-anchored `val decode64` declaration. A right-to-left scanner carries
seven lookahead bytes between pages. `scan_exact` proves that its count equals
counting every eight-byte start, including cross-page occurrences. An exact
slice proves the original declaration line, the prefix ends on LF, and the next
bytes are the first checked clause header.

This is a deliberately restricted textual property. It is not Sail lexing or
parsing, a proof about obfuscated declarations or comments, general Sail/ASL
export faithfulness, or execution of the full generated decoder and its 359
callees. Fetch, loader, reset reachability and BTI-enabled instruction execution
remain outside the claim. The existing nondefault `v85=false` composed success
profile remains unchanged. No production verified-authority label changes.

## Reproduction and resource bounds

The existing classification gate runs first. Then run:

```sh
python3 spec/sail/test_decoder_partition.py
python3 spec/sail/check_decoder_partition.py \
  --source external/sail-arm/arm-v8.5-a/model/aarch_decode.sail \
  --classification-dir /tmp/oak-arm-decoder-classification \
  --build-dir /tmp/oak-arm-decoder-partition --jobs 2
OAK_REQUIRE_ARM_PARTITION=1 \
  OAK_ARM_PARTITION_LIB=/tmp/oak-arm-decoder-partition \
  go test ./compiler -run '^TestArmDecoderPartitionCompilerBytes$' -count=1 -v
```

At most two Lean processes run concurrently, each with a 30-second and 1 GiB RSS
ceiling. Launches pause below 2 GiB available system memory; crossing a ceiling
stops only the runner's own process. Dependency stages remain ordered. Receipts
bind the exact source, every transitive compiled import, Lean identity and
successful result. They are local acceleration only. Hosted CI builds fresh,
audits every public theorem for standard-only axioms, and retains timing/RSS,
source/object hashes and logs. A failed or partial run never writes a completed
validation result. The completed local graph contains 323 modules and 2,182
standard-only theorem closures. The largest aggregate completed in 4.12 seconds
with 928,364 KiB peak RSS; the slowest page-scan batch took 14.07 seconds.
The required hosted step has a separate 45-minute budget and uses a fresh build
directory. Prior classifier and core cache inventories are checked in full, and
all partition receipts are rechecked against current sources and compiled imports
before a completed result is written.

Controls reject removal, duplication, reordering, omitted/injected separators,
earlier/later prefix boundaries, gaps/overlaps, extra suffixes, wrong independent
bytes and malformed packed literals. Cross-page marker and declaration-newline
controls ensure scanner state cannot be reset independently for each page.
