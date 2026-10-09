# Pinned Arm decoder clause classification

This is a kernel-checked classifier for the complete, ordered **embedded
AArch64 clause region**. It is not execution of Sail's full generated decoder,
not a verified Sail parser, and not a proof of general Sail/ASL-to-Lean
faithfulness. The standalone classifier retains a complete-file-to-clause extraction
boundary. The downstream [complete-source partition](DECODER_PARTITION.md)
now checks the exact ordered byte coverage in Lean, against an independently
copied input; external file acquisition and Sail parser meaning remain explicit.

## Input and provenance

The unmodified `decoder_classification_source.sail` is
`arm-v8.5-a/model/aarch_decode.sail` from
[rems-project/sail-arm at 1bf2e557](https://github.com/rems-project/sail-arm/blob/1bf2e5574ba9d704639a28401b6a387dcb113cae/arm-v8.5-a/model/aarch_decode.sail).
Its 833,374 bytes have SHA256
`61a57876f4ac9b10849bf90bcd9bb74f6336737015cb3a5b1e1ebd85f11e6ae7`.
The 917 AArch64 clause bodies occupy 431,483 bytes. Their 916 single-LF
separators bring the complete suffix to 432,399 bytes.
Their SEE indices are 1026 through 1942, in that order.

`decoder_classification.py` checks the complete pin and exact prefix pin,
accounts for every region byte, reconstructs the entire file from the prefix,
all raw clause chunks and separators (including trailing whitespace), and
compares it byte-for-byte with the pinned input. It fails on unknown region
text, malformed headers/bodies, missing/extra/duplicate/reordered clauses,
changed guards/writes, invalid widths and argument-order changes. It also
checks every generated certificate module against deterministic regeneration.

Those Python checks alone are **trusted extraction checks**, not kernel proofs
of parser completeness or of the absence of other Sail declarations. The
downstream partition proof independently checks their exact byte coverage;
it still does not prove Sail parser completeness. The source pin,
complete-file inventory and retained original file make the boundary
reviewable; they do not erase it.

## What Lean proves

`Oak.ArmDecoderClassification.Checker` is fixed code. An untrusted certificate
provides pattern segments, SEE index, field declarations and a callee name.
The checker validates positive segment widths totaling 32 bits, binary digits,
field bounds/widths, singleton syntax, identifiers and binder distinctness. It
rejects `op_code`, `SEE`, reserved keywords and field/callee collisions.

The checker reconstructs **every chunk of the complete clause**, including
punctuation and whitespace, the strict SEE guard, SEE write, field declarations,
callee and argument order. Equality is checked before a certificate is
accepted. `checked_bytes` then proves equality of the concatenated complete
clause strings by congruence, avoiding expensive large-string normalization.
The raw source chunks and the certificate are separate data inputs.

Each `CheckedRow` carries both the whole-clause check and a kernel proof that
its numeric mask/value/index were derived from that same certificate.
`table_bound` relates the ordered table to those checked entries, and
`table_indices` fixes the full sequence 1026..1942. The first matching clause and
unique matching eligible clause are proved for SEE=-1:

| Word | Instruction class | SEE index | Zero-based position |
| --- | --- | --- | --- |
| `0x0a010000` | AND |1845|819|
| `0x2a010000` | ORR |1858|832|
| `0x4a010000` | EOR |1788|762|
| `0xd65f03c0` | RET |1522|496|

`ByteBinding.function_bytes_classified` uses the existing
`Oak.AArch64BitwiseFunction.functionBytes` and `takeWord` definitions to bind
each exact eight-byte artifact to the corresponding two ordered choices. It
rejects short/trailing bytes. A mandatory compiler test passes the original
`mix: (a: u32, b: u32): u32 = a & b` source (and OR/XOR variants) through the
actual compiler, extracts the complete relocation-free ELF function, and proves
that the returned bytes equal `functionBytes` before applying this binding.
That compiler/ELF extraction remains executable correspondence evidence, not a
universal compiler or ELF-loader proof.

These are the words in the existing 8-byte bitwise/RET slice. The classifier
interprets the admitted bit-pattern and literal-slice syntax; it does not
execute any of the 359 distinct terminal callees. Argument-list controls cover
the four words, including the changed argument caused by changing Rd.

Generated certificate proofs use `rfl` kernel reduction; small negative controls
use `decide_cbv` with kernel-checked proof terms in Lean 4.33.1. The mandatory audit permits only
`propext`, `Classical.choice` and `Quot.sound`; native/custom/sorry axioms are
rejected. The Python generator and its computed masks are not proof oracles.

## Remaining execution boundary

The existing scalar model contains four selected clauses in a different order;
it remains explicitly selected-clause execution. This classifier does not turn
it into a full generated decoder theorem. It has no register-read action or
failure state: SEE=-1 is an explicit classifier argument, not a proof of an
initialized architectural register. Feature gates, Undefined/SEE exceptions
inside callees, unmatched generated-decoder behavior, callbacks, fetch, loader,
reset reachability and BTI-enabled instruction execution remain outside it.

The separate existing concrete return theorem still requires the nondefault
`v85=false` profile. No production verified-authority label is enabled.

The attempted intact 917-clause generated export is not used here. The default
pipeline exceeded the bounded memory budget after guard expansion; the
supported `--lean-matchbv` experiment was rejected by the unchanged no-shadow
guard. No guard exemption, Sail source rewrite or Lean-support syntax change
was adopted.

## Reproduce and check

With the pinned source checkout and Lean 4.33.1 installed:

```sh
python3 spec/sail/decoder_classification.py
python3 spec/sail/test_decoder_classification.py
python3 spec/sail/check_decoder_classification.py --build-dir /tmp/oak-arm-decoder-check
python3 spec/sail/check_decoder_byte_binding.py --build-dir /tmp/oak-arm-decoder-check
```

To regenerate the untrusted certificates, use
`python3 spec/sail/decoder_classification.py --generate`, then run all checks.
The `Sail bridges and oracles` CI lane requires the full source check, negative
controls, serial kernel validation and standard-only closure audit. It preserves
per-module timing/RSS, hashes and logs as the `arm-decoder-classification`
artifact. Each Lean process uses one worker and stops at 30 seconds/1 GiB RSS or
an available-memory floor of 1.5 GiB; no failed/partial batch counts as validation.
Eight-clause batches keep memory bounded. Successful local receipts may avoid
rebuilding unchanged modules, with source, compiled-dependency, Lean and olean hashes checked;
the hosted lane starts from an empty build directory.

These modules are validated by this dedicated mandatory gate rather than added
to the ordinary core library's default imports, avoiding uncontrolled parallel
compilation of 115 certificate batches.
