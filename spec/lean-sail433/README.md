# Concrete RV64 decoder/body projection in one Lean kernel

This bounded project uses Lean 4.33.1 for both Oak and the pinned generated
Sail model. It does not compose incompatible 4.29/4.33 compiled proofs by trust.
The existing `../lean-sail` project and its 4.29 pin remain unchanged.

## Reproduce

First obtain the already-verified generated export using the existing
`../lean-sail/README.md` bootstrap or the source-artifact workflow. Pins:
Sail `dba5f007`, sail-riscv `497209b9298bf11b040e000095fe24c51a598a1d`,
lean-sail `079463134b9c50450b8393e1566a09fc492a34d9` (`v5`). Then:

```sh
python3 spec/lean-sail433/prepare.py --generated /path/to/Lean_RV64D
cd spec/lean-sail433
lake update
lake build OakSailComposition OakSailFullDispatch OakSailBridge.BitwiseDispatchAgreement
python3 audit.py
```

The preparation script verifies the input against the separately recorded
upstream artifact provenance and exact source hashes; it does not regenerate
Sail or prove generation correct. It also checks the original toolchain and
declared lean-sail pin, records every copied source's SHA256, and verifies
byte-identical source copies. Only the copies' toolchain
and dependency paths change. No 4.29 `.olean` files are copied or consumed.
The project also needs the source/body/framed proof stack in `../lean`.

The integration uses the committed default `lakefile.toml` and the source/body
prerequisites in `../lean`; no `lakefile.local.toml` override is needed.

The required Sail CI lane retains its pinned source checkout/generation and
original 4.29 checks, then runs this preparation, the bounded 4.33 targets, and
`audit.py`. `export-provenance.json` records upstream artifact 11540095028 from
run 37749261545, its outer ZIP digest, original pins, all 164 model/configuration
file hashes. The separate `support_source` record pins the 9 Sail library/configuration
files to upstream lean-sail git revision `079463134b9c50450b8393e1566a09fc492a34d9`;
those hashes were taken from that commit and checked against the local checkout,
not extracted from the model ZIP. `verify_export.py` requires both exact source
inventories and bytes before preparation, including
on a restored build cache. It does not depend on an expiring artifact download
at CI runtime or claim exporter correctness. Updating external sources requires
an explicit provenance/hash review, not merely editing a version string.

## What is proved

- The unchanged external `encdec_backwards` decodes the exact AND/OR/XOR and
  RET words, and all seven other words of the actual 36-byte compiler wrapper.
  Its eager Zihintpause/Zicfilp queries are retained, not optimized away by hand.
- Concrete mapped-register states execute the generated per-instruction bitwise body and RET
  successfully. The result is written to x10, and the actual JALR target is
  written to nextPC. All other state, including memory and PC, is unchanged.
- The profile supplies Machine privilege, mseccfg=0, RV64I misa with compressed
  instructions disabled, x10/x11 inputs, ra, and nextPC. The bit-cleared return
  target must satisfy IALIGN=32. These are hypotheses about concrete state,
  not assumptions that decoding or execution is successful.
- Original source bytes are independently parsed by the restricted checker.
  Their named meaning and existing typed-expression meaning compose, in the
  same kernel, with the external execution of the selected instruction bodies.
- Source/complete-wrapper admission binds all 36 bytes; the projection selects
  the actual bitwise word at offset 16 and RET at offset 32. Malformed projected
  byte lengths and source/operator mutation cases are checked.

## What is still separate

The two-body driver supplies decoded words and invokes generated instruction
bodies. It is not the generated fetch/step loop; PC is not ticked, and RET's
architectural effect is reported as nextPC. No fetch/cache/code-immutability,
loader, boot configuration, or OS syscall behavior is proved.

Complete 36-byte decoding is proved. Complete 36-byte **external execution is
not**: the seven omitted instructions are not semantically erased. In
particular the actual Sail virtual/physical-memory path for SD/LD has not been
related to Oak's flat frame memory, address translation, PMP, permissions,
faults, or access events. The existing internal framed proof and its explicit
96-byte mapped-frame contract remain separate. No native verified verdict or
compiler authority is enabled here.

## Trust and build audit

`audit.py` checks the public theorem closures against the explicit
`axiom-allowlist.json`. The broader full-dispatch parameter set is audited
separately; new or native-evaluation dependencies fail the audit.

The successful new theorem closures contain standard Lean axioms plus the
pinned export's existing `sys_enable_experimental_extensions : Unit → Bool`
platform parameter (`LeanRV64D/RiscvExtras.lean:41`). No value of that parameter
is assumed; the normalized supported paths do not depend on it. No native
`bv_decide`/`native_decide` evaluation axioms or `sorryAx` are admitted.

`OakSailFullDispatch.accepted_source_full_projection` additionally proves the
same successful two-body result through the full generated dispatcher. Its
broader closure is audited separately, with 72 opaque primitive parameters plus
the Boolean platform parameter and standard Lean axioms.

`BitwiseDispatchAgreement.lean` separately proves by kernel reduction that the
full generated `execute` dispatcher chooses exactly these bodies. Referencing
that unrestricted dispatcher adds the pinned export's opaque soft-float,
reservation, randomness and terminal-I/O primitives to the transitive axiom
closure, including primitives in unused branches. They are model parameters,
not assumed successful outcomes. This broader closure must be included in any
claim using the full-dispatcher agreement; splitting the files does not remove
it from that claim. The narrow driver rejects other instruction classes.

The required unchanged Sail/library/ISA dependencies build under 4.33.1. A
separate attempt to build **all**135 generated targets reached the optional
`RvfiDii` debugging interface and exited 137. That full-model build is not
reported as passing. The bounded import graph used by this project excludes
that interface and builds the actual decoder/executor used in the theorems.
