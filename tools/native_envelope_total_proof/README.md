# Total native envelope proof gate

Run from the repository root with official pinned Lean 4.33.1:

```sh
OAK_REQUIRE_SELFHOST_IMAGE_PRODUCERS=1 go test ./compiler \
  -run '^TestLeanNativeBitwiseEnvelopeTotalProof$' -count=1
python3 -m unittest discover -s tools/native_envelope_total_proof -p 'test_*.py'
```

The new Go root first invokes the unchanged complete-source extraction check,
then rebuilds all 46 local transitive Lean modules in a new temporary directory.
Every Lean invocation uses `-j1 -t0 -M3000` and a 900-second timeout; the Go test
allows 20 minutes. No candidate `.olean` cache is searched. Imported sources are
hashed before and after the build. Official release Init/Lean/Std modules are the
only reusable dependencies in this gate.

The committed audit must exactly equal the independently listed 56 theorem roots.
The retained 30 successful-domain roots are supplemented with the total name
scan, four-byte inversion, startup equivalence, actual refusal branches, total
outcome, and 12 controls. Only `propext`, `Quot.sound`, and `Classical.choice` are
allowed. Missing, duplicate, extra, custom, admitted, and native-computation axiom
reports are rejected. A negative control explicitly rejects a native
`bv_decide`-style axiom; the actual proof uses ordinary bit extensionality and
kernel-checked arithmetic instead of that tactic.

The required `selfhost-image-producers` inventory now has 218 names: every prior
217 name is retained and the new total-outcome gate is mandatory. The separate
complete-tuple admission inventory is unchanged.

See [the total-outcome specification](../../docs/spec/native-envelope-total-outcome.md).
