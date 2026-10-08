# Experimental no-shadow export profile

This is a restrictive local experiment, not a general Sail exporter correction
or replacement for Oak's official generator pin.

Official base: `3b7af38d66466ecadad563158b07ce2f82fe05da`.
Experimental source commit: `8989869c9e74cec412a3dbd79d134cd97b8150c9`.
The full patch, executable and Lean-plugin hashes are in `profile.json`.
The source commit is local to the validation checkout, not an upstream release.

The first eleven-line nested-let update patch fixed the original 55-versus-63
reproducers but was rejected: source `shadow_case(false,0)=5` became generated
99. The transformation inserted a reference beneath an inner same-name binder.
That rejected patch and kernel counterexample remain preserved in the local
audit artifact; do not use it alone.

The checked profile gates the transformation at the beginning of shared
`rewrite_ast_remove_e_assign`, before any mutations or loop-spec insertion.
It checks typed outer lexical environments, rejects shadowing and duplicate
pattern binders, and fails closed on unsupported patterns/internal binders,
residual introducing assignments and local reference aliases. It does not
rename pinned sources, relax query behavior, or hand-edit generated Lean.
Direct registered rewrite calls are guarded too. This guard is a typed-AST
admission check; it is not a proof of source/export equivalence.

Negative fixtures cover immutable, nested, tuple-pattern, loop and function
parameter shadows, plus an outer update before shadowing. Explicit mutable
redeclaration is already rejected by Sail's typechecker. Ordinary typed
reassignment is a separate admitted case. Positive fixtures cover non-unit
results, early returns, register effects and assertion failures. Raw-generated
kernel proofs are checked without `sorryAx` or custom correctness axioms.

The existing scalar/STR/primitive exports fail this guard on legitimate
shadowing idioms. Keep those official exports unchanged; do not add file-specific
exceptions. A broader future profile needs a separate capture argument.

## Reproduction

Build the official source plus exactly `no-shadow.patch`, keeping this tool
separate from the official release. The validated environment used official
OCaml 5.3.0 Debian packages, Dune 3.21.1, Ott 0.34 and optional linenoise 1.5.1.
No security/sandbox settings were disabled. Executable hashes are specific to
that recorded build; another build requires separately reviewed provenance.

Set `OAK_RETURN_SAIL` to the experimental executable, `SAIL_PLUGIN_DIR` to its
Lean-plugin directory, `SAIL_DIR` to its source root, and
`OAK_LEAN_SAIL_SUPPORT` to Oak's pinned/patched Lean-Sail support checkout.
Keep `SAIL` (or `sail` on PATH) pointed at the unchanged official 0.20.2 release.
Then run:

```
python3 spec/sail/repros/guarded_mutation/guarded_profile/check.py --output-dir /tmp/guarded-profile-check
python3 spec/sail/return_execution_regen.py --regenerate
```

The first command verifies hashes before execution, uses the official source
evaluator, preserves raw outputs, checks rejection diagnostics and runs Lean
proofs. REPL commands can report errors with process status zero, so the direct
entry regression checks the diagnostic itself. The optional REPL dependency is
required for that check; a missing REPL is not counted as rejection evidence.

The source REPL retains its prior command state after a failing command even
though `Interpreter.Fail` retains a failure frame. Subsequent REPL register reads
therefore cannot establish source failure-state correspondence. The error-state
proof here is explicitly about the generated model.

## Reproducible source+patch build lane

The existing `Sail bridges and oracles` CI job now rebuilds the generator in an
isolated prefix from official Sail base plus exactly `no-shadow.patch`.
`toolchain-lock.json` fixes every downloaded Debian package and Dune/Ott archive
by URL and SHA256. Packages are extracted with `dpkg-deb`; maintainer scripts are
not installed/run. No opam switch, sandbox-disable option, system security change,
or replacement of the official Sail installation is used. The runner supplies
ordinary C build tools/libgmp; binary reproducibility across different host C
libraries is not claimed. Generated Lean bytes must still match exactly.

```
python3 spec/sail/repros/guarded_mutation/guarded_profile/build.py --workdir /tmp/oak-guarded-build
source /tmp/oak-guarded-build/env.sh
export OAK_LEAN_SAIL_SUPPORT=/absolute/path/to/pinned/lean-sail
python3 spec/sail/return_execution_regen.py --regenerate
python3 spec/sail/repros/guarded_mutation/guarded_profile/check.py --output-dir /tmp/oak-guarded-tests
```

The script requires an empty build directory and Linux x86_64 with glibc >=2.38
(the CI runner is Ubuntu24.04). Optional download/source caches are only a local
optimization; all content/source pins are checked. CI fetches the official source
and creates its own receipt in the same job, not from an uploaded receipt.

`OAK_RETURN_BUILD_RECEIPT` selects this distinct source-build profile. Verification
checks official source HEAD, exact tracked patch/no extra sources, dependency
archive hashes, extracted-prefix digest, builder/lock identity and the newly built
executable/plugin hashes. It also binds the environment to that checkout. A
receipt is provenance metadata, not a proof of source semantics. The old exact
local executable/plugin hashes remain enforced when no build receipt is selected.

The job saves the receipt and build/regeneration/regression logs. Until the lane
passes on the proposed commit, hosted reproduction remains pending and merge must
stay on hold. Existing official scalar/STR/primitive exports remain unchanged.
