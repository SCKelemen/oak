# Complete Wasm total-outcome source gate

From the repository root, with the official Lean 4.33.1 `lake` selected:

```sh
python3 -m unittest discover -s tools/wasm_module_proof -p test_check.py
python3 -m unittest discover -s tools/wasm_module_total_proof -p test_check.py
python3 tools/wasm_module_total_proof/check.py --lake /path/to/lean-4.33.1/bin/lake
```

The runner rebuilds all 20 local dependencies from source in a fresh temporary
directory, using `-j1 -t0 -M2048 -DwarningAsError=true`. Only the installed
toolchain's standard dependencies are reused. Both committed theorem
inventories must match exactly and every reported axiom must belong to
`propext`, `Classical.choice`, or `Quot.sound`. Both the unchanged successful
module controls and the new total-outcome controls are checked. The original
gate's parsing and dependency functions are reused without modification.

The required equipped `TestLeanWasmBitwiseModuleFaithful` test runs this
superset gate after its existing extraction checks. It retains the prior
106 finite source/compiler claims and independent name-copy controls. This
runner alone does not perform Go builds or regenerate extracted source.

The successful-domain proof is the frozen parent; this gate adds only its
total-outcome refinement. See `docs/spec/91-wasm-module-total-proof.md` for the
contract, development dependency-reuse disclosure, and unchanged trust scope.
