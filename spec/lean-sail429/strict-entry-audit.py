#!/usr/bin/env python3
"""Fail closed on the real 4.29 strict-image admission/execution consumer.

Admission roots use only the standard three Lean axioms. Execution roots must
match the unchanged real entry theorem's exact 77-name external closure.
The optional fresh compiler fixture has a fixed 48-root proof inventory.
This script does not accept 4.33 receipts, expression stand-ins, or allowlists.
"""
import argparse
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
TOOLCHAIN = "leanprover/lean4:v4.29.0"
BASE = json.loads((ROOT.parent / "lean-sail433/axiom-allowlist.json").read_text())
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXECUTION = STANDARD | set(BASE["configuration"]) | set(BASE["full_dispatch_extras"]) | {"valid_reservation"}
BASELINE = "OakSailEntrySource.accepted_typed_entry_clocked_prefix"
MODEL_ROOTS = {
    "Oak.StrictImageEntryContract": (
        "strict_segment", "strict_startup", "strict_call_prefix", "source_entry_binding",
        "entry_preconditions", "entry_stack_disjoint", "entry_bounds"),
    "OakSailStrictImageEntry": (
        "strict_source_entry_admitted", "strict_source_entry_admitted_of_layout"),
    "OakSailStrictImageEntryExecution": ("strict_typed_entry_clocked_prefix",),
    "OakSailStrictImageEntryChecks": (
        "strict_layout_below", "strict_layout_above", "initialized_strict_entry_clocked_prefix"),
}
MODEL_EXECUTION = {
    "OakSailStrictImageEntryExecution.strict_typed_entry_clocked_prefix",
    "OakSailStrictImageEntryChecks.initialized_strict_entry_clocked_prefix",
}
FIXTURE_NAMESPACE = "StrictEntryCompilerPins"
FIXTURE_PURE = {
    "slice_after", "padded_tail_slice", "padded_tail_read", "zero_gap",
    "accepts_of_profile", "refuses_profile", "refuses_body",
    "layout_touch_below", "admitted_touch_below", "layout_touch_above", "admitted_touch_above",
    "reject_source", "reject_source_type", "reject_wasm", "reject_arm_body", "reject_rv_body",
    "reject_startup", "reject_entry", "reject_stack_underflow", "reject_stack_alignment",
    "reject_stack_overlap", "reject_stack_upper", "prefix_accepts_changed_suffix", "strict_rejects_changed_suffix",
} | {f"{kind}_{op}" for kind in
     ("parsed", "wasm_checked", "arm_checked", "rv_checked", "checked", "layout", "admitted")
     for op in ("and", "or", "xor")}
FIXTURE_EXECUTION = {f"execution_{op}" for op in ("and", "or", "xor")}
EXACT_STANDARD = {
    "OakSailStrictImageEntry.strict_source_entry_admitted",
    "OakSailStrictImageEntry.strict_source_entry_admitted_of_layout",
} | {FIXTURE_NAMESPACE + ".admitted_" + op for op in ("and", "or", "xor")} | {
    FIXTURE_NAMESPACE + ".admitted_touch_below", FIXTURE_NAMESPACE + ".admitted_touch_above",
}


def proof_inventory(text):
    # Data definitions are kernel-checked transitively through the fixed roots.
    # Every theorem/helper and noncomputable execution definition is inventoried.
    return re.findall(r"(?m)^(?:private )?(?:theorem|noncomputable def) ([A-Za-z0-9_]+)\b", text)


def require_inventory(text, expected, label):
    names = proof_inventory(text)
    if len(names) != len(set(names)) or set(names) != set(expected):
        raise RuntimeError(f"{label}: proof inventory differs: missing={sorted(set(expected)-set(names))}, "
                           f"extra={sorted(set(names)-set(expected))}, duplicates={len(names)!=len(set(names))}")


def model_inventory():
    for namespace, names in MODEL_ROOTS.items():
        path = (ROOT.parent / "lean/Oak/StrictImageEntryContract.lean" if namespace.startswith("Oak.")
                else ROOT / (namespace + ".lean"))
        require_inventory(path.read_text(), names, str(path))


def require_execution_signatures():
    # Source equality is an audit guard, not a kernel execution proof.
    root = ROOT
    for old_file, old_name, new_file, new_name in (
        ("OakSailEntrySource.lean", "accepted_typed_entry_clocked_prefix",
         "OakSailStrictImageEntryExecution.lean", "strict_typed_entry_clocked_prefix"),
        ("OakSailEntryChecks.lean", "initialized_entry_clocked_prefix",
         "OakSailStrictImageEntryChecks.lean", "initialized_strict_entry_clocked_prefix"),
    ):
        def signature(file, name):
            text = (root / file).read_text()
            start = text.index("theorem " + name)
            return text[start:text.index(" := by", start)]
        expected = signature(old_file, old_name).replace("theorem " + old_name, "theorem " + new_name)
        expected = expected.replace("{source : List UInt8}", "{source wasm : List UInt8}")
        expected = expected.replace("{image : Bytes}", "{arm image : Bytes}")
        expected = expected.replace("(accepted : acceptsEntry source claim image sp = true)",
            "(checked : Oak.BitwiseSourceImageParity.check source wasm arm image = some claim)\n"
            "    (layout : OakSailImageLoad.ImageLayout image sp)")
        if signature(new_file, new_name) != expected:
            raise RuntimeError("Changed actual execution signature: " + new_name)


def require_fixture_execution(source):
    for op in ("and", "or", "xor"):
        pattern = (r"(?ms)^noncomputable def execution_" + op +
                   r"\b.*?(?=^(?:noncomputable def|private theorem|theorem|def|end)\b|\Z)")
        declarations = re.findall(pattern, source)
        expected = (f"noncomputable def execution_{op} := "
                    f"OakSailStrictImageEntryChecks.initialized_strict_entry_clocked_prefix checked_{op} layout_{op}")
        if len(declarations) != 1 or " ".join(declarations[0].split()) != expected:
            raise RuntimeError("Changed fixture execution application: execution_" + op)


def parse_axioms(output, expected):
    rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output, re.S)
    entries = [(name, {x.strip() for x in body.split(",") if x.strip()}) for name, body in rows]
    entries += [(name, set()) for name in re.findall(r"'([^']+)' does not depend on any axioms", output)]
    names = [name for name, _ in entries]
    if len(names) != len(set(names)) or set(names) != set(expected):
        raise RuntimeError("Missing, duplicate or unexpected axiom reports")
    return dict(entries)


def validate_closures(actual, execution_roots):
    if len(EXECUTION) != 77 or actual.get(BASELINE) != EXECUTION:
        raise RuntimeError("The real baseline entry theorem does not have its exact existing 77-name closure")
    for name, axioms in actual.items():
        if name == BASELINE or name in execution_roots:
            if axioms != actual[BASELINE]:
                raise RuntimeError("Changed external execution closure: " + name)
        elif axioms - STANDARD:
            raise RuntimeError(f"Nonstandard pure-admission dependencies: {name}: {sorted(axioms-STANDARD)}")
        elif name in EXACT_STANDARD and axioms != STANDARD:
            raise RuntimeError("Changed strict admission closure: " + name)


def require_version(version):
    if not version.startswith("Lean (version 4.29.0,"):
        raise RuntimeError("Expected same-kernel Lean 4.29.0, got " + version)


def pinned_environment():
    selected = (ROOT / "lean-toolchain").read_text().strip()
    if selected != TOOLCHAIN:
        raise RuntimeError(f"Unexpected Sail project toolchain: {selected!r}")
    return {**os.environ, "ELAN_TOOLCHAIN": TOOLCHAIN}


def run(args):
    # A temporary proof path never selects the project or its kernel. Do not
    # inherit a caller's 4.33 override, and do not mutate process-global state.
    return subprocess.run(args, cwd=ROOT, env=pinned_environment(),
                          text=True, capture_output=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, help="fresh generated compiler certificate; fixed proof inventory")
    args = parser.parse_args()
    require_execution_signatures()
    version_check = run(["lake", "env", "lean", "--version"])
    if version_check.returncode:
        raise RuntimeError("Real Sail project preflight failed:\n" + version_check.stdout + version_check.stderr)
    require_version(version_check.stdout)
    model_inventory()
    names = {namespace + "." + name for namespace, roots in MODEL_ROOTS.items() for name in roots}
    execution_roots = set(MODEL_EXECUTION)
    if args.fixture:
        source = args.fixture.read_text()
        require_inventory(source, FIXTURE_PURE | FIXTURE_EXECUTION, "fresh compiler fixture")
        require_fixture_execution(source)
        names |= {FIXTURE_NAMESPACE + "." + name for name in FIXTURE_PURE | FIXTURE_EXECUTION}
        execution_roots |= {FIXTURE_NAMESPACE + "." + name for name in FIXTURE_EXECUTION}
    else:
        source = "import OakSailStrictImageEntryChecks\n"
    names.add(BASELINE)
    source += "\nset_option debug.skipKernelTC false\n"
    source += "\n".join("#print axioms " + name for name in sorted(names)) + "\n"
    with tempfile.TemporaryDirectory(prefix="oak-strict-entry-audit-") as tmp:
        path = Path(tmp) / "StrictEntryAudit.lean"
        path.write_text(source)
        result = run(["lake", "env", "lean", "-t", "0", "--tstack=400000", str(path)])
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    actual = parse_axioms(result.stdout, names)
    validate_closures(actual, execution_roots)
    for name in sorted(names):
        print(f"{name}: {len(actual[name])} checked dependencies")
    print(f"{len(names)-len(execution_roots)-1} pure roots: standard Lean axioms only.")
    print(f"{len(execution_roots)} execution roots: exact unchanged 77-name actual entry closure.")
    print("Real Lean 4.29 consumer, trust level zero; no native-evaluation or sorry dependencies.")


if __name__ == "__main__":
    main()
