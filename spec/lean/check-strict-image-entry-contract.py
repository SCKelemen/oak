#!/usr/bin/env python3
"""Preparatory 4.33 admission-expression check; NOT an external Sail build.

The pure consumer expressions and adapter proof are read from their one source
of truth every run. Extracted declarations exist only in a generated local test
under ExtractedOnly. No copied checker becomes a maintained production module.
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
TOOLCHAIN = "leanprover/lean4:v4.33.1"
SPEC = ROOT.parent
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
PURE = [
    ("lean-sail433/OakSailComposition.lean", "OakSailComposition", "NativeBytes"),
    ("lean-sail433/OakSailComposition.lean", "OakSailComposition", "acceptsProjection"),
    ("lean-sail433/OakSailFramedComposition.lean", "OakSailFramedComposition", "acceptsFrame"),
    ("lean-sail429/OakSailImageLoad.lean", "OakSailImageLoad", "ImageLayout"),
    ("lean-sail429/OakSailImageLoad.lean", "OakSailImageLoad", "acceptsImage"),
    ("lean-sail429/OakSailImageLoad.lean", "OakSailImageLoad", "acceptsImage_iff"),
    ("lean-sail429/OakSailImageSource.lean", "OakSailImageSource", "accepts"),
    ("lean-sail429/OakSailImageSource.lean", "OakSailImageSource", "accepts_iff"),
    ("lean-sail429/OakSailEntryInstructions.lean", "OakSailEntryInstructions", "startupBytes"),
    ("lean-sail429/OakSailEntrySource.lean", "OakSailEntrySource", "acceptsEntry"),
    ("lean-sail429/OakSailEntrySource.lean", "OakSailEntrySource", "acceptsEntry_iff"),
]

def declaration(text, name):
    starts = list(re.finditer(r"(?m)^(?:def|abbrev|theorem) " + re.escape(name) + r"\b", text))
    if len(starts) != 1:
        raise RuntimeError(f"Expected exactly one declaration: {name}")
    tail = text[starts[0].start():]
    boundary = re.search(r"\n(?=/--|/-!|def |abbrev |instance |theorem |end )", tail)
    if boundary is None:
        raise RuntimeError(f"Missing declaration boundary: {name}")
    return tail[:boundary.start()].rstrip() + "\n"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def pinned_environment():
    selected = (ROOT / "lean-toolchain").read_text().strip()
    if selected != TOOLCHAIN:
        raise RuntimeError(f"Unexpected pure project toolchain: {selected!r}")
    return {**os.environ, "ELAN_TOOLCHAIN": TOOLCHAIN}


def run(args):
    result = subprocess.run(args, cwd=ROOT, env=pinned_environment(),
                            text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def generated():
    out = ["import Oak.StrictImageEntryContract\nset_option autoImplicit false\n",
           "/- TEST-ONLY exact pure source extraction; no external model import. -/\n",
           "namespace ExtractedOnly\n"]
    inventory = []
    for relative, namespace, name in PURE:
        raw = (SPEC / relative).read_bytes()
        snippet = declaration(raw.decode(), name)
        inventory.append({"source": relative, "declaration": namespace + "." + name,
                          "source_sha256": sha(raw), "snippet_sha256": sha(snippet.encode())})
        out += [f"namespace {namespace}\n", "open Oak.MinimalELF\n",
                "open OakSailImageLoad\n" if namespace == "OakSailImageSource" else "",
                "open OakSailImageSource OakSailEntryInstructions\n" if namespace == "OakSailEntrySource" else "",
                snippet]
        if name == "ImageLayout":
            # Preserve the existing decidability instance verbatim as well.
            text = raw.decode()
            instance = text[text.index("instance (image : Bytes) (sp : Nat) : Decidable (ImageLayout"):
                            text.index("def acceptsImage")].strip() + "\n"
            out.append(instance)
            inventory.append({"source": relative, "declaration": namespace + ".ImageLayout instance",
                              "snippet_sha256": sha(instance.encode())})
        out.append(f"end {namespace}\n")
    adapter = (SPEC / "lean-sail429/OakSailStrictImageEntry.lean").read_text()
    adapter_body = adapter[adapter.index("set_option autoImplicit false"):]
    out += [adapter_body, "end ExtractedOnly\n"]
    inventory.append({"source": "lean-sail429/OakSailStrictImageEntry.lean",
                      "snippet_sha256": sha(adapter_body.encode())})
    return "\n".join(out), inventory


def fixture_checks():
    """Recheck selected complete committed production native fixtures, unchanged."""
    raw = (ROOT / "NativeBitwiseImageFixtures.lean").read_bytes()
    text = raw.decode()
    preamble = text[:text.index("namespace arm64_mix_and")]
    preamble = preamble.replace("import Oak.NativeBitwiseImage\n", "")
    chunks = [preamble]
    inventory = [{"source": "lean/NativeBitwiseImageFixtures.lean",
                  "source_sha256": sha(raw), "preamble_sha256": sha(preamble.encode())}]
    names = []
    negatives = ["reject_mutation_header_entry", "reject_mutation_stub_byte_4096",
                 "reject_mutation_stub_byte_4104", "reject_mutation_body_byte_4112",
                 "reject_mutation_function_alias_start"]
    for machine in ["arm64", "riscv64"]:
        for op in ["and", "or", "xor"]:
            namespace = f"{machine}_mix_{op}"
            start = text.index("namespace " + namespace + "\n")
            finish = text.index("\ntheorem loaded", start)
            snippet = text[start:finish] + "\n"
            chunks.append(snippet)
            inventory.append({"fixture": namespace, "snippet_sha256": sha(snippet.encode())})
            names.append(f"Oak.NativeBitwiseImageFixtures.{namespace}.admitted")
            if machine == "riscv64" and op == "and":
                end = text.index("end " + namespace, start)
                for name in negatives:
                    matches = [line for line in text[start:end].splitlines()
                               if line.startswith("theorem " + name + " ")]
                    if len(matches) != 1:
                        raise RuntimeError("Missing one-line fixture theorem: " + name)
                    chunks.append(matches[0] + "\n")
                    names.append(f"Oak.NativeBitwiseImageFixtures.{namespace}.{name}")
            chunks.append("end " + namespace + "\n")
    chunks.append("end Oak.NativeBitwiseImageFixtures\n")
    chunks.append(r"""
namespace StrictImageEntryTests
open Oak.MinimalELF
open Oak.NativeBitwiseImageFixtures
open ExtractedOnly

-- This is a canonical checked Wasm companion, not a fresh compiler artifact.
def wasm (op : Oak.BitwiseFunction.Op) : List UInt8 :=
  [0,97,115,109,1,0,0,0,1,7,1,96,2,127,127,1,127,3,2,1,0,
   7,7,1,3,109,105,120,0,0,10,9,1,7,0] ++ Oak.BitwiseFunction.functionBytes op

def declaration (op : Oak.BitwiseFunction.Op) : Oak.BitwiseSource.Decl :=
  ⟨[109,105,120], [97], [98], op⟩

theorem rejects_layout {source : List UInt8} {d : Oak.BitwiseSource.Decl}
    {image : Bytes} {sp : Nat} (bad : ¬ OakSailImageLoad.ImageLayout image sp) :
    OakSailEntrySource.acceptsEntry source d image sp = false := by
  have hb : decide (OakSailImageLoad.ImageLayout image sp) = false := decide_eq_false bad
  simp only [OakSailEntrySource.acceptsEntry, OakSailImageSource.accepts,
    OakSailImageLoad.acceptsImage, hb, Bool.and_false, Bool.false_and]
""")
    names.append("StrictImageEntryTests.rejects_layout")
    for op in ["and", "or", "xor"]:
        rv, arm = f"riscv64_mix_{op}", f"arm64_mix_{op}"
        chunks.append(f"""
theorem source_identity_{op} : {rv}.source = {arm}.source := by decide +kernel

theorem parsed_{op} : Oak.BitwiseSource.parse {rv}.source = some (declaration .{op}) := by
  decide +kernel

theorem strict_check_{op} :
    Oak.BitwiseSourceImageParity.check {rv}.source (wasm .{op})
      {arm}.image {rv}.image = some (declaration .{op}) := by
  apply Oak.BitwiseSourceImageParity.check_of_artifacts parsed_{op}
  · decide +kernel
  · exact {arm}.admitted
  · exact {rv}.admitted

theorem segment_{op} : segment {rv}.image = ⟨65536, 4096, 65536, 64, 64, 5, 4096⟩ := by
  obtain ⟨_, _, _, _, _, hs, _⟩ := Oak.StrictImageEntryContract.source_entry_binding strict_check_{op}
  exact hs
""")
        for name in [f"source_identity_{op}", f"parsed_{op}", f"strict_check_{op}", f"segment_{op}"]:
            names.append("StrictImageEntryTests." + name)
        for label, sp in [("touching_below", 65536), ("touching_above", 65696)]:
            name = f"{label}_{op}"
            chunks.append(f"""
theorem {name} :
    OakSailEntrySource.acceptsEntry {rv}.source (declaration .{op}) {rv}.image {sp} = true :=
  OakSailStrictImageEntry.strict_source_entry_admitted_of_layout strict_check_{op}
    (by rw [OakSailImageLoad.ImageLayout, segment_{op}]; decide +kernel)
""")
            names.append("StrictImageEntryTests." + name)
    for label, sp in [("underflow", 80), ("misaligned", 65535), ("overlap", 65552),
                      ("segment_end_overlap", 65600), ("clint_overflow", 33554448)]:
        name = "reject_" + label
        chunks.append(f"""
theorem {name} : OakSailEntrySource.acceptsEntry riscv64_mix_and.source
    (declaration .and) riscv64_mix_and.image {sp} = false := by
  apply rejects_layout
  rw [OakSailImageLoad.ImageLayout, segment_and]
  decide +kernel
""")
        names.append("StrictImageEntryTests." + name)
    chunks.append(r"""
theorem reject_source_replay :
    Oak.BitwiseSourceImageParity.check riscv64_mix_or.source (wasm .and)
      arm64_mix_and.image riscv64_mix_and.image ≠ some (declaration .and) :=
  Oak.BitwiseSourceImageParity.refuses_source_replay (by decide +kernel)

-- The broader old admission accepts a changed excluded ADDI byte. The strict
-- original checker still refuses it. This is why the adapter is one-way.
def changedSuffix : Bytes := riscv64_mix_and.image.set 4104
  ((riscv64_mix_and.image.getD 4104 0) ^^^ (BitVec.ofNat 8 1))

theorem prefix_consumer_accepts_changed_suffix :
    OakSailEntrySource.acceptsEntry riscv64_mix_and.source (declaration .and)
      changedSuffix 65536 = true := by decide +kernel

theorem strict_refuses_changed_suffix :
    Oak.BitwiseSourceImageParity.check riscv64_mix_and.source (wasm .and)
      arm64_mix_and.image changedSuffix = none :=
  Oak.BitwiseSourceImageParity.refuses_failed_artifact parsed_and
    (Or.inr (Or.inr riscv64_mix_and.reject_mutation_stub_byte_4104))

end StrictImageEntryTests
""")
    names += ["StrictImageEntryTests." + name for name in
              ["reject_source_replay", "prefix_consumer_accepts_changed_suffix", "strict_refuses_changed_suffix"]]
    return "\n".join(chunks), inventory, names


def audit_output(output, names):
    actual = {name: set(x.strip() for x in body.split(",") if x.strip())
              for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output, re.S)}
    actual.update({name: set() for name in re.findall(r"'([^']+)' does not depend on any axioms", output)})
    for name in names:
        if name not in actual:
            raise RuntimeError("Missing audit output: " + name)
        if actual[name] - STANDARD:
            raise RuntimeError(f"Unexpected axioms: {name}: {sorted(actual[name] - STANDARD)}")
    return {name: sorted(actual[name]) for name in names}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence-dir", type=Path)
    args = parser.parse_args()
    version = run(["lake", "env", "lean", "--version"]).strip()
    if not version.startswith("Lean (version 4.33.1,"):
        raise RuntimeError("Expected pinned Lean 4.33.1; got " + version)
    build = run(["lake", "build", "Oak.StrictImageEntryContract"])
    source, inventory = generated()
    fixture_source, fixture_inventory, fixture_names = fixture_checks()
    source += fixture_source
    inventory += fixture_inventory
    model = (ROOT / "Oak/StrictImageEntryContract.lean").read_text()
    names = ["Oak.StrictImageEntryContract." + name for name in
             re.findall(r"(?m)^theorem ([A-Za-z0-9_]+)", model)]
    names += ["ExtractedOnly." + namespace + "." + name
              for _, namespace, name in PURE if name.endswith("_iff")]
    adapter_text = (SPEC / "lean-sail429/OakSailStrictImageEntry.lean").read_text()
    names += ["ExtractedOnly.OakSailStrictImageEntry." + name for name in
              re.findall(r"(?m)^theorem ([A-Za-z0-9_]+)", adapter_text)] + fixture_names
    source += "\n" + "\n".join("#print axioms " + name for name in names) + "\n"
    with tempfile.TemporaryDirectory(prefix="oak-entry-preconditions-") as tmp:
        check = Path(tmp) / "ExtractedEntryAdmission.lean"
        check.write_text(source)
        output = run(["lake", "env", "lean", "-t", "0", str(check)])
    axioms = audit_output(output, names)
    report = {"scope": "Preparatory pure admission only; real Sail import is NOT built",
              "version": version, "source_sha256": sha(source.encode()),
              "projection_sha256": sha(model.encode()), "extracted_sources": inventory,
              "axioms": axioms}
    if args.evidence_dir:
        args.evidence_dir.mkdir(parents=True, exist_ok=True)
        (args.evidence_dir / "ExtractedEntryAdmission.lean").write_text(source)
        (args.evidence_dir / "build.log").write_text(build)
        (args.evidence_dir / "kernel.log").write_text(output)
        (args.evidence_dir / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
