#!/usr/bin/env python3
"""Fixed numeric-only Lean request renderer; never accepts Lean text or names.

This renderer is a development fixture utility, not production authority. Its
four immutable byte buffers must also be compared with the final audit record.
"""
from pathlib import Path
import argparse

LIMITS = {"source": 2048, "wasm": 1024, "arm": 2048, "rv": 2048}
PREFIX = """import Oak.CheckedBundleAudit
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace Oak.CheckedBundleRequest
"""
SUFFIX = """def declaration : Oak.BitwiseSource.Decl :=
  (Oak.BitwiseSource.parse source).getD ⟨[], [], [], .and⟩
theorem admitted : Oak.BitwiseSourceObjectParity.check source wasm arm rv = some declaration := by decide +kernel
theorem binding : type_of% (Oak.BitwiseSourceObjectParity.accepted_source_object_binding admitted) := Oak.BitwiseSourceObjectParity.accepted_source_object_binding admitted
theorem all_inputs : type_of% (Oak.BitwiseSourceObjectParity.accepted_all_input_success admitted) := Oak.BitwiseSourceObjectParity.accepted_all_input_success admitted
end Oak.CheckedBundleRequest
#oak_checked_bundle_audit
"""


def render(source: bytes, wasm: bytes, arm: bytes, rv: bytes) -> str:
    parts = [PREFIX]
    for name, raw in zip(LIMITS, (source, wasm, arm, rv), strict=True):
        if type(raw) is not bytes:
            raise TypeError(f"{name} must be an immutable bytes buffer")
        if not 0 < len(raw) <= LIMITS[name]:
            raise ValueError(f"{name} length must be 1..{LIMITS[name]}")
        typ = "List UInt8" if name in ("source", "wasm") else "Oak.MinimalELF.Bytes"
        parts.append(f"def {name} : {typ} := [" + ",".join(map(str, raw)) + "]\n")
    parts.append(SUFFIX)
    return "".join(parts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in LIMITS:
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    # Read once. Source contents and paths are never interpolated as Lean code.
    args.output.write_text(render(*(getattr(args, name).read_bytes() for name in LIMITS)))


if __name__ == "__main__":
    main()
