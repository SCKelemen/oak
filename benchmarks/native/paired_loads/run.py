#!/usr/bin/env python3
"""Compare frozen native compilers on modular u32/u64 reductions."""
import argparse
import datetime
import hashlib
import json
import os
import platform
import re
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BACKENDS = ("c", "native-before", "native-identity", "native-after")


def capture(argv, **kwargs):
    return subprocess.check_output(argv, text=True, **kwargs).strip()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def observation_index(round_, offset, count):
    return (round_ + offset) % count


def accept_sample(row, expected):
    if (type(row.get("elapsed_ns")) is not int or row["elapsed_ns"] <= 0 or
            not isinstance(row.get("checksum"), str) or
            not re.fullmatch(r"[0-9a-f]{16}", row["checksum"])):
        raise ValueError("invalid benchmark sample")
    if expected is not None and row["checksum"] != expected:
        raise ValueError("benchmark checksum mismatch")
    return row["checksum"]


def selected_bodies(diagnostics):
    bodies = {}
    for name in ("sum32", "sum64"):
        if f"asm unit {name}: proven equal to its Oak body" not in diagnostics:
            raise ValueError(f"{name} was not proven by the native compiler")
        matches = re.findall(rf"^{name} = \{{\n.*?^\}}", diagnostics, re.M | re.S)
        if not matches:
            raise ValueError(f"no selected assembly for {name}")
        assembly = matches[-1]
        # The last dump is the selected body, after any refused candidates.
        main = re.search(r"^loop_\w+:\n(.*?)(?=^\w+:)", assembly, re.M | re.S)
        loop = main.group(1).splitlines() if main else []
        frame = re.search(r"\bframe (\d+)", assembly)
        bodies[name] = {
            "verdict": "proven", "assembly": assembly,
            "frame_bytes": int(frame[1]) if frame else 0,
            "main_loop_instructions": len([line for line in loop if line.strip()]),
            "main_loop_addresses": sum("uxtw" in line and line.strip().startswith("add ") for line in loop),
        }
    return bodies


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline-emit", type=Path, required=True)
    parser.add_argument("--baseline-oak", type=Path, required=True)
    parser.add_argument("--baseline-revision", required=True)
    parser.add_argument("--candidate-emit", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--samples", type=int, default=9)
    parser.add_argument("--elements", type=int, nargs="+", default=[7, 4096, 1 << 20])
    parser.add_argument("--cc", default="cc")
    args = parser.parse_args()
    if platform.system() != "Darwin" or platform.machine() != "arm64":
        parser.error("this runner currently requires ARM64 macOS")
    if args.samples < 1 or args.samples > 99 or args.samples % 2 == 0:
        parser.error("samples must be odd and in [1,99]")
    if any(n < 1 or n > 1 << 20 for n in args.elements) or len(set(args.elements)) != len(args.elements):
        parser.error("elements must be distinct and in [1,1048576]")
    if not re.fullmatch(r"[0-9a-f]{40}", args.baseline_revision):
        parser.error("baseline revision must be a full commit ID")
    if args.output.exists():
        parser.error("output already exists")
    flags = ["-std=c11", "-O3", "-ffp-contract=off", "-fno-fast-math"]
    binaries = {"baseline_emit": args.baseline_emit.resolve(), "baseline_oak": args.baseline_oak.resolve(), "candidate_emit": args.candidate_emit.resolve()}
    # The candidate binary must be built from this checkout; retain embedded
    # Go build metadata as well as its digest so stale binaries are visible.
    revision = capture(["git", "rev-parse", "HEAD"], cwd=ROOT)
    metadata = {name: {"sha256": digest(path), "go_build_info": capture(["go", "version", "-m", str(path)])} for name, path in binaries.items()}
    for name, wanted in (("baseline_emit", args.baseline_revision), ("baseline_oak", args.baseline_revision), ("candidate_emit", revision)):
        if f"vcs.revision={wanted}" not in metadata[name]["go_build_info"]:
            parser.error(f"{name} binary revision does not match {wanted}")
    report = {
        "schema": "oak-paired-load-liveness-v1", "revision": revision,
        "dirty_worktree": bool(capture(["git", "status", "--porcelain"], cwd=ROOT)),
        "baseline_revision": args.baseline_revision, "binaries": metadata,
        "date": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "cpu": capture(["sysctl", "-n", "machdep.cpu.brand_string"]),
        "cc": capture([args.cc, "--version"]), "c_flags": flags,
        "source_sha256": digest(HERE / "sums.oak"), "runner_sha256": digest(HERE / "runner.c"),
        "sample_order": "interleaved backend/width, rotating first variant each round",
        "core_affinity": "uncontrolled", "cache_flush": False,
        "native_bodies": {}, "diagnostics": {}, "samples": [],
    }
    env = dict(os.environ)
    for key in ("OAK_OPT_SKIP", "OAK_OPT_BEAM", "OAK_NATIVE_ONLY", "OAK_NATIVE_DUMP"):
        env.pop(key, None)
    transforms = re.findall(r'Transform\w+\s*=\s*"([^"]+)"', (ROOT / "nativegen/opt.go").read_text())
    if not transforms:
        raise ValueError("cannot determine identity transform names")
    report["identity_disabled_transforms"] = transforms
    with tempfile.TemporaryDirectory(prefix="oak-paired-loads-") as temporary:
        build = Path(temporary)
        executables = {}
        for backend in BACKENDS:
            directory = build / backend
            directory.mkdir()
            prefix = directory / "kernels"
            objects = []
            if backend == "c":
                subprocess.run([str(binaries["baseline_oak"]), "build", "-o", str(prefix.with_suffix(".c")), str(HERE / "sums.oak")], cwd=ROOT, env=env, check=True, capture_output=True)
            else:
                native_env = dict(env, OAK_NATIVE_ONLY="sum32,sum64", OAK_NATIVE_DUMP="selected")
                if backend == "native-identity":
                    native_env["OAK_OPT_SKIP"] = ",".join(transforms)
                emitter = binaries["baseline_emit" if backend == "native-before" else "candidate_emit"]
                compiled = subprocess.run([str(emitter), str(HERE / "sums.oak"), str(prefix)], cwd=ROOT, env=native_env, check=True, capture_output=True, text=True)
                report["diagnostics"][backend] = compiled.stderr
                report["native_bodies"][backend] = selected_bodies(compiled.stderr)
                objects.append(str(prefix.with_suffix(".o")))
            executable = directory / "runner"
            subprocess.run([args.cc, *flags, "-I", str(directory), str(HERE / "runner.c"), *objects, "-o", str(executable), "-lm"], check=True, capture_output=True)
            executables[backend] = str(executable)
        report["load_before"] = capture(["uptime"])
        variants = [(backend, width) for backend in BACKENDS for width in (32, 64)]
        checksums = {}
        for n in args.elements:
            calls = min(1 << 20, max(64, (1 << 27) // n))
            for round_ in range(args.samples):
                for offset in range(len(variants)):
                    backend, width = variants[observation_index(round_, offset, len(variants))]
                    row = json.loads(capture([executables[backend], str(width), str(n), str(calls)]))
                    checksums[n, width] = accept_sample(row, checksums.get((n, width)))
                    report["samples"].append(dict(row, backend=backend, width=width, elements=n, calls=calls, round=round_, ns_per_element=row["elapsed_ns"] / (n * calls)))
        report["load_after"] = capture(["uptime"])
    with args.output.open("x") as output:
        json.dump(report, output, indent=2)
        output.write("\n")


if __name__ == "__main__":
    main()
