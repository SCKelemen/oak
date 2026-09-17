#!/usr/bin/env python3
"""Compare exact stdlib grapheme lookup through C, before, identity and after."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BACKENDS = ("c", "native-before", "native-identity", "native-after")


def capture(args, **kwargs):
    return subprocess.run(args, check=True, capture_output=True, text=True, **kwargs).stdout.strip()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fixture(text):
    start = text.index("pub grapheme_table:")
    end = text.index("// grapheme_gcb:", start)
    return text[start:end] + "\nmain: (): i32 = 0\n"


def selected(diagnostics, require_proven=False):
    verdicts = [line for line in diagnostics.splitlines()
                if line.startswith("native backend: asm unit grapheme_class:")]
    bodies = re.findall(r"^grapheme_class = \{\n.*?^\}", diagnostics, re.M | re.S)
    if len(verdicts) != 1 or not bodies:
        raise ValueError("missing unique selected verdict or assembly")
    if require_proven and "proven equal to its Oak body" not in verdicts[0]:
        raise ValueError("candidate did not prove")
    return {"verdict": verdicts[0], "assembly": bodies[-1]}


def accept(row, expected):
    if (type(row.get("elapsed_ns")) is not int or row["elapsed_ns"] <= 0 or
            not isinstance(row.get("checksum"), str) or
            not re.fullmatch(r"[0-9a-f]{16}", row["checksum"])):
        raise ValueError("invalid sample")
    if expected is not None and row["checksum"] != expected:
        raise ValueError("checksum disagreement")
    return row["checksum"]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--baseline-emit", type=Path, required=True)
    p.add_argument("--baseline-oak", type=Path, required=True)
    p.add_argument("--candidate-emit", type=Path, required=True)
    p.add_argument("--baseline-revision", required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--samples", type=int, default=9)
    p.add_argument("--rounds", type=int, default=256)
    p.add_argument("--cc", default="cc")
    args = p.parse_args()
    if platform.system() != "Darwin" or platform.machine() != "arm64":
        p.error("this timing harness currently requires ARM64 macOS")
    if args.samples not in range(1, 100, 2) or not 1 <= args.rounds <= 4096:
        p.error("samples must be odd in [1,99]; rounds must be in [1,4096]")
    if not re.fullmatch(r"[0-9a-f]{40}", args.baseline_revision) or args.output.exists():
        p.error("full baseline revision and a new output path required")
    revision = capture(["git", "rev-parse", "HEAD"], cwd=ROOT)
    binaries = {name: getattr(args, name).resolve()
                for name in ("baseline_emit", "baseline_oak", "candidate_emit")}
    metadata = {name: {"sha256": digest(path), "build_info": capture(["go", "version", "-m", str(path)])}
                for name, path in binaries.items()}
    for name, record in metadata.items():
        wanted = revision if name == "candidate_emit" else args.baseline_revision
        if f"vcs.revision={wanted}" not in record["build_info"]:
            p.error(f"{name} revision mismatch")
    source = fixture((ROOT / "stdlib/grapheme.oak").read_text())
    flags = ["-std=c11", "-O3", "-ffp-contract=off", "-fno-fast-math"]
    transforms = re.findall(r'Transform\w+\s*=\s*"([^"]+)"', (ROOT / "nativegen/opt.go").read_text())
    if not transforms:
        raise ValueError("missing transform registry")
    report = {
        "schema": "oak-table-views-v1", "baseline_revision": args.baseline_revision,
        "candidate_revision": revision, "binaries": metadata,
        "dirty_worktree": bool(capture(["git", "status", "--porcelain"], cwd=ROOT)),
        "date": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "cpu": capture(["sysctl", "-n", "machdep.cpu.brand_string"]),
        "cc": capture([args.cc, "--version"]), "c_flags": flags,
        "fixture_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "runner_sha256": digest(HERE / "runner.c"), "identity_disabled_transforms": transforms,
        "sample_order": "all backend/distribution pairs interleaved, first pair rotated each round",
        "core_affinity": "uncontrolled", "cache_flush": False,
        "native_bodies": {}, "diagnostics": {}, "samples": [],
    }
    env = dict(os.environ)
    for key in list(env):
        if key.startswith(("OAK_OPT_", "OAK_NATIVE_", "OAK_VERIFY_")):
            env.pop(key)
    env["OAK_VERIFY_CACHE"] = "0"
    with tempfile.TemporaryDirectory(prefix="oak-table-views-") as temp:
        build = Path(temp)
        oak = build / "lookup.oak"
        oak.write_text(source)
        runners = {}
        for backend in BACKENDS:
            directory = build / backend
            directory.mkdir()
            prefix = directory / "kernels"
            objects = []
            if backend == "c":
                capture([str(binaries["baseline_oak"]), "build", "-o", str(prefix.with_suffix(".c")), str(oak)], cwd=ROOT, env=env)
            else:
                native_env = dict(env, OAK_NATIVE_ONLY="grapheme_class", OAK_NATIVE_DUMP="selected", OAK_OPT_REPORT="1")
                if backend == "native-identity":
                    native_env["OAK_OPT_SKIP"] = ",".join(transforms)
                emitter = binaries["baseline_emit" if backend == "native-before" else "candidate_emit"]
                done = subprocess.run([str(emitter), str(oak), str(prefix)], check=True, capture_output=True, text=True, cwd=ROOT, env=native_env)
                report["diagnostics"][backend] = done.stderr
                report["native_bodies"][backend] = selected(done.stderr, backend == "native-after")
                objects = [str(prefix.with_suffix(".o"))]
            exe = directory / "runner"
            capture([args.cc, *flags, "-I", str(directory), str(HERE / "runner.c"), *objects, "-o", str(exe), "-lm"])
            runners[backend] = str(exe)
        report["load_before"] = capture(["uptime"])
        variants = [(backend, mode) for backend in BACKENDS for mode in (1, 2, 3)]
        checksums = {}
        for round_ in range(args.samples):
            for offset in range(len(variants)):
                backend, mode = variants[(round_ + offset) % len(variants)]
                row = json.loads(capture([runners[backend], str(mode), str(args.rounds)]))
                checksums[mode] = accept(row, checksums.get(mode))
                report["samples"].append(dict(row, backend=backend, mode=mode, round=round_,
                                              calls=4096 * args.rounds, ns_per_lookup=row["elapsed_ns"] / (4096 * args.rounds)))
        report["load_after"] = capture(["uptime"])
    with args.output.open("x") as output:
        json.dump(report, output, indent=2)
        output.write("\n")


if __name__ == "__main__":
    main()
