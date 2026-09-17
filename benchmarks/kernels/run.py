#!/usr/bin/env python3
"""Kernel comparison: Oak against Go and Rust on the same workloads.

Builds the Oak kernels through the compiler (oak build -> C -> cc -O3), through
the native backend (the Oak assembler's companion object beside the C shell,
the oak-native row), the Go
program (go build), and the Rust program (rustc -O), runs each kernel with the
same command line, checks that every implementation produced the same
checksum before accepting any timing, and writes one JSON file with the raw
samples and medians. See README.md for what is and is not measured.
"""
import argparse
import json
import os
import platform
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
KERNELS = ["crc32c", "sha256", "blake3", "dot", "sum", "search", "page_probe", "bitmap", "dispatch", "tiled"]
GO_IMPLS = {"crc32c": ["go-stdlib", "go-generic"], "sha256": ["go-stdlib", "go-generic"],
            "dot": ["go"], "sum": ["go"], "search": ["go"],
            "page_probe": ["go"], "bitmap": ["go-stdlib", "go-generic"], "dispatch": ["go"], "tiled": ["go"]}
RUST_KERNELS = ["crc32c", "sha256", "dot", "sum", "search", "page_probe", "bitmap", "dispatch", "tiled"]


def capture(args, cwd=None):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def cpu_model():
    try:
        if platform.system() == "Darwin":
            return capture(["sysctl", "-n", "machdep.cpu.brand_string"])
        for line in Path("/proc/cpuinfo").read_text().splitlines():
            if line.startswith("model name"):
                return line.split(":", 1)[1].strip()
    except Exception:
        pass
    return platform.processor() or "unknown"


def sample_kernel(commands, size, rounds, samples):
    """Interleave implementations, rotating which runs first each sample."""
    if not commands or samples < 1:
        raise ValueError("benchmark needs an implementation and at least one sample")
    rows = [None] * len(commands)
    checksum = None
    for sample in range(samples):
        for offset in range(len(commands)):
            index = (sample + offset) % len(commands)
            row = json.loads(capture(commands[index] + [str(size), str(rounds), "1"]))
            if checksum is None:
                checksum = row["checksum"]
            elif row["checksum"] != checksum:
                raise ValueError(
                    f"{row['kernel']}: implementations disagree at sample {sample + 1}: "
                    f"{row['impl']} returned {row['checksum']}, expected {checksum}"
                )
            if rows[index] is None:
                rows[index] = dict(row)
                rows[index]["samples"] = []
            rows[index]["samples"].extend(row["samples"])
    for row in rows:
        # Keep raw samples in observation order so load drift is visible.
        ordered = sorted(row["samples"])
        row["ns_per_op_median"] = ordered[len(ordered) // 2]
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=1 << 20, help="elements per kernel (bytes, floats, or words)")
    parser.add_argument("--rounds", type=int, default=5)
    parser.add_argument("--samples", type=int, default=7)
    parser.add_argument("--cc", default="cc")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--kernels", nargs="*", default=KERNELS)
    args = parser.parse_args()
    flags = ["-O3", "-DNDEBUG"]
    results = []
    with tempfile.TemporaryDirectory(prefix="oak-kernels-") as tmp:
        build = Path(tmp)
        subprocess.run(["go", "run", ".", "build", "-o", str(build / "kernels.c"), str(HERE / "oak")], cwd=ROOT, check=True)
        subprocess.run([args.cc, "-std=c99", *flags, "-I" + str(build), "-o", str(build / "oak-runner"), str(HERE / "runner.c"), "-lm"], check=True)
        # The native backend: the same package through the Oak assembler,
        # the C shell plus the companion object (benchmarks/native/emit),
        # linked into a second runner labeled oak-native.
        native = build / "native"
        native.mkdir()
        subprocess.run(["go", "run", "./benchmarks/native/emit", str(HERE / "oak"), str(native / "kernels")], cwd=ROOT, check=True, stderr=subprocess.DEVNULL)
        subprocess.run([args.cc, "-std=c99", *flags, "-DOAK_IMPL=\"oak-native\"", "-I" + str(native), "-o", str(build / "oak-native-runner"), str(HERE / "runner.c"), str(native / "kernels.o"), "-lm"], check=True)
        subprocess.run(["go", "build", "-o", str(build / "go-runner"), "."], cwd=HERE / "go", check=True)
        subprocess.run(["rustc", "-O", "-o", str(build / "rust-runner"), str(HERE / "rust" / "main.rs")], check=True)
        for kernel in args.kernels:
            runs = [[str(build / "oak-runner"), kernel], [str(build / "oak-native-runner"), kernel]]
            for impl in GO_IMPLS.get(kernel, []):
                runs.append([str(build / "go-runner"), impl, kernel])
            if kernel in RUST_KERNELS:
                runs.append([str(build / "rust-runner"), kernel])
            try:
                results.extend(sample_kernel(runs, args.size, args.rounds, args.samples))
            except ValueError as err:
                sys.exit(str(err))
    report = {
        "schema": "oak-kernels-benchmark-v1",
        "machine": platform.machine(), "platform": platform.platform(), "cpu": cpu_model(),
        "oak": capture(["git", "rev-parse", "HEAD"], cwd=ROOT),
        "cc": capture([args.cc, "--version"]).splitlines()[0],
        "go": capture(["go", "version"]), "rustc": capture(["rustc", "--version"]),
        "c_flags": flags, "rust_flags": ["-O"], "go_flags": [],
        "size": args.size, "rounds": args.rounds, "samples": args.samples,
        "sample_order": "interleaved implementations, rotating first implementation each sample",
        "core_affinity": "not controlled", "cache_flush": False,
        "results": results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    for row in results:
        print(f"{row['kernel']:8s} {row['impl']:11s} {row['ns_per_op_median']:>14.1f} ns/op")


if __name__ == "__main__":
    main()
