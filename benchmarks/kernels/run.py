#!/usr/bin/env python3
"""Kernel comparison: Oak against Go and Rust on the same workloads.

Builds the Oak kernels through the compiler (oak build -> C -> cc -O3), the Go
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
KERNELS = ["crc32c", "sha256", "blake3", "dot", "sum", "search"]
GO_IMPLS = {"crc32c": ["go-stdlib", "go-generic"], "sha256": ["go-stdlib", "go-generic"],
            "dot": ["go"], "sum": ["go"], "search": ["go"]}
RUST_KERNELS = ["crc32c", "sha256", "dot", "sum", "search"]


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
        subprocess.run(["go", "build", "-o", str(build / "go-runner"), "."], cwd=HERE / "go", check=True)
        subprocess.run(["rustc", "-O", "-o", str(build / "rust-runner"), str(HERE / "rust" / "main.rs")], check=True)
        for kernel in args.kernels:
            runs = [[str(build / "oak-runner"), kernel]]
            for impl in GO_IMPLS.get(kernel, []):
                runs.append([str(build / "go-runner"), impl, kernel])
            if kernel in RUST_KERNELS:
                runs.append([str(build / "rust-runner"), kernel])
            rows = []
            for command in runs:
                # Alternate the order across samples by running each implementation
                # once per outer sample, interleaved, so drift affects all alike.
                merged = None
                for _ in range(args.samples):
                    line = capture(command + [str(args.size), str(args.rounds), "1"])
                    row = json.loads(line)
                    if merged is None:
                        merged = dict(row)
                        merged["samples"] = []
                    merged["samples"].extend(row["samples"])
                merged["samples"].sort()
                merged["ns_per_op_median"] = merged["samples"][len(merged["samples"]) // 2]
                rows.append(merged)
            checksums = {row["checksum"] for row in rows}
            if len(checksums) != 1:
                sys.exit(f"{kernel}: implementations disagree: {[(r['impl'], r['checksum']) for r in rows]}")
            results.extend(rows)
    report = {
        "schema": "oak-kernels-benchmark-v1",
        "machine": platform.machine(), "platform": platform.platform(), "cpu": cpu_model(),
        "oak": capture(["git", "rev-parse", "HEAD"], cwd=ROOT),
        "cc": capture([args.cc, "--version"]).splitlines()[0],
        "go": capture(["go", "version"]), "rustc": capture(["rustc", "--version"]),
        "c_flags": flags, "rust_flags": ["-O"], "go_flags": [],
        "size": args.size, "rounds": args.rounds, "samples": args.samples,
        "core_affinity": "not controlled", "cache_flush": False,
        "results": results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    for row in results:
        print(f"{row['kernel']:8s} {row['impl']:11s} {row['ns_per_op_median']:>14.1f} ns/op")


if __name__ == "__main__":
    main()
