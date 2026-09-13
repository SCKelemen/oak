#!/usr/bin/env python3
"""Time Oak's rings (stdlib/rings.oak) between threads, and Go's channels on
the same shapes (benchmarks/rings/README.md). Run from the repository root:

    python3 benchmarks/rings/run.py --output benchmarks/rings/rings-<date>-<machine>.json
"""
import argparse
import hashlib
import json
import os
import platform
import statistics
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def capture(args, cwd=None):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def revision(path):
    return {
        "sha": capture(["git", "rev-parse", "HEAD"], path),
        "tracked_changes": bool(capture(["git", "status", "--porcelain", "--untracked-files=no"], path)),
    }


def cpu_model():
    if platform.system() == "Darwin":
        return capture(["sysctl", "-n", "machdep.cpu.brand_string"])
    try:
        for line in Path("/proc/cpuinfo").read_text().splitlines():
            if line.startswith("model name"):
                return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return platform.processor() or platform.machine()


def lines(text):
    return [json.loads(raw) for raw in text.splitlines() if raw.strip()]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True)
    parser.add_argument("--samples", type=int, default=5)
    parser.add_argument("--items", type=int, default=2000000)
    parser.add_argument("--cc", default="cc")
    parser.add_argument("--cflags", default="-O2")
    parser.add_argument("--skip-go", action="store_true")
    parser.add_argument("--inspect", help="keep the generated C in this directory")
    args = parser.parse_args()
    flags = args.cflags.split()
    metadata = {
        "schema": "oak-rings-benchmark-v1",
        "mode": "wall time of the whole transfer, producers and consumers on pthreads, checksum verified",
        "items": args.items, "samples": args.samples, "capacity": 1024,
        "machine": platform.machine(), "platform": platform.platform(),
        "cpu": cpu_model(), "logical_cpu_count": os.cpu_count(),
        "oak": revision(ROOT),
        "cc": capture([args.cc, "--version"]).splitlines()[0],
        "go": capture(["go", "version"]), "flags": flags,
        "core_affinity": "not controlled",
    }
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(args.inspect) if args.inspect else Path(tmp)
        work.mkdir(parents=True, exist_ok=True)
        generated = work / "rings.c"
        subprocess.check_call(["go", "run", ".", "build", "-o", str(generated), str(HERE / "oak")], cwd=ROOT)
        source = generated.read_text() + (HERE / "bench.c").read_text()
        (work / "bench_all.c").write_text(source)
        metadata["generated_c_sha256"] = hashlib.sha256(generated.read_bytes()).hexdigest()
        oak_samples = {}
        # Two producer policies when the ring is full: spin on the push (the
        # Oak loop) and yield the core (the C loop calling the Oak push).
        for policy, define in (("spin", []), ("yield", ["-DYIELD"])):
            binary = work / ("rings_bench_" + policy)
            subprocess.check_call([args.cc, "-std=c11", *flags, "-pthread", "-Wno-parentheses-equality", f"-DITEMS={args.items}u", *define, "-o", str(binary), str(work / "bench_all.c")])
            for _ in range(args.samples):
                for record in lines(capture([str(binary)])):
                    oak_samples.setdefault(record["ring"] + "/" + policy, []).append(record)
        go_samples = {}
        if not args.skip_go:
            goref = work / "goref"
            subprocess.check_call(["go", "build", "-o", str(goref), "."], cwd=HERE / "goref")
            for _ in range(args.samples):
                for record in lines(capture([str(goref)])):
                    go_samples.setdefault(record["ring"], []).append(record)
    results = {}
    for ring, records in oak_samples.items():
        ns = [r["ns_per_item"] for r in records]
        results[ring] = {
            "threads": records[0]["threads"],
            "oak_ns_per_item": statistics.median(ns), "oak_ns_per_item_min": min(ns), "oak_ns_per_item_max": max(ns),
            "producer_spins_median": statistics.median(r["producer_spins"] for r in records),
        }
        base = ring.split("/")[0].replace("_ticket", "")
        if base in go_samples:
            gns = [r["ns_per_item"] for r in go_samples[base]]
            results[ring]["go_channel_ns_per_item"] = statistics.median(gns)
            results[ring]["oak_over_go_time"] = statistics.median(ns) / statistics.median(gns)
    Path(args.output).write_text(json.dumps({"metadata": metadata, "results": results}, indent=2) + "\n")
    for ring, r in results.items():
        go = f", Go channel {r['go_channel_ns_per_item']:.1f} ns/item ({r['oak_over_go_time']:.2f}x)" if "go_channel_ns_per_item" in r else ""
        print(f"{ring:16s} {r['threads']:26s} Oak {r['oak_ns_per_item']:.1f} ns/item{go}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
