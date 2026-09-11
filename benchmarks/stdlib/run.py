#!/usr/bin/env python3
"""Build the Oak standard-library benchmarks, check every workload's checksum
against the Go reference, time both, and save reproducible samples."""
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
PACKAGES = ("sort", "varint", "encoding", "hash", "random", "uuid", "strings", "time")


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


def parse_lines(text):
    preflight, samples = {}, []
    for raw in text.splitlines():
        raw = raw.strip()
        if not raw:
            continue
        record = json.loads(raw)
        if record["event"] == "preflight":
            preflight[record["workload"]] = record
        elif record["event"] == "sample":
            samples.append(record)
    return preflight, samples


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--scale", type=float, default=1.0, help="corpus size multiplier; 1.0 is the documented size")
    parser.add_argument("--samples", type=int, default=5)
    parser.add_argument("--only", default="", help="workload prefix, e.g. sort/ or encoding/base64")
    parser.add_argument("--cc", default="cc")
    parser.add_argument("--cflags", default="-O2", help="space-separated flags for the Oak C and the bridges")
    parser.add_argument("--sanitize", action="store_true", help="correctness run under ASan/UBSan; not a performance result")
    parser.add_argument("--skip-go", action="store_true", help="time Oak (and C references) only")
    parser.add_argument("--inspect", type=Path, help="save the generated C for inspection")
    args = parser.parse_args()
    if not (0 < args.scale <= 16 and 1 <= args.samples <= 100):
        parser.error("scale must be in (0, 16]; samples 1..100")
    flags = ["-O1", "-g", "-fsanitize=address,undefined"] if args.sanitize else args.cflags.split()
    metadata = {
        "schema": "oak-stdlib-benchmark-v1",
        "mode": "sanitizer correctness" if args.sanitize else "resident corpus, steady state",
        "scale": args.scale, "samples": args.samples, "only": args.only,
        "machine": platform.machine(), "platform": platform.platform(),
        "cpu": cpu_model(), "logical_cpu_count": os.cpu_count(),
        "oak": revision(ROOT),
        "cc": capture([args.cc, "--version"]).splitlines()[0],
        "go": capture(["go", "version"]), "flags": flags,
        "allocation_counts": None, "core_affinity": "not controlled", "cache_flush": False,
        "generated_c_sha256": {},
    }
    commands, preflight, samples = [], {}, []
    with tempfile.TemporaryDirectory(prefix="oak-stdlib-bench-") as tmp:
        build = Path(tmp)
        for package in PACKAGES:
            if args.only and not args.only.startswith(package) and not package.startswith(args.only.split("/")[0]):
                continue
            # Prefixed so a generated file never shadows a system header on the
            # include path (the time package would otherwise produce time.c).
            generated = build / ("oak_" + package + ".c")
            commands.append(["go", "run", ".", "build", "-o", str(generated), str(HERE / "oak" / package)])
            subprocess.run(commands[-1], cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
            metadata["generated_c_sha256"][package] = hashlib.sha256(generated.read_bytes()).hexdigest()
            if args.inspect:
                args.inspect.mkdir(parents=True, exist_ok=True)
                (args.inspect / ("oak_" + package + ".c")).write_bytes(generated.read_bytes())
            binary = build / ("bench_" + package)
            commands.append([args.cc, "-std=c99", *flags, "-I" + str(build), "-I" + str(HERE),
                             str(HERE / "runner.c"), str(HERE / ("bridge_" + package + ".c")), "-o", str(binary)])
            compile = subprocess.run(commands[-1], capture_output=True, text=True)
            if compile.returncode != 0:
                sys.stderr.write(compile.stderr)
                raise SystemExit("C compilation failed for " + package)
            commands.append([str(binary), str(args.scale), str(args.samples)] + ([args.only] if args.only else []))
            pre, runs = parse_lines(capture(commands[-1]))
            preflight.update({name: dict(record, side="oak") for name, record in pre.items()})
            samples.extend(runs)
    go_preflight = {}
    if not args.skip_go:
        commands.append(["go", "run", "./benchmarks/stdlib/goref", str(args.scale), str(args.samples)] + ([args.only] if args.only else []))
        go_preflight, runs = parse_lines(capture(commands[-1], ROOT))
        samples.extend(runs)
    mismatches = []
    for name, record in go_preflight.items():
        if name in preflight and (record["checksum"] != preflight[name]["checksum"] or record["items"] != preflight[name]["items"]):
            mismatches.append({"workload": name, "oak": preflight[name], "go": record})
    if mismatches:
        print(json.dumps(mismatches, indent=2), file=sys.stderr)
        raise SystemExit("preflight checksum mismatch between Oak and Go; not timing a workload whose results differ")
    metadata["commands"] = commands
    summary = {}
    for sample in samples:
        entry = summary.setdefault(sample["workload"], {}).setdefault(sample["backend"], {"ns": [], "items": sample["items"], "bytes": sample["bytes"]})
        entry["ns"].append(sample["ns"])
    table = {}
    for workload, backends in sorted(summary.items()):
        table[workload] = {}
        for backend, entry in backends.items():
            median = statistics.median(entry["ns"])
            table[workload][backend] = {
                "median_ns": median,
                "median_ns_per_item": median / entry["items"],
                "median_mb_per_second": entry["bytes"] / median * 1e9 / 1e6,
                "items": entry["items"], "bytes": entry["bytes"], "runs": len(entry["ns"]),
            }
        if "oak" in table[workload] and "go" in table[workload]:
            table[workload]["oak_over_go_time"] = table[workload]["oak"]["median_ns"] / table[workload]["go"]["median_ns"]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({"metadata": metadata, "summary": table, "preflight": {"oak": preflight, "go": go_preflight}, "samples": samples}, indent=2) + "\n")
    print("| Workload | Oak ns/item | Oak MB/s | Go ns/item | Go MB/s | Oak / Go time | C reference |")
    print("| --- | ---: | ---: | ---: | ---: | ---: | ---: |")
    for workload, backends in table.items():
        oak = backends.get("oak")
        go = backends.get("go")
        others = {k: v for k, v in backends.items() if k not in ("oak", "go", "oak_over_go_time")}
        cell = lambda entry, key, fmt: (fmt % entry[key]) if entry else "—"
        ratio = ("%.2f×" % backends["oak_over_go_time"]) if "oak_over_go_time" in backends else "—"
        reference = ", ".join("%s %.1f ns/item" % (k, v["median_ns_per_item"]) for k, v in others.items()) or "—"
        print("| %s | %s | %s | %s | %s | %s | %s |" % (workload, cell(oak, "median_ns_per_item", "%.2f"), cell(oak, "median_mb_per_second", "%.1f"),
              cell(go, "median_ns_per_item", "%.2f"), cell(go, "median_mb_per_second", "%.1f"), ratio, reference))
    print("Saved", args.output)


if __name__ == "__main__":
    main()
