#!/usr/bin/env python3
"""Build both native decoders and save reproducible, preflight-checked samples."""
import argparse
import hashlib
import json
import os
import platform
import shutil
import statistics
import subprocess
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--simdjson", required=True, type=Path, help="local simdjson git checkout")
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--documents", type=int, default=1024)
    parser.add_argument("--rounds", type=int, default=100)
    parser.add_argument("--samples", type=int, default=5)
    parser.add_argument("--cc", default="cc")
    parser.add_argument("--cxx", default="c++")
    parser.add_argument("--sanitize", action="store_true", help="correctness run; not a performance result")
    parser.add_argument("--inspect", type=Path, help="save generated C and assembly for inspection")
    args = parser.parse_args()
    if not (1 <= args.documents <= 1000000 and 1 <= args.rounds <= 1000000 and 1 <= args.samples <= 100):
        parser.error("documents/rounds must be 1..1000000; samples 1..100")
    simdjson = args.simdjson.resolve()
    for name in ("simdjson.h", "simdjson.cpp"):
        if not (simdjson / "singleheader" / name).is_file():
            parser.error("simdjson checkout must contain singleheader/" + name)
    flags = ["-O1", "-g", "-fsanitize=address,undefined"] if args.sanitize else ["-O3", "-DNDEBUG"]
    metadata = {
        "schema": "oak-json-benchmark-v1",
        "workload": "required id:u64 active:Bool samples:[4]i32; full typed decoding",
        "corpus": "deterministic-v1; alternating key order; escaped keys; integer boundaries",
        "mode": "sanitizer correctness" if args.sanitize else "resident corpus, reused parser, steady state",
        "machine": platform.machine(), "platform": platform.platform(),
        "cpu": cpu_model(), "logical_cpu_count": os.cpu_count(),
        "oak": revision(ROOT), "simdjson": revision(simdjson),
        "cc": capture([args.cc, "--version"]), "cxx": capture([args.cxx, "--version"]),
        "go": capture(["go", "version"]), "flags": flags,
        "documents_per_round": args.documents, "rounds": args.rounds, "samples": args.samples,
        "allocation_counts": None,  # Not instrumented; never infer counts from throughput.
        "core_affinity": "not controlled", "cache_flush": False,
    }
    commands = []
    with tempfile.TemporaryDirectory(prefix="oak-json-bench-") as tmp:
        build = Path(tmp)
        shutil.copyfile(HERE / "schema.oak", build / "schema.oak")
        commands.append(["go", "run", ".", str(build / "schema.oak")])
        subprocess.run(commands[-1], cwd=ROOT, check=True)
        metadata["generated_c_sha256"] = hashlib.sha256((build / "schema.c").read_bytes()).hexdigest()
        commands.append([args.cc, "-std=c99", *flags, "-I" + str(build), "-c", str(HERE / "bridge.c"), "-o", str(build / "oak.o")])
        subprocess.run(commands[-1], check=True)
        if args.inspect:
            args.inspect.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(build / "schema.c", args.inspect / "schema.c")
            commands.append([args.cc, "-std=c99", *flags, "-I" + str(build), "-S", str(HERE / "bridge.c"), "-o", str(args.inspect / "oak.s")])
            subprocess.run(commands[-1], check=True)
            assembly = (args.inspect / "oak.s").read_text()
            # Print the derived reader and its callees for remote inspection.
            for name in ("oak___oak_json_read_BenchRecord", "oak___oak_json_read_i32", "oak_json_read_integer", "oak_json_key_equal"):
                start = assembly.find("\n_" + name + ":")
                if start < 0:
                    start = assembly.find("\n" + name + ":")
                if start >= 0:
                    end = assembly.find(".cfi_endproc", start)
                    print(assembly[start:end + len(".cfi_endproc")])
        commands.append([args.cxx, "-std=c++17", *flags, "-pthread", "-I" + str(simdjson / "singleheader"), str(HERE / "runner.cpp"), str(simdjson / "singleheader/simdjson.cpp"), str(build / "oak.o"), "-o", str(build / "benchmark")])
        subprocess.run(commands[-1], check=True)
        commands.append([str(build / "benchmark"), str(args.documents), str(args.rounds), str(args.samples)])
        lines = capture(commands[-1]).splitlines()
    records = [json.loads(line) for line in lines]
    metadata.update(records[0])
    metadata["commands"] = commands
    samples = records[1:]
    if len(samples) != args.samples * 2:
        raise RuntimeError("missing benchmark samples")
    summary = {}
    for backend in ("oak", "simdjson_ondemand"):
        selected = [sample for sample in samples if sample["backend"] == backend]
        summary[backend] = {
            "median_ns_per_document": statistics.median(s["ns"] / s["documents"] for s in selected),
            "median_bytes_per_second": statistics.median(s["bytes"] * 1e9 / s["ns"] for s in selected),
        }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({"metadata": metadata, "summary": summary, "samples": samples}, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    print("Saved", args.output)


if __name__ == "__main__":
    main()
