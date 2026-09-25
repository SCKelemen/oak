#!/usr/bin/env python3
"""Prepare checked four-language reductions; measure only by explicit opt-in."""
import argparse
import datetime
import hashlib
import json
import math
import os
import platform
import re
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE = HERE.parent / "paired_loads/sums.oak"
IMPLEMENTATIONS = ("oak-native", "c", "rust", "zig")
CHECK_SIZES = (0, 1, 3, 4, 7, 8, 15, 16, 31, 32, 511, 512, 513, 4096)
SCHEMA = "oak-four-way-reductions-v1"


def capture(argv, **kwargs):
    return subprocess.check_output(argv, text=True, timeout=600, **kwargs).strip()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    with path.open("x") as output:
        json.dump(value, output, indent=2)
        output.write("\n")


def source_hashes():
    paths = [SOURCE, *sorted(HERE.glob("*.py")), HERE / "runner.c", HERE / "sums.rs", HERE / "sums.zig"]
    return {str(path.relative_to(ROOT)): digest(path) for path in paths}


def compiler_source_hashes():
    # Actual build dependencies, not concurrently edited tests/proof generators.
    packages = capture(["go", "list", "-deps", "-json", "./benchmarks/native/emit"], cwd=ROOT)
    paths = {ROOT / "go.mod", ROOT / "go.sum"}
    decoder = json.JSONDecoder()
    while packages:
        package, end = decoder.raw_decode(packages)
        packages = packages[end:].lstrip()
        if package.get("Standard"):
            continue
        directory = Path(package["Dir"])
        for field in ("GoFiles", "CgoFiles", "CFiles", "HFiles", "SFiles", "SysoFiles", "EmbedFiles"):
            paths.update(directory / name for name in package.get(field, []))
    if len(paths) == 2:
        raise ValueError("no compiler build inputs discovered")
    return {str(path.relative_to(ROOT) if path.is_relative_to(ROOT) else path): digest(path)
            for path in sorted(paths)}


def host():
    try:
        cpu = capture(["sysctl", "-n", "machdep.cpu.brand_string"], stderr=subprocess.DEVNULL)
    except (OSError, subprocess.SubprocessError):
        cpu = None
    return {"platform": platform.platform(), "machine": platform.machine(), "cpu": cpu,
            "logical_cpus": os.cpu_count(), "load_average": list(os.getloadavg())}


def oracle(width, elements):
    random, total = 42, 0
    mask = (1 << width) - 1
    for _ in range(elements):
        random = (random * 6364136223846793005 + 1) & ((1 << 64) - 1)
        total = (total + (random >> 32 if width == 32 else random)) & mask
    return f"{total:016x}"


def accept_row(row, mode, implementation, width, elements, calls, expected):
    identity = {"mode": mode, "implementation": implementation, "width": width,
                "elements": elements, "calls": calls}
    if (not isinstance(row, dict) or implementation not in IMPLEMENTATIONS or
            any(type(row.get(k)) is not type(v) or row[k] != v for k, v in identity.items())):
        raise ValueError("runner identity mismatch")
    keys = {*identity, "checksum"} | ({"elapsed_ns"} if mode == "measure" else set())
    if set(row) != keys or row["checksum"] != expected:
        raise ValueError("runner schema/checksum mismatch")
    if mode == "measure" and (type(row["elapsed_ns"]) is not int or row["elapsed_ns"] <= 0):
        raise ValueError("invalid elapsed_ns")
    return row


def selected_bodies(diagnostics):
    bodies = {}
    for name in ("sum32", "sum64"):
        if f"asm unit {name}: proven equal to its Oak body" not in diagnostics:
            raise ValueError(f"{name}: missing native proven verdict")
        matches = re.findall(rf"^{name} = \{{\n.*?^\}}", diagnostics, re.M | re.S)
        if not matches:
            raise ValueError(f"{name}: missing selected native body")
        bodies[name] = {"verdict": "proven", "assembly": matches[-1]}
    return bodies


def zig_target(diagnostics):
    cpu = re.search(r"^  cpu: (\S+)$", diagnostics, re.M)
    features = re.search(r"^  features: (.+)$", diagnostics, re.M)
    if not cpu or not features or "+neon" not in features[1].split(","):
        raise ValueError("Zig target CPU/NEON capability missing")
    return {"cpu": cpu[1], "neon": True, "llvm_features": features[1]}


def verify_artifacts(build, report):
    if report.get("schema") != SCHEMA or report.get("state") != "correctness-passed-timing-pending":
        raise ValueError("not a prepared four-way manifest")
    if report.get("source_sha256") != source_hashes():
        raise ValueError("benchmark sources changed since preparation")
    required = {"runner", "emit", "kernels.c", "kernels.o", "c.o", "rust.o", "zig.o"}
    artifacts = report.get("artifacts_sha256", {})
    if not required <= artifacts.keys():
        raise ValueError("missing required comparison artifact")
    for name, expected in artifacts.items():
        path = (build / name).resolve()
        if path.parent != build.resolve() or digest(path) != expected:
            raise ValueError(f"artifact changed or outside build directory: {name}")
    wanted = {(impl, width, n) for impl in IMPLEMENTATIONS for width in (32, 64) for n in CHECK_SIZES}
    observed = set()
    for row in report.get("correctness", []):
        key = row["implementation"], row["width"], row["elements"]
        if key not in wanted or key in observed:
            raise ValueError("duplicate/unexpected correctness row")
        accept_row(row, "check", *key, 1, oracle(key[1], key[2]))
        observed.add(key)
    if observed != wanted or set(report.get("native_bodies", {})) != {"sum32", "sum64"}:
        raise ValueError("incomplete correctness/proof manifest")
    if any(body.get("verdict") != "proven" for body in report["native_bodies"].values()):
        raise ValueError("unproven native body")


def prepare(args):
    build = args.artifacts.resolve()
    build.mkdir(parents=True, exist_ok=False)
    source_before, compiler_before = source_hashes(), compiler_source_hashes()
    status = capture(["git", "status", "--porcelain"], cwd=ROOT)
    report = {"schema": SCHEMA, "state": "correctness-passed-timing-pending",
              "date_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "revision": capture(["git", "rev-parse", "HEAD"], cwd=ROOT),
              "worktree_status": status,
              "tracked_diff_sha256": hashlib.sha256(subprocess.check_output(["git", "diff", "HEAD"], cwd=ROOT)).hexdigest(),
              "source_sha256": source_before, "compiler_source_sha256": compiler_before,
              "host": host(), "tools": {}, "commands": [], "correctness": [],
              "semantics": "unsigned modular sums; initialized aligned input; len is u32",
              "abi": "ARM64 C ABI: pointer then u32 length, 16-byte view",
              "comparison": "independent C, Rust, Zig objects; Oak native object plus generated C declarations/runtime",
              "target_policy": "C/Rust generic ARM64; Zig macOS baseline (resolved CPU recorded); not M4 tuning or identical feature sets",
              "deployment_target": "macOS 13.0",
              "lto": False, "timing": None,
              "limits": ["Two reduction microkernels, not representative language parity.",
                         "Check mode never reads a benchmark clock.",
                         "No affinity, thermal, power, or host-isolation guarantee."]}
    for name, requested, version in (("cc", args.cc, "--version"), ("rustc", args.rustc, "--version"),
                                     ("zig", args.zig, "version"), ("go", "go", "version")):
        found = shutil.which(requested)
        if not found:
            raise ValueError(f"required compiler unavailable: {requested}")
        path = str(Path(found).resolve())
        report["tools"][name] = {"path": path, "version": capture([path, version]), "sha256": digest(Path(path))}
    env = {key: value for key, value in os.environ.items() if not key.startswith("OAK_")}
    env.update(OAK_VERIFY_CACHE="0", OAK_NATIVE_ONLY="sum32,sum64", OAK_NATIVE_DUMP="selected",
               MACOSX_DEPLOYMENT_TARGET="13.0")
    report["oak_environment"] = {key: value for key, value in env.items() if key.startswith("OAK_")}

    def command(argv):
        index = len(report["commands"])
        result = subprocess.run([str(arg) for arg in argv], cwd=ROOT, env=env,
                                capture_output=True, text=True, timeout=600)
        (build / f"command-{index}.stdout").write_text(result.stdout)
        (build / f"command-{index}.stderr").write_text(result.stderr)
        report["commands"].append({"argv": [str(arg) for arg in argv], "exit_code": result.returncode})
        write_json(build / f"command-{index}.json", report["commands"][-1])
        if result.returncode:
            raise RuntimeError(f"build command {index} failed; see {build}/command-{index}.stderr")
        return result.stdout, result.stderr

    cc, rustc, zig, go = (report["tools"][name]["path"] for name in ("cc", "rustc", "zig", "go"))
    command([go, "build", "-o", build / "emit", "./benchmarks/native/emit"])
    _, diagnostics = command([build / "emit", SOURCE, build / "kernels"])
    report["native_bodies"] = selected_bodies(diagnostics)
    report["emitter_build_info"] = capture([go, "version", "-m", str(build / "emit")])
    flags = ["-std=c11", "-O3", "-mcpu=generic", "-mmacosx-version-min=13.0", "-fno-lto", "-ffp-contract=off", "-fno-fast-math"]
    command([cc, *flags, "-DFOUR_WAY_REFERENCE", "-c", HERE / "runner.c", "-o", build / "c.o"])
    command([rustc, "--edition=2021", "--crate-type=lib", "--emit=obj", "-C", "opt-level=3",
             "-C", "target-cpu=generic", "-C", "panic=abort", "-C", "lto=off", HERE / "sums.rs", "-o", build / "rust.o"])
    _, features = command([zig, "build-obj", "-O", "ReleaseFast", "-target", "aarch64-macos.13.0", "-mcpu=baseline", "-fno-lto", "-fllvm",
             "--verbose-llvm-cpu-features",
             "--cache-dir", build / "zig-cache", "--global-cache-dir", build / "zig-global-cache",
             HERE / "sums.zig", f"-femit-bin={build / 'zig.o'}"])
    report["zig_target"] = zig_target(features)
    command([cc, *flags, "-I", build, HERE / "runner.c", build / "kernels.o", build / "c.o",
             build / "rust.o", build / "zig.o", "-o", build / "runner", "-lm"])
    disassembly, _ = command(["xcrun", "llvm-objdump", "-d", "--no-show-raw-insn", build / "runner"])
    (build / "runner.disassembly").write_text(disassembly)
    for width in (32, 64):
        for n in CHECK_SIZES:
            expected = oracle(width, n)
            for implementation in IMPLEMENTATIONS:
                row = json.loads(capture([str(build / "runner"), "check", implementation, str(width), str(n), "1"]))
                report["correctness"].append(accept_row(row, "check", implementation, width, n, 1, expected))
    if source_before != source_hashes() or compiler_before != compiler_source_hashes():
        raise ValueError("benchmark or compiler sources changed during preparation; rerun")
    report["artifacts_sha256"] = {path.name: digest(path) for path in sorted(build.iterdir()) if path.is_file()}
    verify_artifacts(build, report)
    write_json(build / "prepared.json", report)
    print(f"Prepared: 2 proven Oak bodies; {len(report['correctness'])} correctness rows; timings pending. {build / 'prepared.json'}")


def quiet_host(prepared, max_load):
    current = host()
    if not current["cpu"] or any(current[key] != prepared[key] for key in ("cpu", "machine", "logical_cpus")):
        raise ValueError("CPU identity unavailable or differs from prepared host")
    if any(value > max_load for value in current["load_average"]):
        raise ValueError(f"host is not quiet enough: {current['load_average']}")
    return current


def measure(args):
    if not args.confirm_host_quiet:
        raise ValueError("measurement requires --confirm-host-quiet after stopping builds and other host work")
    if not args.output or args.output.exists():
        raise ValueError("measurement requires a new --output path")
    build = args.artifacts.resolve()
    report = json.loads((build / "prepared.json").read_text())
    verify_artifacts(build, report)
    before = quiet_host(report["host"], args.max_load)
    rows = []
    variants = [(impl, width) for impl in IMPLEMENTATIONS for width in (32, 64)]
    for n in args.elements:
        expected = {width: oracle(width, n) for width in (32, 64)}
        for round_ in range(args.samples):
            for offset in range(len(variants)):
                quiet_host(report["host"], args.max_load)
                impl, width = variants[(round_ + offset) % len(variants)]
                row = json.loads(capture([str(build / "runner"), "measure", impl, str(width), str(n), str(args.calls)]))
                accept_row(row, "measure", impl, width, n, args.calls, expected[width])
                rows.append(dict(row, round=round_, ns_per_element=row["elapsed_ns"] / (n * args.calls)))
    after = quiet_host(report["host"], args.max_load)
    verify_artifacts(build, report)
    write_json(args.output, {"schema": SCHEMA, "prepared_manifest": str(build / "prepared.json"),
                            "prepared_sha256": digest(build / "prepared.json"), "date_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                            "host_before": before, "host_after": after, "max_load": args.max_load,
                            "host_quiet_confirmed_by_operator": True, "core_affinity": "uncontrolled", "cache_flush": False,
                            "sample_order": "rotating implementation/width first each round", "samples": rows,
                            "limits": "Load guard and operator confirmation do not prove isolation or representative parity."})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("prepare", "measure"))
    parser.add_argument("--artifacts", required=True, type=Path)
    parser.add_argument("--cc", default="clang")
    parser.add_argument("--rustc", default="rustc")
    parser.add_argument("--zig", default="zig")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--confirm-host-quiet", action="store_true")
    parser.add_argument("--max-load", type=float, default=1.0)
    parser.add_argument("--samples", type=int, default=9)
    parser.add_argument("--elements", type=int, nargs="+", default=[7, 4096, 1 << 20])
    parser.add_argument("--calls", type=int, default=128)
    args = parser.parse_args()
    if platform.system() != "Darwin" or platform.machine() != "arm64":
        parser.error("ARM64 macOS is required")
    if (args.samples not in range(1, 100, 2) or not 1 <= args.calls <= 1 << 20 or
            not math.isfinite(args.max_load) or args.max_load <= 0 or not args.elements or
            len(set(args.elements)) != len(args.elements) or any(not 1 <= n <= 1 << 20 for n in args.elements)):
        parser.error("invalid sample count (odd 1..99), calls/elements (1..1048576), or positive finite load limit")
    if args.mode == "prepare":
        prepare(args)
    else:
        measure(args)


if __name__ == "__main__":
    main()
