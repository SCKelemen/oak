#!/usr/bin/env python3
"""Partition non-compiler race coverage without sharing the root test deadline.

The former packages/stdlib lanes both exhausted the root package's cumulative
45-minute timeout on PR #769. Successful root parents in run 39280344580 took
990.30s (CNF A-G), 455.82s (other CNF), and 975.41s (rest); the solver tail was
incomplete. Keep it separate, retain the 45-minute deadline and race detector,
and select every live test, example, and fuzz seed exactly once per workflow.
"""
import collections
import re
import subprocess
import sys

ROOT_PACKAGE = "github.com/SCKelemen/oak"
ROOT_SHARDS = ("root-cnf-a-g", "root-cnf-h-z", "root-solver", "root-rest")
SHARDS = (*ROOT_SHARDS, "packages-rest")
INVENTORY_PATTERN = "^(Test|Example|Fuzz)"
TIMEOUT = "45m"


def validate_inventory(names):
    if not names:
        raise ValueError("root runnable inventory is empty")
    if len(names) != len(set(names)):
        raise ValueError("root runnable inventory contains duplicate names")
    for name in names:
        # -run treats / as a subtest separator, even inside escaped patterns.
        if not re.fullmatch(r"(?:Test|Example|Fuzz)[^/\s]*", name):
            raise ValueError(f"invalid root runnable name: {name!r}")


def run_pattern(names):
    validate_inventory(names)
    return "^(" + "|".join(re.escape(name) for name in sorted(names)) + ")$"


def check_partition(names, partitions):
    validate_inventory(names)
    if set(partitions) != set(ROOT_SHARDS):
        raise ValueError("root partition has missing or unexpected shards")
    assigned = collections.Counter(name for group in partitions.values() for name in group)
    expected = collections.Counter(names)
    if assigned != expected:
        raise ValueError(f"root partition is not exact: missing={expected - assigned}, "
                         f"extra/duplicate={assigned - expected}")
    for shard, selected in partitions.items():
        if not selected:
            raise ValueError(f"root shard {shard} is empty")
        pattern = run_pattern(selected)
        matched = {name for name in names if re.search(pattern, name)}
        if matched != set(selected):
            raise ValueError(f"root shard {shard} selector is not exact")
    return partitions


def partition_roots(names):
    partitions = {shard: [] for shard in ROOT_SHARDS}
    for name in sorted(names):
        if name.startswith("TestOakCNF"):
            initial = name[len("TestOakCNF"):][:1]
            shard = "root-cnf-a-g" if initial and initial in "ABCDEFG" else "root-cnf-h-z"
        elif name.startswith(("TestOakSolver", "TestOakShell", "TestOakLean", "TestOakSyntax")):
            shard = "root-solver"
        else:
            shard = "root-rest"
        partitions[shard].append(name)
    return check_partition(names, partitions)


def root_inventory():
    # Discover through Go, with the same race/platform/build tags as execution.
    # Examples and fuzz seed corpora also run during ordinary `go test`.
    output = subprocess.check_output(
        ["go", "test", "-race", ".", "-list", INVENTORY_PATTERN], text=True,
    )
    names = []
    for line in output.splitlines():
        if re.match(INVENTORY_PATTERN, line):
            names.append(line)
        elif line and not re.match(r"^(ok|\?)\s+" + re.escape(ROOT_PACKAGE) + r"(?:\s|$)", line):
            raise ValueError(f"unexpected root inventory output: {line!r}")
    validate_inventory(names)
    return names


def remaining_packages():
    packages = subprocess.check_output(["go", "list", "./..."], text=True).splitlines()
    if not packages or len(packages) != len(set(packages)):
        raise ValueError("package inventory is empty or contains duplicates")
    if ROOT_PACKAGE not in packages or ROOT_PACKAGE + "/compiler" not in packages:
        raise ValueError("package inventory is missing root or compiler")
    if any(not name.startswith(ROOT_PACKAGE + "/") and name != ROOT_PACKAGE for name in packages):
        raise ValueError("package inventory contains an unexpected import path")
    # Preserve the old grep -v '/compiler$' set exactly, except for the root
    # package now covered by ROOT_SHARDS. No full root run remains here.
    remaining = [name for name in packages if name != ROOT_PACKAGE and not name.endswith("/compiler")]
    if not remaining:
        raise ValueError("remaining package inventory is empty")
    return remaining


def main(args=None):
    args = sys.argv[1:] if args is None else args
    if len(args) != 1 or args[0] not in (*SHARDS, "--check"):
        raise SystemExit("expected --check or one package shard: " + ", ".join(SHARDS))
    try:
        partitions = partition_roots(root_inventory())
        packages = remaining_packages()
        print("complete root partition: " + str({key: len(value) for key, value in partitions.items()}), flush=True)
        print(f"remaining non-compiler packages: {len(packages)}", flush=True)
        if args[0] == "--check":
            return 0
        command = ["go", "test", "-v", "-race", "-timeout", TIMEOUT]
        if args[0] == "packages-rest":
            command += packages
        else:
            # An anchored root-only selector retains every descendant; do not
            # add / filters, -short, -fuzz or -bench.
            command += [".", "-run", run_pattern(partitions[args[0]])]
        subprocess.run(command, check=True)
    except (ValueError, OSError, UnicodeError, subprocess.CalledProcessError) as error:
        print(f"package shard failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
