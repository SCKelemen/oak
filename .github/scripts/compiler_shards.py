#!/usr/bin/env python3
"""Run a compiler CI shard only after checking the complete test partition."""
import re
import subprocess
import sys

# Keep the race detector and the existing per-shard deadlines. The former
# compiler-rest exceeded 45 minutes cumulatively; no individual test hung.
SHARDS = {
    "e2e-a-r": (r"^TestE2E[A-R]", "90m"),
    "e2e-stdlib-text": (r"^TestE2EStdlibT", "60m"),
    "e2e-stdlib-rest": (r"^TestE2EStd(lib[^T]|[^l])", "90m"),
    "e2e-s-z": (r"^TestE2E(S[^t]|St[^d]|[T-Z])", "45m"),
    "compiler-rest-a-m": (r"^Test([A-D]|E[^2]|E2[^E]|[F-M])", "45m"),
    "compiler-rest-n-z": (r"^Test[^A-M]", "45m"),
}


def check_partition(names, shards=SHARDS):
    if not names:
        raise ValueError("compiler test inventory is empty")
    if len(names) != len(set(names)):
        raise ValueError("compiler test inventory contains duplicate names")
    counts = dict.fromkeys(shards, 0)
    for name in names:
        owners = [shard for shard, (pattern, _) in shards.items()
                  if re.search(pattern, name)]
        if len(owners) != 1:
            raise ValueError(f"{name}: expected exactly one shard, got {owners}")
        counts[owners[0]] += 1
    return counts


def self_test():
    names = [
        "TestE2EArray", "TestE2EStdlibText", "TestE2EStdlibMath",
        "TestE2EStdSomething", "TestE2ESelfHostedPlacement",
        "TestE2EStorage", "TestE2EZ", "TestDifferentialCorpus",
        "TestExtract", "TestE2Other", "TestMathLibrary",
        "TestNativeBlake3", "TestTimehostCompilesEverywhere", "Test_Extra",
    ]
    counts = check_partition(names)
    assert sum(counts.values()) == len(names)
    # Both a missing assignment and an overlapping assignment must fail closed.
    for inventory, shards in [
        ([], SHARDS),
        (["TestE2EUnhandled"], {"only": (r"^TestNative", "45m")}),
        (["TestNative"], {"a": (r"^Test", "45m"), "b": (r"Native", "45m")}),
        (["TestNative", "TestNative"], SHARDS),
    ]:
        try:
            check_partition(inventory, shards)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid partition was accepted")
    # The two replacement shards preserve exactly the old compiler-rest set.
    old = re.compile(r"^Test([^E]|E[^2]|E2[^E])")
    for name in names:
        new = [key for key in ("compiler-rest-a-m", "compiler-rest-n-z")
               if re.search(SHARDS[key][0], name)]
        assert len(new) == int(bool(old.search(name))), name
    print("compiler shard self-tests passed", flush=True)


def main():
    self_test()
    if sys.argv[1:] == ["--self-test"]:
        return
    if len(sys.argv) != 2 or sys.argv[1] not in SHARDS:
        raise SystemExit("expected one compiler shard: " + ", ".join(SHARDS))
    shard = sys.argv[1]
    inventory = subprocess.run(
        ["go", "test", "-race", "./compiler", "-list", "^Test"],
        check=True, text=True, stdout=subprocess.PIPE,
    )
    names = [line for line in inventory.stdout.splitlines()
             if line.startswith("Test")]
    counts = check_partition(names)
    if not counts[shard]:
        raise SystemExit(f"selected shard {shard} is empty")
    print(f"complete compiler partition: {counts}", flush=True)
    pattern, timeout = SHARDS[shard]
    subprocess.run(
        ["go", "test", "-v", "-race", "-timeout", timeout,
         "./compiler", "-run", pattern], check=True,
    )


if __name__ == "__main__":
    main()
