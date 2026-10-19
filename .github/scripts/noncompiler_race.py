#!/usr/bin/env python3
"""Keep non-compiler race coverage while bounding each root-test batch."""
import re
import subprocess
import sys


def partition(names):
    if not names or len(names) != len(set(names)):
        raise ValueError("empty or duplicate root test inventory")
    # Include examples and fuzz seeds, which ordinary go test also executes.
    if any(not re.fullmatch(r"(?:Test|Example|Fuzz)\w*", n) for n in names):
        raise ValueError("unexpected root test name")
    ordered = sorted(names)
    batches = [ordered[i::4] for i in range(4)]
    assert sorted(n for batch in batches for n in batch) == ordered
    return [batch for batch in batches if batch]


def self_test():
    names = ["TestAlpha", "TestBeta", "TestGamma", "TestDelta", "TestExtra",
             "Example", "Example_output", "FuzzInput"]
    batches = partition(names)
    assert len(batches) == 4
    assert all(len(batch) == 2 for batch in batches)
    assert partition(["TestOnly"]) == [["TestOnly"]]
    for invalid in [[], ["TestA", "TestA"], ["BenchmarkA"], ["TestA|TestB"]]:
        try:
            partition(invalid)
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted invalid inventory: {invalid}")


def main():
    self_test()
    if sys.argv[1:] == ["--self-test"]:
        return
    if sys.argv[1:] not in ([], ["--check"]):
        raise SystemExit("expected no arguments, --check, or --self-test")
    root = subprocess.check_output(["go", "list", "."], text=True).strip()
    packages = subprocess.check_output(["go", "list", "./..."], text=True).splitlines()
    others = [p for p in packages if p not in (root, root + "/compiler")]
    if not root or root not in packages or not others:
        raise ValueError("incomplete package inventory")
    listing = subprocess.check_output(
        ["go", "test", "-race", ".", "-list", "^(Test|Example|Fuzz)"], text=True)
    names = [line for line in listing.splitlines()
             if line.startswith(("Test", "Example", "Fuzz"))]
    batches = partition(names)
    print(f"root race batches: {[len(b) for b in batches]}; other packages: {len(others)}",
          flush=True)
    if sys.argv[1:] == ["--check"]:
        return
    # Retain the previous deadline per invocation and every existing package.
    # Root tests exceeded it cumulatively on run 39261180757.
    for i, batch in enumerate(batches):
        print(f"root race batch {i + 1}/{len(batches)}: {batch}", flush=True)
        pattern = "^(" + "|".join(re.escape(n) for n in batch) + ")$"
        subprocess.run(["go", "test", "-v", "-race", "-count=1", "-timeout", "45m",
                        ".", "-run", pattern], check=True)
    subprocess.run(["go", "test", "-v", "-race", "-timeout", "45m", *others], check=True)


if __name__ == "__main__":
    main()
