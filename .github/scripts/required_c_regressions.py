#!/usr/bin/env python3
"""Require fresh Go/Oak ROR twins and portable C value-branch execution."""
import hashlib
import json
import os
from pathlib import Path
import secrets
import shutil
import subprocess
import sys
import tempfile

from required_backend_tests import Suite, run_suite

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "testdata/ror_consistency.json"
VALUE_BRANCHES = (
    "last_assignment_in_statement_branch",
    "nested_declarations_and_sibling_scopes",
    "condition_once_and_left_to_right_effects",
    "enclosing_local_read_before_branch_write",
    "short_circuit_and_skipped_traps",
    "loop_condition_reevaluates_declarations",
    "aggregate_result_and_call_argument",
    "scalar_match_arms",
    "defer_follows_branch_value",
    "atomic_storage_paths_retain_identity_and_index_order",
)


def source_digest():
    # Hash the actual contents, including staged/unstaged edits and new source
    # files, rather than trusting HEAD or the nonce. Receipts live outside this
    # tree. No environment variables or Git metadata enter the digest.
    paths = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
        cwd=ROOT,
    ).split(b"\0")
    paths = sorted(set(path for path in paths if path))
    if not paths:
        raise ValueError("source tree is empty")
    digest = hashlib.sha256()
    for path in paths:
        data = (ROOT / os.fsdecode(path)).read_bytes()
        digest.update(len(path).to_bytes(8, "big") + path)
        digest.update(len(data).to_bytes(8, "big") + data)
    return digest.hexdigest()


def require_source(expected):
    if source_digest() != expected:
        raise ValueError("source tree changed during required C regression checks")


def suite(package, root, names):
    return Suite(package, "3m", (root, *(root + "/" + name for name in names)))


def check_receipt(path, source, run, fixture, names):
    if path.is_symlink() or not path.is_file():
        raise ValueError("Go twin producer did not create a fresh regular receipt")
    document = json.loads(path.read_bytes())
    if (not isinstance(document, dict) or document.get("schema") != 1
            or document.get("source_sha256") != source or document.get("run") != run
            or document.get("fixture_sha256") != hashlib.sha256(fixture).hexdigest()):
        raise ValueError("stale or substituted Go twin receipt")
    cases = document.get("cases")
    if (not isinstance(cases, list) or len(cases) != 30
            or any(not isinstance(case, dict) for case in cases)
            or [case.get("name") for case in cases] != names):
        raise ValueError("incomplete or reordered Go twin receipt")


def run():
    if shutil.which("cc") is None:
        raise ValueError("required C regression lane needs cc on PATH")
    fixture = FIXTURE.read_bytes()
    document = json.loads(fixture)
    names = [case["name"] for case in document["cases"]]
    if (document.get("schema") != 1 or len(names) != 30 or len(set(names)) != 30
            or any(not isinstance(name, str) or not name or "/" in name for name in names)):
        raise ValueError("expected exactly 30 distinct serialized ROR fixtures")
    source = source_digest()
    print("Required C regressions source SHA256: " + source, flush=True)
    with tempfile.TemporaryDirectory(prefix="oak-required-c-") as directory:
        receipt = Path(directory) / "ror-twin.json"
        run_id = secrets.token_hex(32)
        # Overlays and external workspaces can compile different source bytes
        # from the checkout we just hashed. Ignore persistent go-env defaults too.
        env = dict(os.environ, GOENV="off", GOFLAGS="", GOWORK="off",
                   OAK_REQUIRE_CC="1", OAK_REQUIRE_ROR_TWIN="1",
                   OAK_ROR_TWIN_RECEIPT=str(receipt), OAK_ROR_TWIN_SOURCE=source,
                   OAK_ROR_TWIN_RUN=run_id)
        binding = dict(source_sha256=source, run=run_id,
                       fixture_sha256=hashlib.sha256(fixture).hexdigest(),
                       required_cc=True, required_twin=True, race=True,
                       goenv="off", goflags="", gowork="off")
        print("Required C regressions launch: " + json.dumps(binding, sort_keys=True), flush=True)
        # Each command requires the exact root and every child to PASS, rejects
        # all nested skips, and must exit successfully before consuming output.
        run_suite(suite("./asm", "TestRotateConsistencySerializedTwinFixtures", names), race=True, env=env)
        require_source(source)
        check_receipt(receipt, source, run_id, fixture, names)
        receipt_bytes = receipt.read_bytes()
        run_suite(suite(".", "TestOakRORConsistency", names), race=True, env=env)
        if receipt.read_bytes() != receipt_bytes:
            raise ValueError("Go twin receipt changed during consumption")
        print("Required C regressions consumer: " + json.dumps(
            dict(binding, receipt_sha256=hashlib.sha256(receipt_bytes).hexdigest(),
                 producer_passes=31, consumer_passes=31), sort_keys=True), flush=True)
        run_suite(suite("./compiler", "TestE2EValueBranchDeclarations", VALUE_BRANCHES), race=True, env=env)
        require_source(source)


def main():
    try:
        os.chdir(ROOT)
        run()
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print(f"Required C regressions FAILED: {error}", file=sys.stderr, flush=True)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
