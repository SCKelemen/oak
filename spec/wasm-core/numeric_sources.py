#!/usr/bin/env python3
"""Prepare and verify the complete, pinned original numeric SpecTec sources.

Run without arguments to require all five sources, or with --fetch to download
only missing sources from their pinned upstream raw URLs. --source-dir overrides
OAK_WASM_NUMERIC_SOURCES; the default is the adjacent upstream directory.

This verifies full original bytes, not semantic correspondence. The separate
Lean source checker must consume these same files to establish its source gate.
"""

import argparse
import hashlib
import json
import os
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from urllib.error import URLError
from urllib.request import Request, urlopen


ROOT = Path(__file__).resolve().parent
DEFAULT_MANIFEST = ROOT / "numeric-sources.json"
REPOSITORY = "https://github.com/WebAssembly/spec"
COMMIT = "970c4116e644e2bf7acb39aab8b733db14ccdf28"
SOURCE_NAMES = (
    "0.1-aux.vars.spectec",
    "1.1-syntax.values.spectec",
    "1.2-syntax.types.spectec",
    "1.3-syntax.instructions.spectec",
    "3.1-numerics.scalar.spectec",
)
STATUS = (
    "Byte provenance only; semantic correspondence requires independent Lean "
    "source checking."
)


class SourceError(RuntimeError):
    """The source manifest, inventory, or original bytes were not accepted."""


@dataclass(frozen=True)
class Source:
    file: str
    path: str
    bytes: int
    sha256: str
    git_blob_sha1: str
    url: str
    raw_url: str


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise SourceError(f"Duplicate manifest key: {key}")
        result[key] = value
    return result


def _exact_keys(value, expected, label):
    if not isinstance(value, dict) or set(value) != set(expected):
        raise SourceError(f"Missing or extra {label} fields")


def load_manifest(path=DEFAULT_MANIFEST):
    """Load the strict five-file inventory; no omitted/extra entries are allowed."""
    try:
        data = json.loads(Path(path).read_text(encoding="utf-8"),
                          object_pairs_hook=_unique_object)
    except (OSError, ValueError) as exc:
        raise SourceError(f"Cannot read numeric source manifest {path}: {exc}") from exc
    _exact_keys(data, ("schema_version", "repository", "commit", "status", "sources"),
                "manifest")
    if (type(data["schema_version"]) is not int or data["schema_version"] != 1
            or data["repository"] != REPOSITORY or data["commit"] != COMMIT
            or data["status"] != STATUS):
        raise SourceError("Unexpected numeric source manifest version, pin, or scope")
    entries = data["sources"]
    if not isinstance(entries, list) or len(entries) != len(SOURCE_NAMES):
        raise SourceError("Missing or extra numeric source manifest entries")
    sources = []
    for entry, name in zip(entries, SOURCE_NAMES):
        _exact_keys(entry, Source.__dataclass_fields__, "source entry")
        source_path = "specification/wasm-3.0/" + name
        if (entry["file"] != name or entry["path"] != source_path
                or entry["url"] != f"{REPOSITORY}/blob/{COMMIT}/{source_path}"
                or entry["raw_url"] != (
                    f"https://raw.githubusercontent.com/WebAssembly/spec/{COMMIT}/"
                    f"{source_path}")):
            raise SourceError(f"Unexpected source name, order, path, or pinned URL: {name}")
        if type(entry["bytes"]) is not int or entry["bytes"] <= 0:
            raise SourceError(f"Invalid source byte length: {name}")
        for key, length in (("sha256", 64), ("git_blob_sha1", 40)):
            if (not isinstance(entry[key], str)
                    or re.fullmatch(f"[0-9a-f]{{{length}}}", entry[key]) is None):
                raise SourceError(f"Invalid {key}: {name}")
        sources.append(Source(**entry))
    return tuple(sources)


def source_directory(source_dir=None):
    """Resolve explicit CLI/API selection, then the environment, then the default."""
    if source_dir is not None:
        return Path(source_dir)
    configured = os.environ.get("OAK_WASM_NUMERIC_SOURCES")
    return Path(configured) if configured else ROOT / "upstream"


def verify_bytes(source, data):
    """Check both digests and the length over the exact original byte sequence."""
    if len(data) != source.bytes:
        raise SourceError(f"Byte length mismatch: {source.file}")
    if hashlib.sha256(data).hexdigest() != source.sha256:
        raise SourceError(f"SHA-256 mismatch: {source.file}")
    header = b"blob " + str(len(data)).encode("ascii") + b"\0"
    if hashlib.sha1(header + data).hexdigest() != source.git_blob_sha1:
        raise SourceError(f"Git blob SHA-1 mismatch: {source.file}")


def _verify_file(source, path):
    if path.is_symlink() or not path.is_file():
        raise SourceError(f"Missing or non-regular numeric source: {path}")
    try:
        verify_bytes(source, path.read_bytes())
    except OSError as exc:
        raise SourceError(f"Cannot read numeric source {path}: {exc}") from exc


def _check_inventory(directory):
    if directory.exists() and not directory.is_dir():
        raise SourceError(f"Numeric source directory is not a directory: {directory}")
    extra = {path.name for path in directory.glob("*.spectec")} - set(SOURCE_NAMES)
    if extra:
        raise SourceError(f"Extra numeric source files: {', '.join(sorted(extra))}")


def _download(source):
    request = Request(source.raw_url, headers={"User-Agent": "oak-numeric-source-gate/1"})
    try:
        with urlopen(request, timeout=60) as response:
            # Do not publish overlong or truncated responses, including error pages.
            data = response.read(source.bytes + 1)
    except (OSError, URLError) as exc:
        raise SourceError(f"Could not fetch {source.raw_url}: {exc}") from exc
    verify_bytes(source, data)
    return data


def prepare_sources(source_dir=None, *, fetch=False, manifest_path=DEFAULT_MANIFEST):
    """Verify all originals, atomically installing only verified missing files.

    Existing wrong files are errors, including under --fetch. No source file is
    overwritten. Each missing file is downloaded and checked before publication;
    temporary downloads are removed on failure. The returned paths are in the
    exact manifest order. Callers must still run the independent Lean checker.
    """
    sources = load_manifest(manifest_path)
    directory = source_directory(source_dir)
    _check_inventory(directory)
    missing = []
    for source in sources:
        path = directory / source.file
        if path.exists() or path.is_symlink():
            _verify_file(source, path)
        else:
            missing.append(source)
    if missing and not fetch:
        names = ", ".join(source.file for source in missing)
        raise SourceError(f"Missing numeric source files in {directory}: {names}; run --fetch")
    if missing:
        directory.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix=".numeric-sources-", dir=directory) as tmp:
            for source in missing:
                data = _download(source)
                temporary = Path(tmp) / source.file
                with temporary.open("xb") as output:
                    output.write(data)
                    output.flush()
                    os.fsync(output.fileno())
            for source in missing:
                target = directory / source.file
                try:
                    # A hard link publishes complete bytes atomically without
                    # replacing a concurrently created destination.
                    os.link(Path(tmp) / source.file, target)
                except FileExistsError:
                    _verify_file(source, target)
    _check_inventory(directory)
    paths = tuple(directory / source.file for source in sources)
    for source, path in zip(sources, paths):
        _verify_file(source, path)
    return paths


def verify_sources(source_dir=None, *, manifest_path=DEFAULT_MANIFEST):
    """Require and verify all files, with no network requests or file writes."""
    return prepare_sources(source_dir, manifest_path=manifest_path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch", action="store_true",
                        help="download only missing files and verify all original bytes")
    parser.add_argument("--source-dir", type=Path,
                        help="override OAK_WASM_NUMERIC_SOURCES and the upstream default")
    args = parser.parse_args()
    try:
        paths = prepare_sources(args.source_dir, fetch=args.fetch)
    except (SourceError, OSError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    print(f"PASS: exact pinned bytes verified for {len(paths)} numeric sources in "
          f"{source_directory(args.source_dir)}; not semantic verification.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
