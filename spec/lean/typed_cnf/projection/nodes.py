"""Verbatim Node025..374 factoring and Nodes01..14 import aggregators."""
import re
from common import require, digest as sha256

SUFFIX = b"\nend TypedCNFInstance\n"
AUXILIARIES = {30: "d30left", 35: "d35bool", 118: "d118left"}
DECLARATION = re.compile(
    rb"theorem (d([0-9]+)(?:left|bool)?) : Derivation context "
    rb"(n[0-9]+(?:left|bool)?) (r[0-9]+(?:left|bool)?) := [^\r\n]+\n")
REFERENCE = re.compile(rb"\bd[0-9]+(?:[A-Za-z][A-Za-z0-9]*)?\b")


def declaration_lines(raw):
    return [line for line in raw.splitlines(keepends=True) if line.startswith(b"theorem d")]


def imports_of(raw):
    return [line[len(b"import "):].decode("ascii")
            for line in raw.splitlines() if line.startswith(b"import ")]


def parse_group(raw, group, budget):
    first_line = f"import TypedCNFInstance.Nodes{group - 1:02d}\n".encode()
    require(raw.startswith(first_line) and raw.endswith(SUFFIX), "module boundary mismatch")
    require(imports_of(raw) == [f"TypedCNFInstance.Nodes{group - 1:02d}"], "original import mismatch")
    first_decl = raw.find(b"theorem d")
    require(first_decl > len(first_line), "missing declarations")
    prefix = raw[:first_decl]
    body = raw[first_decl:-len(SUFFIX)]
    require(prefix.count(b"namespace TypedCNFInstance\n") == 1, "namespace mismatch")
    expected_numbers = list(range(25 * group, 25 * (group + 1)))
    buckets = {number: [] for number in expected_numbers}
    ordered, source_lines = [], body.splitlines(keepends=True)
    for line in source_lines:
        budget.charge(len(line))
        if line == b"\n":
            continue
        match = DECLARATION.fullmatch(line)
        require(match is not None, "non-declaration content in proof body")
        name = match.group(1).decode("ascii")
        primary = int(match.group(2))
        require(primary in buckets, "declaration outside owning group")
        suffix = name[1:]
        require(match.group(3).decode() == "n" + suffix and
                match.group(4).decode() == "r" + suffix, "term/root name mismatch")
        require(name == f"d{primary}" or AUXILIARIES.get(primary) == name,
                "unexpected auxiliary")
        buckets[primary].append(line)
        ordered.append((name, line))
    expected_order = []
    for primary in expected_numbers:
        expected_order.extend(([AUXILIARIES[primary]] if primary in AUXILIARIES else []) + [f"d{primary}"])
    require([name for name, _ in ordered] == expected_order, "declaration order/coverage mismatch")
    return first_line, prefix, source_lines, buckets, ordered


def project(stage):
    budget = stage
    outputs, source_rows, stage_order = {}, [], []
    original_declarations, regenerated_declarations = [], []
    source_total = 0
    # These are the exact already checked Nodes00 exports; no proof is assumed anew.
    available = {f"d{number}" for number in range(25)} | {"d3decl", "d11bool"}
    generated_names = []
    for group in range(1, 15):
        name = f"Nodes{group:02d}.lean"
        raw = stage.raw('TypedCNFInstance.' + name[:-5])
        source_total += len(raw)
        old_import, prefix, body_lines, buckets, ordered = parse_group(raw, group, budget)
        restored = {}
        for primary in range(25 * group, 25 * (group + 1)):
            declaration = b"".join(buckets[primary])
            predecessor = (f"TypedCNFInstance.Nodes{group - 1:02d}" if primary == 25 * group
                           else f"TypedCNFInstance.Node{primary - 1:03d}")
            new_import = f"import {predecessor}\n".encode()
            new_prefix = new_import + prefix[len(old_import):]
            result = new_prefix + declaration + SUFFIX
            budget.charge(len(result))
            require(result[len(new_import):len(new_prefix)] == prefix[len(old_import):],
                    "namespace/open/options header changed")
            require(imports_of(result) == [predecessor], "generated predecessor mismatch")
            extracted = declaration_lines(result)
            require(extracted == buckets[primary], "rendered declaration lines changed")
            actual_names = []
            for line in extracted:
                match = DECLARATION.fullmatch(line)
                require(match is not None, "rendered declaration grammar")
                declared = match.group(1).decode("ascii")
                require(declared not in available, "duplicate declaration")
                proof = line.split(b" := ", 1)[1]
                dependencies = [name.decode("ascii") for name in REFERENCE.findall(proof)]
                require(all(dependency in available for dependency in dependencies),
                        f"unavailable derivation dependency: {declared}")
                available.add(declared)
                actual_names.append(declared)
                generated_names.append(declared)
                restored[declared] = line
            expected_names = ([AUXILIARIES[primary]] if primary in AUXILIARIES else []) + [f"d{primary}"]
            require(actual_names == expected_names, "rendered declaration ownership changed")
            relative = f"TypedCNFInstance/Node{primary:03d}.lean"
            require(relative not in outputs, "duplicate output path")
            outputs[relative] = result
            source_rows.append([relative, sha256(result), len(result), [predecessor]])
            stage_order.append(relative)
            regenerated_declarations.extend(extracted)
        # Reconstruct the entire original file, including every original blank separator.
        reconstructed_body = []
        for line in body_lines:
            if line == b"\n":
                reconstructed_body.append(line)
            else:
                match = DECLARATION.fullmatch(line)
                reconstructed_body.append(restored[match.group(1).decode("ascii")])
        require(prefix + b"".join(reconstructed_body) + SUFFIX == raw,
                "full original module reconstruction failed")
        original_declarations.extend(line for _, line in ordered)
        aggregator_relative = f"TypedCNFInstance/Nodes{group:02d}.lean"
        predecessor = f"TypedCNFInstance.Node{25 * (group + 1) - 1:03d}"
        aggregator = f"import {predecessor}\n".encode()
        outputs[aggregator_relative] = aggregator
        source_rows.append([aggregator_relative, sha256(aggregator), len(aggregator), [predecessor]])
        stage_order.append(aggregator_relative)
        budget.charge(len(aggregator))
    require(source_total == 46480, "authenticated node source byte total")
    require(len(generated_names) == 353 and len(set(generated_names)) == 353,
            "declaration count or uniqueness")
    require(original_declarations == regenerated_declarations,
            "ordered declaration reconstruction failed")
    declaration_bytes = b"".join(original_declarations)
    require(len(declaration_bytes) == 41944, "declaration byte total")
    require(len(outputs) == 364, 'split node module count')
    for relative, raw in outputs.items():
        stage.save(relative[:-5].replace('/', '.'), raw)
    stage.finish(364, {'primary_count': 350, 'declaration_count': 353,
                       'declaration_bytes': 41944, 'aggregators': 14,
                       'ordered_declarations_sha256': sha256(declaration_bytes)})
