"""Bind the complete reviewed 658-module DAG without duplicating source files."""
from common import (METADATA_CAP, SOURCE_CAP, digest, encode, expected_rows,
                    module_path, regular_read, require)


def project(stage):
    selected = {module: 'initial' for module in
                ('TypedCNFInstance.Nodes00', 'TypedCNFInstance.Final')}
    for origin in ('refutation', 'data', 'checks', 'permutation', 'nodes', 'bits031', 'bits145', 'reuse'):
        for module in stage.receipt(origin):
            selected[module] = origin
    counts = {'repository': 26, 'refutation': 162, 'typed': 470}
    products, all_modules, imports = {}, set(), {}
    family_bytes = {}
    for family, count in counts.items():
        expected = expected_rows(family, stage)
        require(len(expected) == count, 'expected closure family count')
        rows = []
        for module, sha, size in expected:
            require(module not in all_modules, 'duplicate closure module')
            all_modules.add(module)
            if family == 'repository':
                origin = 'repo'
                raw = stage.read_file(stage.repo / 'spec' / 'lean' / module_path(module), sha, size)
            else:
                require(module in selected, 'missing generated closure source: ' + module)
                origin = selected[module]
                raw = stage.raw(module) if origin == 'initial' else stage.source(origin, module)
                require(digest(raw) == sha and len(raw) == size, 'reviewed closure identity: ' + module)
            dependencies = []
            for line in raw.decode('utf-8').splitlines():
                if line.startswith('import '):
                    dependencies.extend(line.split()[1:])
            imports[module] = dependencies
            rows.append([module, sha, size, origin])
        products[family + '.json'] = encode({'schema': 'typed-cnf-source-inventory-v1',
                                             'family': family, 'modules': rows})
        family_bytes[family] = sum(row[2] for row in rows)
        require(len(products[family + '.json']) <= METADATA_CAP, 'source inventory metadata cap')
    require(len(all_modules) == 658 and set(selected) == all_modules - {m for m in all_modules if m.startswith('Oak.')},
            'complete generated/repository closure inventory')
    # These imports are supplied by the separately pinned Lean distribution.
    standard = {'Init.Data.List.Sort.Lemmas', 'Std.Tactic.BVDecide'}
    require(all(dep in all_modules or dep in standard for deps in imports.values() for dep in deps),
            'unbound local import')
    reached, visiting, order = set(), set(), []

    def visit(module):
        stage.charge(1)
        require(module not in visiting, 'source import cycle')
        if module in reached:
            return
        visiting.add(module)
        for dependency in imports[module]:
            if dependency not in standard:
                visit(dependency)
        visiting.remove(module)
        reached.add(module)
        order.append(module)

    visit('TypedCNFInstance.Final')
    require(reached == all_modules and len(order) == 658, 'final theorem transitive closure')
    sizes = stage.check_physical_caps()
    stage.charge(sum(len(v) for v in products.values()) + METADATA_CAP)
    summary = {'schema': 'typed-cnf-assembled-sources-v1', 'module_count': 658,
               'family_counts': counts, 'family_source_bytes': family_bytes,
               'physical_source_bytes': sizes, 'kernel_checked': False,
               'work': stage.work, 'work_cap': 16777216,
               'inventories': {name: [digest(raw), len(raw)] for name, raw in sorted(products.items())}}
    products['PROJECTION.json'] = encode(summary)
    require(all(len(raw) <= METADATA_CAP for raw in products.values()), 'assembly metadata cap')
    stage.output.mkdir(mode=0o700)
    for name, raw in products.items():
        stage.charge(0)
        with (stage.output / name).open('xb') as stream:
            require(stream.write(raw) == len(raw), 'short inventory write')
    for name, raw in products.items():
        require(regular_read(stage.output / name, METADATA_CAP) == raw, 'published inventory identity')
    print(encode(summary).decode().strip())
