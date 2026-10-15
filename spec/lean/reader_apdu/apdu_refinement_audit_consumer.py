"""Finite APDU refinement audit consumer, adapted from the accepted consumer.

No compiler, process, control, repair, or historical-session imports. The caller
authenticates the contract, distribution, driver, and successful compilation.
"""
import time
from support import decode, require

ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}
FORBIDDEN = {'sorryAx', 'Lean.trustCompiler', 'Lean.ofReduceBool',
             'Lean.ofReduceNat', 'Lean.reduceBool', 'Lean.reduceNat'}
KINDS = {'axiom', 'definition', 'theorem', 'opaque', 'quotient',
         'inductive', 'constructor', 'recursor'}
MODULES = {'Oak.Stdlib.APDULengthModel', 'Oak.Stdlib.APDUParserHelperProofs',
           'Oak.Stdlib.BoundedReaderExtracted', 'Oak.Stdlib.APDUModelErrorContracts',
           'Oak.Stdlib.APDUExtracted', 'Oak.Stdlib.APDUParserRefinement',
           'Oak.Stdlib.APDUParserControls', 'Oak.Stdlib.APDUReaderBridge',
           'Oak.Stdlib.BoundedReaderRefinement', 'Oak.Stdlib.BoundedReaderModel',
           'Oak.Stdlib.APDUParserCorrectness'}
PREFIX = 'OAK_READER_REFINEMENT_AUDIT '


def text(value):
    require(type(value) is str and 0 < len(value.encode('utf-8', 'strict')) <= 65536
            and '\x00' not in value, 'bounded nonempty exact name')
    return value


def names(value, cap=100000, unique=False):
    require(type(value) is list and len(value) <= cap, 'finite name-array bound')
    for name in value:
        text(name)
    require(not unique or len(value) == len(set(value)), 'duplicate name forbidden')
    return value


def keys(record, wanted):
    require(type(record) is dict and set(record) == set(wanted.split()),
            'exact audit record schema')


def axioms(value):
    names(value, 3, True)
    require(set(value) <= ALLOWED, 'only approved foundational axioms')
    return set(value)


def position(value):
    require(type(value) is dict and set(value) == {'line', 'column'} and
            all(type(v) is int and 0 <= v <= 2**32 - 1 for v in value.values()),
            'message position')


def diagnostics(stdout, stderr, phase, deadline, driver_path, contract):
    require(time.monotonic() < deadline and stderr == b'', 'complete stderr must be empty')
    if phase != 'audit':
        require(stdout == b'', 'compile phases must have no diagnostics')
        return None
    require(0 < len(stdout) <= 12582912 and stdout.endswith(b'\n'),
            'complete bounded audit stdout')
    lines = stdout.split(b'\n')
    require(lines[-1] == b'' and 1 <= len(lines) - 1 <= 14282,
            'finite complete audit message count')
    out = []
    for line in lines[:-1]:
        require(time.monotonic() < deadline and line,
                'audit parsing original deadline/empty line')
        message = decode(line)
        keys(message, 'fileName pos endPos keepFullRange severity isSilent caption data kind')
        require(message['fileName'] == str(driver_path) and
                message['severity'] == 'information' and message['isSilent'] is False and
                message['keepFullRange'] is False and message['caption'] == '' and
                message['kind'] == '[anonymous]' and type(message['data']) is str and
                message['data'].startswith(PREFIX),
                'only exact driver informational audit messages; no unsupported diagnostics')
        position(message['pos'])
        position(message['endPos'])
        out.append(decode(message['data'][len(PREFIX):].encode('utf-8', 'strict')))
    return audit_records(out, deadline, contract)


def audit_records(records, deadline, contract):
    require(time.monotonic() < deadline and type(records) is list and
            1 <= len(records) <= 14282, 'finite complete audit records/original deadline')
    require(type(contract) is dict and 'expected' in contract and
            'distribution_modules' in contract, 'supplied audit contract')
    expected = contract['expected']
    keys(expected, 'theorems anonymous_controls named_controls')
    require(type(expected['theorems']) is list and len(expected['theorems']) == 280,
            '280 exact theorem entries')
    order = []
    for theorem in expected['theorems']:
        keys(theorem, 'module qualified_name private')
        require(text(theorem['module']) in MODULES and type(theorem['private']) is bool,
                'expected theorem owner/private type')
        order.append((theorem['module'], text(theorem['qualified_name']), theorem['private']))
    wanted = set(order)
    require(len(wanted) == 280, '280 unique exact theorems')
    examples = expected['anonymous_controls']
    require(type(examples) is list and len(examples) == 15, '15 source examples')
    example_positions = set()
    for example in examples:
        keys(example, 'module line')
        require(text(example['module']) in MODULES and type(example['line']) is int and
                1 <= example['line'] <= 2**32 - 1, 'exact anonymous source position')
        example_positions.add((example['module'], example['line']))
    require(len(example_positions) == 15, '15 distinct source examples')
    controls = names(expected['named_controls'], 41, True)
    require(len(controls) == 41 and set(controls) <= {row[1] for row in order},
            '41 named controls in theorem inventory')
    distribution = names(contract['distribution_modules'], 1047, True)
    require(len(distribution) == 1047 and not (set(distribution) & MODULES),
            'exact distribution module graph')
    keys(records[0], 'record modules')
    require(records[0]['record'] == 'imports', 'one first import record')
    imports = names(records[0]['modules'], 1058, True)
    require(set(imports) == set(distribution) | MODULES, 'exact actual imported module set')
    theorems = {}
    triples = set()
    candidates = {}
    nodes = {}
    state = 'expected_theorem'
    complete = None
    for index, record in enumerate(records[1:], 1):
        require(time.monotonic() < deadline and type(record) is dict,
                'audit original deadline/record type')
        kind = record.get('record')
        if kind == 'expected_theorem':
            require(state == 'expected_theorem' and len(theorems) < 280,
                    'theorem section/order/count')
            keys(record, 'record owner user_name actual_name private axioms direct_dependencies')
            require(type(record['private']) is bool, 'exact private boolean')
            triple = (text(record['owner']), text(record['user_name']), record['private'])
            name = text(record['actual_name'])
            require(triple == order[len(theorems)] and triple in wanted and
                    triple not in triples and name not in theorems and name not in FORBIDDEN,
                    'unique exact theorem resolution')
            if not record['private']:
                require(name == record['user_name'], 'public theorem exact actual name')
            else:
                require(name.startswith('_private.'), 'private actual-name marker')
            axioms(record['axioms'])
            names(record['direct_dependencies'])
            triples.add(triple)
            theorems[name] = record
        elif kind == 'candidate_declaration':
            require(state in ('expected_theorem', 'candidate_declaration') and
                    len(theorems) == 280 and len(candidates) < 4000,
                    'candidate section/order/count')
            state = kind
            keys(record, 'record actual_name user_name owner kind axioms direct_dependencies')
            name = text(record['actual_name'])
            text(record['user_name'])
            require(name not in candidates and name not in FORBIDDEN and
                    record['owner'] in MODULES and record['kind'] in KINDS - {'axiom'},
                    'unique safe candidate ownership/kind')
            axioms(record['axioms'])
            names(record['direct_dependencies'])
            candidates[name] = record
        elif kind == 'dependency':
            require(state in ('candidate_declaration', 'dependency') and candidates and
                    len(nodes) < 10000, 'dependency section/order/count')
            state = kind
            keys(record, 'record actual_name kind direct_dependencies')
            name = text(record['actual_name'])
            require(name not in nodes and name not in FORBIDDEN and record['kind'] in KINDS and
                    (record['kind'] != 'axiom' or name in ALLOWED),
                    'unique approved dependency kind')
            names(record['direct_dependencies'])
            nodes[name] = record
        elif kind == 'complete':
            require(state == 'dependency' and complete is None and index == len(records) - 1,
                    'exactly one last complete sentinel')
            keys(record, 'record expected_theorems candidate_declarations dependency_nodes '
                 'dependency_edges anonymous_examples_persisted '
                 'anonymous_examples_accounted_by_exact_source_compile')
            require(all(type(record[name]) is int for name in
                        ('expected_theorems', 'candidate_declarations', 'dependency_nodes',
                         'dependency_edges', 'anonymous_examples_accounted_by_exact_source_compile')),
                    'completion integer counters')
            require(type(record['anonymous_examples_persisted']) is bool and
                    record['anonymous_examples_persisted'] is False, 'examples do not persist')
            complete = record
            state = 'complete'
        else:
            raise RuntimeError('unknown audit record')
    require(complete is not None and triples == wanted and len(theorems) == 280 and
            len(candidates) == 2226 and 1 <= len(nodes) <= 10000, 'complete inventories')
    edges = sum(len(record['direct_dependencies']) for record in nodes.values())
    require(edges <= 100000, 'combined edge-occurrence cap')
    require(complete == {'record': 'complete', 'expected_theorems': 280,
                         'candidate_declarations': len(candidates), 'dependency_nodes': len(nodes),
                         'dependency_edges': edges, 'anonymous_examples_persisted': False,
                         'anonymous_examples_accounted_by_exact_source_compile': 15},
            'completion reconciliation')
    for node in nodes.values():
        require(all(dependency in nodes for dependency in node['direct_dependencies']),
                'every referenced dependency present')
    for name, candidate in candidates.items():
        require(name in nodes and candidate['kind'] == nodes[name]['kind'] and
                candidate['direct_dependencies'] == nodes[name]['direct_dependencies'],
                'candidate and shared graph equality')
    for name, theorem in theorems.items():
        require(name in candidates and candidates[name]['kind'] == 'theorem' and
                all(candidates[name][key] == theorem[key] for key in
                    ('owner', 'user_name', 'direct_dependencies')) and
                set(candidates[name]['axioms']) == set(theorem['axioms']),
                'theorem/candidate record equality')
    processed = 0
    walk_edges = 0

    def walk(roots):
        nonlocal processed, walk_edges
        todo = list(roots)
        seen = set()
        reached_axioms = set()
        count = 0
        while todo:
            require(time.monotonic() < deadline, 'graph reconstruction original deadline')
            name = todo.pop()
            if name in seen:
                continue
            seen.add(name)
            processed += 1
            require(len(seen) <= 10000 and processed <= 2810000, 'independent node bounds')
            node = nodes[name]
            if node['kind'] == 'axiom':
                reached_axioms.add(name)
            dependencies = node['direct_dependencies']
            count += len(dependencies)
            walk_edges += len(dependencies)
            require(count <= 100000 and walk_edges <= 28100000 and
                    len(todo) + len(dependencies) <= 100000, 'independent edge/pending bounds')
            todo.extend(dependencies)
        return seen, reached_axioms

    all_seen, _ = walk(candidates)
    require(all_seen == set(nodes), 'no extra or missing combined dependency node')
    for name, theorem in theorems.items():
        _, actual = walk([name])
        require(actual == set(theorem['axioms']) <= ALLOWED,
                'independent theorem reachable axioms')
    return {'schema': 'oak-apdu-parser-refinement-audit-acceptance-v1', 'accepted': True,
            'actual_imports': len(imports), 'named_theorems': 280, 'source_examples': 15,
            'named_controls': 41, 'anonymous_examples_persisted': False,
            'candidate_declarations': len(candidates), 'dependency_nodes': len(nodes),
            'dependency_edges': edges, 'independent_processed_nodes': processed,
            'independent_edge_occurrences': walk_edges, 'allowed_axioms': sorted(ALLOWED),
            'imported_distribution_normal_trust': True,
            'implementation_refinement_established': False,
            'generated_definition_refinement_established': True,
            'oak_implementation_refinement_established': False}
