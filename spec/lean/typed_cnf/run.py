#!/usr/bin/env python3
"""Mandatory clean-checkout supplied-instance gate. Never runs a SAT solver.

`generate` stops after the authenticated source inventory for local review;
`build` resumes that same ledger. CI uses `all`. Every stage is one-shot, serial,
and bounded. This tool deliberately has no skip, resume-failed or retry option.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

from supervise import (encoded, publish, regular, require, sha,
                       check_dependencies, check_sources, output_guard, subreaper, bytes_in, check_observation)
from ownership import OwnedProcesses
from process_observation import ProcessObservation
from observed_subprocess import run as observed_run
from observation_acceptance import check_acceptance_controls
from ledger import Ledger

ROOT = Path(__file__).resolve().parent
TOTAL_SECONDS = 9000
PROJECTIONS = ['refutation', 'data', 'checks', 'permutation', 'nodes', 'bits031', 'bits145', 'reuse', 'assemble']
TESTS = ['TestTypedCNF' + name for name in [
    'ArithmeticWidths', 'ViewsShiftsAndGuards', 'ReadEmbedding', 'Adversarial',
    'LimitsAndConcurrentCalls', 'MuxPins', 'DurableFixture', 'FixtureJSONBoundaries',
    'FixtureManifestBoundaries', 'FixtureGraphBoundaries', 'FixtureFileBoundaries',
    'FixtureIdentityBoundaries', 'FixtureCancellation', 'InstanceWriterBoundaries']]
SELECTOR = '^(' + '|'.join(TESTS) + ')$'
THEOREM = 'TypedCNFInstance.supplied_raw_implication'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def tool(path):
    resolved = Path(shutil.which(str(path)) or str(path)).resolve(strict=True)
    require(resolved.is_file() and os.access(resolved, os.X_OK), 'required executable missing: ' + str(path))
    return str(resolved)


def version(command, kind, env, owner):
    result = observed_run(owner, 'preflight.'+kind+'-version', command, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, env=env, timeout=5, check=True)
    require(len(result.stdout) < 4096, 'tool version output cap')
    output = result.stdout.decode().strip()
    if kind == 'go':
        match = re.fullmatch(r'go version (\S+) (\S+)', output)
        require(match is not None and match.groups() == ('go1.27.1', 'linux/amd64'), 'exact Go release required')
    else:
        match = re.match(r'Lean \(version ([^, )]+)(?:,|\))', output)
        require(match is not None and match[1] == '4.33.1', 'exact Lean release required')
    return output


def shard(rows, root, prefix, reusable=()):
    chunks, current = [], []
    for row in rows:
        candidate = current + [row]
        if len(encoded(candidate)) > 60000:
            require(bool(current), 'single manifest row too large')
            chunks.append(current)
            current = [row]
        else:
            current = candidate
    if current:
        chunks.append(current)
    prior = {}
    for path, expected in reusable:
        require(sha(path) == expected, 'reusable manifest identity')
        prior.setdefault(expected, path)
    result = []
    for index, chunk in enumerate(chunks):
        raw = encoded(chunk)
        expected = hashlib.sha256(raw).hexdigest()
        if expected in prior:
            # rows came from a fresh complete enumeration/hash pass. Compare
            # actual canonical bytes as well as the authenticated digest.
            path = prior[expected]
            require(regular(path, 65536) == raw, 'reusable manifest byte mismatch')
            result.append([str(path), expected])
            continue
        path = root / ('%s-%03d.json' % (prefix, index))
        publish(path, chunk, 65536)
        result.append([str(path), sha(path)])
    return result


def source_rows(repo):
    # Include all repository Go compilation inputs, module pins, the complete
    # local Lean source and this gate, plus fixture and workflow metadata.
    suffixes = {'.go', '.s', '.S', '.c', '.h'}
    selected = set()
    for path in repo.rglob('*'):
        relative = path.relative_to(repo)
        if any(part in {'.git', '.lake', '__pycache__', 'external'} for part in relative.parts):
            continue
        if path.is_file() and (path.suffix in suffixes or str(relative) in {'go.mod', 'go.sum'}):
            selected.add(path)
    for root in [repo / 'spec/lean/Oak', ROOT, repo / 'asm/testdata/typed_cnf']:
        for path in root.rglob('*'):
            if path.is_file() and '__pycache__' not in path.parts:
                selected.add(path)
    selected.add(repo / 'spec/lean/lean-toolchain')
    selected.add(repo / '.github/workflows/typed-cnf.yml')
    return [[str(path.relative_to(repo)), sha(path)] for path in sorted(selected)]


def toolchain_rows(lean, go, modcache):
    rows = []
    # The release's entire Lean import library and Go installation are recorded
    # once, then rehashed at terminal closure. Neither is an output/import cache.
    for root in [Path(lean).parent.parent, Path(go).parent.parent, Path(modcache)]:
        require(root.is_dir() and not root.is_symlink(), 'tool/dependency root')
        for path in sorted(root.rglob('*')):
            if path.is_symlink():
                require(path.resolve().is_relative_to(root), 'tool/dependency symlink escape')
                rows.append([str(path), 'symlink:' + os.readlink(path), 0])
                continue
            if path.is_file():
                rows.append([str(path), sha(path), path.stat().st_size])
    return rows


def task_configuration(work):
    # This private task data never changes the caller's Go/user configuration.
    # Keep HOME and configuration inside evidence so every later write is capped.
    work = Path(work)
    for name in ['task-home', 'task-config', 'task-config/go', 'task-config/go/telemetry']:
        (work / 'evidence' / name).mkdir(mode=0o700)
    mode = work / 'evidence/task-config/go/telemetry/mode'
    with mode.open('xb') as stream:
        require(stream.write(b'off\n') == 4, 'short task telemetry mode write')
    return [[str(mode), sha(mode)]]


def environment(config):
    work = Path(config['work'])
    paths = sorted({str(Path(value).parent) for value in config['tools'].values()})
    env = {'PATH': os.pathsep.join(paths + ['/usr/bin', '/bin']),
           'HOME': str(work / 'evidence/task-home'),
           'XDG_CONFIG_HOME': str(work / 'evidence/task-config'),
           'GIT_CONFIG_NOSYSTEM': '1', 'GIT_CONFIG_GLOBAL': '/dev/null', 'GIT_OPTIONAL_LOCKS': '0',
           'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8',
           'TMPDIR': str(work / 'tmp'), 'PYTHONDONTWRITEBYTECODE': '1', 'PYTHONHASHSEED': '0',
           'GOENV': 'off', 'GOWORK': 'off', 'GOTOOLCHAIN': 'local', 'GOOS': 'linux',
           'GOARCH': 'amd64', 'GOAMD64': 'v1', 'CGO_ENABLED': '1', 'GOMAXPROCS': '2',
           'GOMEMLIMIT': '2GiB', 'GOPROXY': 'off', 'GOSUMDB': 'off', 'GOFLAGS': '-mod=readonly',
           'GOEXPERIMENT': '', 'GODEBUG': '', 'CGO_CFLAGS': '', 'CGO_CPPFLAGS': '',
           'CGO_CXXFLAGS': '', 'CGO_LDFLAGS': '', 'CC': config['tools']['cc'],
           'CXX': config['tools']['cxx'], 'GOROOT': str(Path(config['tools']['go']).parent.parent),
           'GOCACHE': str(work / 'go-cache'), 'GOPATH': str(work / 'go-path'),
           'GOMODCACHE': config['modcache'], 'LEAN_PATH': str(work / 'lib'),
           'LEAN_SYSROOT': str(Path(config['tools']['lean']).parent.parent), 'LEAN_NUM_THREADS': '1'}
    return env


def prepare(args, ledger, owner):
    repo = args.repo.resolve(strict=True)
    require(args.work.is_absolute() and args.work.name not in {'.', '..'}, 'absolute work path required')
    work = args.work.parent.resolve(strict=True) / args.work.name
    require(ROOT == repo / 'spec/lean/typed_cnf', 'runner must belong to selected repository')
    require(not work.exists() and not work.is_symlink() and work.parent.is_dir(), 'fresh work root required')
    require(not work.is_relative_to(repo), 'work root must be outside clean repository')
    require(not work.is_relative_to(ledger.root) and not ledger.root.is_relative_to(work), 'work and ledger roots must be disjoint')
    git = tool('git')
    git_env = {'PATH': '/usr/bin:/bin', 'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8',
               'HOME': str(work / 'evidence/task-home'), 'XDG_CONFIG_HOME': str(work / 'evidence/task-config'),
               'GIT_CONFIG_NOSYSTEM': '1', 'GIT_CONFIG_GLOBAL': '/dev/null', 'GIT_OPTIONAL_LOCKS': '0'}
    clean = observed_run(owner, 'preflight.git-status', [git, '-C', str(repo), 'status', '--porcelain', '--untracked-files=all'],
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=git_env, timeout=10, check=True)
    require(not clean.stdout, 'clean checkout required, including untracked inputs')
    tools = {name: tool(value) for name, value in {
        'go': args.go, 'lean': args.lean, 'python': sys.executable,
        'timeout': '/usr/bin/timeout', 'cc': args.cc, 'cxx': args.cxx, 'git': git}.items()}
    require(sys.version_info[:2] >= (3, 12) and sys.platform == 'linux', 'Linux and Python 3.12+ required')
    modcache = args.modcache.resolve(strict=True)
    work.mkdir(mode=0o700)
    for name in ['evidence', 'evidence/manifests', 'evidence/specifications', 'evidence/runs',
                 'generated', 'generated/raw', 'generated/projection', 'lib', 'tmp', 'go-cache', 'go-path', 'bin']:
        (work / name).mkdir()
    task_inputs = task_configuration(work)
    env = environment({'work': str(work), 'tools': tools, 'modcache': str(modcache)})
    versions = {'go': version([tools['go'], 'version'], 'go', env, owner),
                'lean': version([tools['lean'], '--version'], 'lean', env, owner)}
    source_manifests = shard(source_rows(repo), work / 'evidence/manifests', 'source')
    chain_manifests = shard(toolchain_rows(tools['lean'], tools['go'], modcache),
                            work / 'evidence/manifests', 'toolchain',
                            reusable=ledger.tool_manifest_references())
    identity = observed_run(owner, 'preflight.git-identity', [git, '-C', str(repo), 'rev-parse', 'HEAD', 'HEAD^{tree}'],
                            stdout=subprocess.PIPE, env=git_env, timeout=5, check=True).stdout.decode().splitlines()
    config = {'schema': 'oak-typed-cnf-clean-gate-v1', 'repo': str(repo), 'work': str(work),
              'commit': identity[0], 'tree': identity[1], 'tools': tools,
              'ledger': str(ledger.root), 'allocation_sha256': ledger.identity,
              'tool_hashes': {name: sha(path) for name, path in tools.items()},
              'versions': versions, 'modcache': str(modcache), 'task_inputs': task_inputs,
              'source_manifests': source_manifests,
              'toolchain_manifests': chain_manifests, 'cumulative_seconds': TOTAL_SECONDS,
              'historical_attempts_charged_here': 0, 'module_count': 738,
              'ordinary_stage_seconds': 180, 'rss_bytes': 4026531840,
              'minimum_memory_bytes': 2147483648, 'minimum_disk_bytes': 536870912,
              'aggregate_objects_bytes': 1073741824, 'aggregate_evidence_bytes': 33554432,
              'per_family_source_bytes': 8388608, 'combined_source_bytes': 16777216}
    publish(work / 'evidence/config.json', config, 65536)
    return config


class Gate:
    def __init__(self, config, ledger, owner):
        self.config = config
        self.work = Path(config['work'])
        self.repo = Path(config['repo'])
        self.env = environment(config)
        self.previous = None
        self.receipts = []
        self.ledger, self.owner = ledger, owner
        require(config['ledger'] == str(ledger.root) and config['allocation_sha256'] == ledger.identity, 'allocation binding')
        self.spent = ledger.spent()

    def recover_generated(self):
        names = ['ownership-controls', 'compile', 'normal', 'race', 'emit'] + ['project-' + name for name in PROJECTIONS]
        for name in names:
            self.accept(name)
        self.tests_passed('normal', TESTS)
        self.tests_passed('race', TESTS)
        self.tests_passed('emit', ['TestTypedCNFEmitInstance'])

    def accept(self, name):
        path = self.work / 'evidence/runs' / name / 'stage.json'
        receipt = json.loads(regular(path, 14336))
        outer = json.loads(regular(path.parent / 'execution.json', 14336))
        require(outer['stage_receipt_sha256'] == sha(path) and outer['returncode'] == 0 and
                outer['remaining_descendants'] == 0 and outer['error'] is None, 'outer execution incomplete')
        self.spent = self.ledger.spent()
        reference = [str(path), sha(path), sha(path.parent / 'execution.json')]
        self.receipts.append(reference)
        require(self.spent <= TOTAL_SECONDS, 'cumulative construction budget exhausted')
        require(receipt['stage'] == name and receipt['returncode'] == 0 and
                receipt['stop_reason'] is None and receipt['supervisor_error'] is None and
                receipt['remaining_descendants'] == 0, 'incomplete stage: ' + name)
        check_dependencies([reference], set())
        self.previous = reference
        return receipt

    def stage(self, name, command, *, seconds=180, products=(), trees=(), cwd=None,
              extra_env=None, dependencies=None, inputs=()):
        self.spent = self.ledger.spent()
        remaining = math.floor(TOTAL_SECONDS - self.spent)
        seconds = min(seconds, remaining)
        require(seconds > 4, 'cumulative construction budget exhausted')
        env = dict(self.env)
        env.update(extra_env or {})
        bound_inputs = [[str(self.work / 'evidence/config.json'), sha(self.work / 'evidence/config.json')]]
        bound_inputs += [[path, self.config['tool_hashes'][key]] for key, path in self.config['tools'].items()]
        bound_inputs += self.config.get('task_inputs', [])
        bound_inputs += [[str(path), sha(path)] for path in inputs]
        spec = {'schema': 'oak-typed-cnf-stage-v1', 'name': name, 'repo': str(self.repo),
                'work': str(self.work), 'artifact_work_roots': self.ledger.work_roots(str(self.work)),
                'ledger_root': str(self.ledger.root), 'directory': str(self.work / 'evidence/runs' / name),
                # Publication tail: 3x64-KiB observations + 3x14-KiB
                # receipts + 64-KiB one-tree inventory + 2-KiB products +
                # 4-KiB ledger finish + 4-KiB outer records + 2-KiB poison
                # is 310 KiB; reserve 384 KiB inside the same 32-MiB cap.
                'observation_reserve_bytes': 393216,
                'command': [str(value) for value in command], 'cwd': str(cwd or self.repo),
                'env': env, 'seconds': seconds, 'inputs': bound_inputs,
                'source_manifests': self.config['source_manifests'],
                'dependencies': dependencies if dependencies is not None else ([self.previous] if self.previous else []),
                'products': [str(path) for path in products], 'tree_products': [str(path) for path in trees]}
        path = self.work / 'evidence/specifications' / (name + '.json')
        publish(path, spec, 65536)
        reservation = self.ledger.reserve(name, seconds, self.work / 'evidence/config.json', path)
        started = time.monotonic()
        command = [self.config['tools']['timeout'], '--signal=TERM', '--kill-after=3s', str(seconds-4)+'s',
                   self.config['tools']['python'], '-B', str(ROOT / 'supervise.py'), str(path), sha(path), repr(started)]
        watcher = None
        code, error, remaining_descendants, reaped = 125, None, None, 0
        cleanup_error = observation_error = observation_reference = None
        invocation_observer = self.owner.observer
        observation = ProcessObservation('execution:'+name)
        self.owner.observer = observation
        self.owner.observe('bind', self.owner.root)
        receipt_path = self.work / 'evidence/runs' / name / 'stage.json'
        execution_path = self.work / 'evidence/runs' / name / 'execution.json'
        try:
            watcher = subprocess.Popen(command, stdin=subprocess.DEVNULL, env=env)
            self.owner.observe('spawned', self.owner, watcher.pid, 'stage supervisor watcher')
            code = watcher.wait()
            self.owner.observe('joined_decoded', watcher.pid, code, 'watcher.wait')
        except BaseException as caught:
            error = repr(caught)[:1024]
        finally:
            # Only this live runner's positively identified descendants can be
            # signalled. Handles pin processes against PID/group-ID reuse.
            try:
                cleanup = self.owner.cleanup(seconds=max(0, min(1, started+seconds-time.monotonic())))
                reaped, remaining_descendants = cleanup['reaped'], cleanup['remaining']
                if reaped or remaining_descendants:
                    error = error or 'runner had to clean an incomplete stage tree'
            except BaseException as caught:
                error = error or ('owned cleanup failed: ' + repr(caught)[:512])
                cleanup_error = repr(caught)[:1024]
            execution_path.parent.mkdir(exist_ok=True)
            try:
                observation_reference = observation.publish(execution_path.parent / 'execution-processes.json')
                check_observation(observation_reference, execution_path.parent)
                require(self.owner.observation_error is None, 'execution observer failed')
            except BaseException as caught:
                observation_error = repr(caught)[:512]
                error = error or observation_error
            finally:
                self.owner.observer = invocation_observer
            duration = time.monotonic()-started
            if not receipt_path.exists():
                error = error or 'missing terminal supervisor receipt'
            if duration >= seconds:
                error = error or 'outer total stage deadline'
            if error is not None:
                code = 125
            execution_path.parent.mkdir(exist_ok=True)
            publish(execution_path, {'schema': 'typed-cnf-owned-execution-v1', 'stage': name,
                    'spec_sha256': sha(path), 'returncode': code, 'wall_seconds': duration,
                    'stage_receipt_sha256': sha(receipt_path) if receipt_path.exists() else None,
                    'remaining_descendants': remaining_descendants, 'reaped_descendants': reaped,
                    'process_observation': observation_reference, 'observation_error': observation_error,
                    'cleanup_error': cleanup_error,
                    'error': error}, 14336)
            self.ledger.finish(reservation, execution_path)
        require(code == 0, 'outer execution failed: '+name)
        receipt = self.accept(name)
        print(json.dumps({'stage': name, 'seconds': duration,
                          'remaining_seconds': TOTAL_SECONDS-self.spent}), flush=True)
        return receipt

    def tests_passed(self, stage, expected):
        raw = regular(self.work / 'evidence/runs' / stage / 'stage.log', 65536).decode()
        require('--- SKIP:' not in raw and '--- FAIL:' not in raw, 'required test skipped/failed')
        starts = re.findall(r'^=== RUN   (Test[^/\s]+)$', raw, re.M)
        passes = re.findall(r'^--- PASS: (Test[^/\s]+) \(', raw, re.M)
        require(sorted(starts) == sorted(expected) and sorted(passes) == sorted(expected), 'required test execution set')

    def generate(self):
        self.stage('ownership-controls', [self.config['tools']['python'], '-B', ROOT / 'ownership_controls.py'], seconds=15)
        binary = self.work / 'bin/asm-typed.test'
        go = self.config['tools']['go']
        self.stage('compile', [go, 'test', '-p', '1', '-c', '-o', binary, './asm'], seconds=120, products=[binary])
        self.stage('normal', [binary, '-test.run='+SELECTOR, '-test.v', '-test.timeout=80s'],
                   seconds=90, cwd=self.repo / 'asm')
        self.tests_passed('normal', TESTS)
        self.stage('race', [go, 'test', '-race', '-failfast', '-p', '1', '-count=1', '-timeout=90s',
                           './asm', '-run', SELECTOR, '-v'], seconds=120)
        self.tests_passed('race', TESTS)
        initial = self.work / 'generated/raw/TypedCNFInstance'
        self.stage('emit', [binary, '-test.run=^TestTypedCNFEmitInstance$', '-test.v', '-test.timeout=150s'],
                   trees=[initial], cwd=self.repo / 'asm', extra_env={'OAK_TYPED_CNF_INSTANCE_OUT': str(initial)})
        self.tests_passed('emit', ['TestTypedCNFEmitInstance'])
        for name in PROJECTIONS:
            target = self.work / 'generated/projection' / name
            self.stage('project-'+name, [self.config['tools']['python'], '-B', ROOT / 'projection/project.py', name,
                       '--repo-root', self.repo, '--instance-root', self.work / 'generated/raw',
                       '--work-root', self.work / 'generated/projection'], trees=[target])
        self.freeze_build()

    def module_rows(self):
        rows = []
        for family, expected_count in [('repository', 26), ('refutation', 162), ('typed', 550)]:
            raw = regular(self.work / 'generated/projection/assemble' / (family+'.json'), 65536)
            inventory = json.loads(raw)
            require(inventory['schema'] == 'typed-cnf-source-inventory-v1' and inventory['family'] == family,
                    'module family schema')
            family_rows = inventory['modules']
            require(isinstance(family_rows, list) and len(family_rows) == expected_count, 'module family inventory')
            rows.extend(family_rows)
        require(len(rows) == 738 and len({row[0] for row in rows}) == 738, 'exact logical module inventory')
        return rows

    def freeze_build(self):
        mapping = {}
        for module, expected, size, origin in self.module_rows():
            require(re.fullmatch(r'(Oak|TypedCNFInstance|TypedCNFRefutation)\.[A-Za-z][A-Za-z0-9]*', module), 'module name')
            require(origin in {'repo', 'initial'} or origin in PROJECTIONS, 'module origin')
            root = (self.repo / 'spec/lean' if origin == 'repo' else
                    self.work / 'generated/raw' if origin == 'initial' else self.work / 'generated/projection' / origin)
            source = root / (module.replace('.', '/') + '.lean')
            require(source.stat().st_size == size and sha(source) == expected, 'generated source identity: '+module)
            imports = re.findall(r'^import ([A-Za-z0-9_.]+)$', regular(source, 8*1024*1024).decode(), re.M)
            mapping[module] = {'module': module, 'source': str(source), 'root': str(root),
                               'sha256': expected, 'bytes': size, 'imports': imports}
        order, visiting, visited = [], set(), set()
        def visit(module):
            require(module not in visiting, 'local import cycle')
            if module in visited:
                return
            visiting.add(module)
            for imported in mapping[module]['imports']:
                if imported.startswith(('Oak.', 'TypedCNFInstance.', 'TypedCNFRefutation.')):
                    require(imported in mapping, 'unbound local import: '+imported)
                    visit(imported)
            visiting.remove(module)
            visited.add(module)
            order.append(mapping[module])
        visit('TypedCNFInstance.Final')
        require(len(order) == 738, 'inventory is not exactly the final import closure')
        manifests = shard(order, self.work / 'evidence/manifests', 'build')
        publish(self.work / 'evidence/build-plan.json', {'schema': 'typed-cnf-frozen-build-v1',
                'module_count': 738, 'modules': manifests, 'source_generation_receipts': self.receipts,
                'spent_seconds': self.spent, 'remaining_seconds': TOTAL_SECONDS-self.spent}, 65536)

    def build(self):
        raw = regular(self.work / 'evidence/build-plan.json', 65536)
        plan = json.loads(raw)
        require(plan['source_generation_receipts'] == self.receipts, 'generation predecessor binding')
        rows = []
        for path, expected in plan['modules']:
            require(sha(path) == expected, 'frozen module plan identity')
            rows.extend(json.loads(regular(path, 65536)))
        require(len(rows) == 738 and len({row['module'] for row in rows}) == 738, 'frozen module count')
        expected_sources = {row[0]: row for row in self.module_rows()}
        seen = set()
        for row in rows:
            module, expected, size, origin = expected_sources[row['module']]
            root = (self.repo / 'spec/lean' if origin == 'repo' else self.work / 'generated/raw'
                    if origin == 'initial' else self.work / 'generated/projection' / origin)
            source = root / (module.replace('.', '/')+'.lean')
            require(row['source'] == str(source) and row['root'] == str(root) and
                    row['sha256'] == expected and row['bytes'] == size and sha(source) == expected,
                    'build plan differs from authenticated generation')
            imports = re.findall(r'^import ([A-Za-z0-9_.]+)$', regular(source, 8*1024*1024).decode(), re.M)
            require(imports == row['imports'], 'build import identity')
            require(all(name in seen for name in imports if name in expected_sources), 'build dependency order')
            seen.add(module)
        outputs = list((self.work / 'lib').rglob('*'))
        require(not outputs, 'fresh sole project import root required')
        succeeded = {}
        for row in rows:
            module = row['module']
            source = Path(row['source'])
            require(sha(source) == row['sha256'], 'source changed after freeze')
            output = self.work / 'lib' / (module.replace('.', '/') + '.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            dependencies = [succeeded[name] for name in row['imports'] if name in succeeded]
            # The generation chain authenticates all fixture/projection inputs.
            dependencies.append(plan['source_generation_receipts'][-1])
            command = [self.config['tools']['lean'], '-j1', '--root='+row['root'], '-o', output, source]
            self.stage('lean-'+module, command, products=[output], dependencies=dependencies, inputs=[source])
            succeeded[module] = self.previous
        self.audit_final()
        self.finish(succeeded)

    def audit_final(self):
        path = self.work / 'evidence/runs/lean-TypedCNFInstance.Final/stage.log'
        raw = regular(path, 65536)
        pattern = rb"'"+re.escape(THEOREM.encode())+rb"' depends on axioms: \[([^\]\r\n]*)\]\r?\n?"
        match = re.fullmatch(pattern, raw)
        require(match is not None, 'missing or ambiguous exact final axiom output')
        names = [] if not match.group(1) else match.group(1).decode('ascii').split(', ')
        require(len(names) == len(set(names)) and set(names) <= ALLOWED_AXIOMS, 'nonstandard final axiom')
        final = self.work / 'lib/TypedCNFInstance/Final.olean'
        publish(self.work / 'evidence/final-axioms.json', {'schema': 'typed-cnf-strict-final-axioms-v1',
                'theorem': THEOREM, 'axioms': names, 'stdout_sha256': sha(path),
                'module_sha256': sha(final), 'receipt': self.previous}, 2048)

    def finish(self, succeeded):
        for path, expected in self.config['toolchain_manifests']:
            require(sha(path) == expected, 'toolchain manifest changed')
            for source, expected_hash, size in json.loads(regular(path, 65536)):
                if expected_hash.startswith('symlink:'):
                    require(Path(source).is_symlink() and os.readlink(source) == expected_hash[len('symlink:'):],
                            'toolchain/dependency link changed')
                else:
                    require(Path(source).stat().st_size == size and sha(source) == expected_hash, 'toolchain/dependency changed')
        check_sources({'repo': str(self.repo), 'source_manifests': self.config['source_manifests']})
        require(output_guard({'work': str(self.work), 'ledger_root': str(self.ledger.root),
                             'artifact_work_roots': self.ledger.work_roots(str(self.work))}) is None,
                'terminal output guard')
        actual = {str(path.relative_to(self.work / 'lib')) for path in (self.work / 'lib').rglob('*.olean')}
        require(actual == {name.replace('.', '/')+'.olean' for name in succeeded}, 'unbound project import')
        self.terminal = {'schema': 'typed-cnf-clean-closure-v1',
                'status': 'passed', 'module_count': len(succeeded), 'attempt_count': len(self.receipts),
                'allocation_attempt_count': len(self.ledger.records()),
                'allocation_sha256': self.ledger.identity,
                'ordered_receipts_sha256': hashlib.sha256(encoded(self.receipts)).hexdigest(),
                'spent_seconds': self.spent, 'remaining_seconds': TOTAL_SECONDS-self.spent,
                'final_axioms_sha256': sha(self.work / 'evidence/final-axioms.json'),
                'config_sha256': sha(self.work / 'evidence/config.json'),
                'build_plan_sha256': sha(self.work / 'evidence/build-plan.json')}

    def publish_terminal(self, cleanup):
        require(cleanup['remaining'] == 0 and cleanup['reaped'] == 0, 'final outer cleanup was not already settled')
        outer = {'schema': 'typed-cnf-final-outer-cleanup-v1', 'owner_identity': list(self.owner.root),
                 'remaining_descendants': 0, 'reaped_descendants': 0,
                 'invocation_cleanup': self.invocation_cleanup,
                 'allocation_sha256': self.ledger.identity}
        terminal = dict(self.terminal)
        terminal['outer_cleanup_sha256'] = hashlib.sha256(encoded(outer)).hexdigest()
        evidence = sum(bytes_in(Path(root) / 'evidence') for root in self.ledger.work_roots(str(self.work)))
        evidence += bytes_in(self.ledger.root)
        require(evidence + len(encoded(outer)) + len(encoded(terminal)) <= 32*1024*1024, 'final evidence cap')
        publish(self.work / 'evidence/outer-closure.json', outer, 2048)
        publish(self.work / 'evidence/terminal.json', terminal, 2048)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['generate', 'build', 'all'])
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--go', default='go')
    parser.add_argument('--lean', default='lean')
    parser.add_argument('--cc', default='cc')
    parser.add_argument('--cxx', default='c++')
    parser.add_argument('--modcache', type=Path, required=True)
    parser.add_argument('--ledger', type=Path, required=True)
    parser.add_argument('--config-sha256')
    parser.add_argument('--build-plan-sha256')
    args = parser.parse_args()
    subreaper()
    invocation_observation = ProcessObservation('portable.invocation')
    owner = OwnedProcesses(observer=invocation_observation)
    ledger = gate = None
    completed = False
    invocation_error = None
    acceptance_controls = None
    def cancelled(signum, frame):
        raise InterruptedError('runner signal '+str(signum))
    for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP, signal.SIGQUIT):
        signal.signal(sig, cancelled)
    try:
        ledger = Ledger(args.ledger)
        acceptance_controls = check_acceptance_controls()
        require(not ledger.root.is_relative_to(args.repo.resolve()), 'ledger must be outside repository')
        if args.mode == 'build':
            require(args.config_sha256 == sha(args.work / 'evidence/config.json') and
                    args.build_plan_sha256 == sha(args.work / 'evidence/build-plan.json'),
                    'build requires explicit reviewed configuration and plan hashes')
            config = json.loads(regular(args.work / 'evidence/config.json', 65536))
            require(config['repo'] == str(args.repo.resolve()) and config['work'] == str(args.work.resolve(strict=True)), 'resume identity')
            gate = Gate(config, ledger, owner)
            gate.recover_generated()
        else:
            gate = Gate(prepare(args, ledger, owner), ledger, owner)
            gate.generate()
        if args.mode in {'build', 'all'}:
            gate.build()
        completed = True
    except BaseException as caught:
        invocation_error = repr(caught)[:1024]
        raise
    finally:
        for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP, signal.SIGQUIT):
            signal.signal(sig, signal.SIG_IGN)
        try:
            cleanup = None
            cleanup_error = observation_error = observation_reference = None
            try:
                cleanup = owner.cleanup()
                if cleanup['remaining'] and ledger is not None:
                    ledger.poison(owner.root, 'final owned descendants remain')
            except BaseException as caught:
                cleanup_error = repr(caught)[:1024]
                if ledger is not None:
                    ledger.poison(owner.root, 'final owned cleanup exception: '+repr(caught)[:512])
                raise
            finally:
                # Generation, build, preflight and exception paths all retain
                # their actual final owned observations before acceptance.
                if ledger is not None:
                    prefix = 'portable-invocation-%d-%d' % owner.root
                    try:
                        observation_reference = invocation_observation.publish(ledger.root / (prefix+'-processes.json'))
                        check_observation(observation_reference, ledger.root)
                        require(owner.observation_error is None, 'invocation observation failed')
                    except BaseException as caught:
                        observation_error = repr(caught)[:512]
                    final_record = {'schema': 'typed-cnf-invocation-cleanup-v1',
                        'mode': args.mode, 'owner_identity': list(owner.root),
                        'completed_body': completed, 'error': invocation_error,
                        'cleanup_error': cleanup_error, 'observation_error': observation_error,
                        'remaining_descendants': cleanup['remaining'] if cleanup is not None else None,
                        'reaped_descendants': cleanup['reaped'] if cleanup is not None else None,
                        'process_observation': observation_reference,
                        'acceptance_controls': acceptance_controls,
                        'allocation_sha256': ledger.identity, 'runner_sha256': sha(ROOT / 'run.py'),
                        'config_sha256': sha(args.work / 'evidence/config.json')
                            if (args.work / 'evidence/config.json').exists() else None}
                    final_path = ledger.root / (prefix+'-cleanup.json')
                    publish(final_path, final_record, 14336)
                    if gate is not None:
                        gate.invocation_cleanup = [str(final_path), sha(final_path)]
                    require(observation_error is None, 'final invocation observation incomplete')
                    require(output_guard({'work': str(args.work), 'ledger_root': str(ledger.root),
                            'artifact_work_roots': ledger.work_roots(str(args.work))}) is None,
                            'final invocation aggregate output guard')
            if cleanup['remaining'] and ledger is not None:
                ledger.poison(owner.root, 'final owned descendants remain')
            require(cleanup['remaining'] == 0, 'runner cleanup incomplete')
            require(cleanup['reaped'] == 0, 'runner required an unexpected final reap')
            if completed and sys.exc_info()[0] is None and gate is not None and hasattr(gate, 'terminal'):
                gate.publish_terminal(cleanup)
        finally:
            if ledger is not None:
                ledger.close()


if __name__ == '__main__':
    main()
