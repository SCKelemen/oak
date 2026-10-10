"""Bounded native prover preparation and independent raw artifact validation."""
import hashlib
import json
import math
import os
from pathlib import Path
import re
import signal
import stat
import subprocess
import time
import threading

from native_arm64_shards import _file_bytes, _no_symlinks, _read_json, _schema

BUDGET_SECONDS = 90 * 60
HARNESS = 'root-harness'
NATIVE = 'native-prover'
STAGES = ('root-harness-build', 'root-harness-list', 'native-prover-build')
ENVIRONMENT = 'OAK_NATIVE_PREREQUISITE'


def digest(path):
    return hashlib.sha256(_file_bytes(path)).hexdigest()


def _hash(value, label):
    if not isinstance(value, str) or not re.fullmatch('[0-9a-f]{64}', value):
        raise ValueError(f'{label}: invalid SHA-256')
    return value


def _duration(value, label, *, positive=False):
    if (type(value) not in (int, float) or not math.isfinite(value)
            or value < 0 or (positive and value == 0) or value > BUDGET_SECONDS):
        raise ValueError(f'{label}: invalid prerequisite duration')
    return value


def commands(directory, names):
    import native_arm64 as runner
    directory = Path(directory)
    harness = str(directory / HARNESS)
    return {
        'root-harness-build': ['go', 'test', '-c', '-race', '-o', harness, '.'],
        'root-harness-list': [harness, '-test.list=' + runner.pattern(names)],
        'native-prover-build': [harness, 'native-prover-build', str(directory / NATIVE)],
    }


def root_command(directory, names):
    import native_arm64 as runner
    return ['go', 'tool', 'test2json', '-t', '-p', runner.MODULE, '--',
            str(Path(directory) / HARNESS), '-test.v=test2json', '-test.count=1',
            '-test.timeout=' + runner.TIMEOUTS['.'], '-test.run=' + runner.pattern(names)]


def _write_json(path, value):
    import json
    path.write_text(json.dumps(value, indent=2) + '\n')


def _bounded_command(command, log, deadline, env):
    """One shared deadline; kill the entire compiler/linker process group."""
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise ValueError('native prover prerequisite exhausted its 90-minute total budget')
    start = time.monotonic()
    timed_out = False
    with log.open('wb') as output:
        process = subprocess.Popen(command, stdout=output, stderr=subprocess.STDOUT,
                                   env=env, start_new_session=True)
        try:
            try:
                returncode = process.wait(timeout=remaining)
            except subprocess.TimeoutExpired:
                timed_out = True
        finally:
            # A successful/failed leader must not leave a compiler or solver
            # descendant able to publish evidence after this stage returns.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            final_returncode = process.wait(timeout=5)
        if timed_out:
            returncode = final_returncode
    status = {'schema_version': 1, 'command': command, 'returncode': returncode,
              'timeout_seconds': remaining, 'elapsed_seconds': time.monotonic() - start,
              'timed_out': timed_out}
    _write_json(log.with_name(log.stem + '-status.json'), status)
    if timed_out or returncode != 0:
        raise ValueError(f'native prover prerequisite failed: {log.stem}; '
                         f'exit={returncode}, timed_out={timed_out}; see {log}')
    return status


class RuntimeDeadline:
    """Bound test2json and every descendant even when a pipe stays open."""
    def __init__(self, process, timeout_seconds):
        self.process = process
        self.timeout_seconds = timeout_seconds
        self.timed_out = threading.Event()
        self.elapsed_seconds = None

    def _kill_group(self):
        try:
            os.killpg(self.process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass

    def _expire(self):
        self.timed_out.set()
        self._kill_group()

    def __enter__(self):
        self.started = time.monotonic()
        self.timer = threading.Timer(self.timeout_seconds, self._expire)
        self.timer.daemon = True
        self.timer.start()
        return self

    def __exit__(self, kind, error, trace):
        self.timer.cancel()
        self.timer.join()
        # The leader may have exited successfully while descendants retained
        # its pipes or survived a Go timeout. Always reap the entire group.
        self._kill_group()
        self.process.wait(timeout=5)
        self.elapsed_seconds = time.monotonic() - self.started
        return False

    def evidence(self):
        return {'timeout_seconds': self.timeout_seconds,
                'elapsed_seconds': self.elapsed_seconds,
                'timed_out': self.timed_out.is_set()}


def check_untracked_inputs(repo, directory, timeout):
    raw = subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard', '-z'],
                                  cwd=repo, timeout=timeout)
    if not isinstance(raw, bytes) or (raw and not raw.endswith(b'\0')):
        raise ValueError('invalid untracked source inventory')
    for entry in raw.split(b'\0'):
        if not entry:
            continue
        path = Path(os.fsdecode(entry))
        if path.is_absolute() or '..' in path.parts:
            raise ValueError('invalid untracked source path')
        if not (repo / path).absolute().is_relative_to(directory.absolute()):
            raise ValueError(f'untracked input cannot enter the race harness: {path}')


def prepare(repo, directory, names, context):
    """Produce a race harness once, then prove and link with those exact bytes."""
    directory = _no_symlinks(directory)
    start = time.monotonic()
    deadline = start + BUDGET_SECONDS
    check_untracked_inputs(repo, directory, deadline - time.monotonic())
    env = dict(os.environ, GOFLAGS='')
    env.pop(ENVIRONMENT, None)
    invocation = commands(directory, names)
    harness_sha = None
    for stage in STAGES:
        print(f'PREPARE {stage}: shared 90-minute prerequisite deadline', flush=True)
        _bounded_command(invocation[stage], directory / (stage + '.log'), deadline, env)
        if stage == 'root-harness-build':
            harness_sha = digest(directory / HARNESS)
        elif digest(directory / HARNESS) != harness_sha:
            raise ValueError('race harness changed during native prover preparation')
        if stage == 'root-harness-list':
            live = [line for line in (directory / (stage + '.log')).read_text().splitlines()
                    if line.startswith('Test')]
            if sorted(live) != sorted(names):
                raise ValueError('race harness inventory does not match the reviewed root selector')
    # Revalidate full evidence before allowing a success receipt or any runtime.
    validate_manifest(repo, directory, context, harness_sha, str(directory))
    elapsed = time.monotonic() - start
    _duration(elapsed, 'prerequisite elapsed')
    receipt = {'schema_version': 1, 'success': True, 'context': context,
               'directory': str(directory), 'budget_seconds': BUDGET_SECONDS,
               'elapsed_seconds': elapsed, 'harness_sha256': harness_sha,
               'success_sha256': digest(directory / NATIVE / 'success.json')}
    _write_json(directory / 'prerequisite-status.json', receipt)
    return receipt


def required_files():
    files = {HARNESS, 'prerequisite-status.json'}
    for stage in STAGES:
        files.update((stage + '.log', stage + '-status.json'))
    return files | {NATIVE + '/' + name for name in native_files()}


def _exact_files(directory, required, optional=()):
    """Reject symlinks, special files, missing/extra files and empty directories."""
    required, optional = set(required), set(optional)
    allowed_dirs = {str(parent) for name in required | optional
                    for parent in Path(name).parents if str(parent) != '.'}
    found, directories = set(), set()
    def visit(root):
        for path in root.iterdir():
            _no_symlinks(path)
            name = path.relative_to(directory).as_posix()
            mode = path.stat().st_mode
            if stat.S_ISDIR(mode):
                if name not in allowed_dirs:
                    raise ValueError(f'unexpected evidence directory: {name}')
                directories.add(name)
                visit(path)
            elif stat.S_ISREG(mode):
                found.add(name)
            else:
                raise ValueError(f'unexpected evidence file type: {name}')
    visit(directory)
    if not required <= found or found - required - optional or directories != allowed_dirs:
        raise ValueError(f'incorrect evidence files: missing={sorted(required - found)}, '
                         f'extra={sorted(found - required - optional)}')


def validate(repo, directory, names, context):
    receipt = _read_json(directory / 'prerequisite-status.json')
    _schema(receipt, ('schema_version', 'success', 'context', 'directory', 'budget_seconds',
                      'elapsed_seconds', 'harness_sha256', 'success_sha256'), 'prerequisite receipt')
    original = receipt['directory']
    if (not isinstance(original, str) or not Path(original).is_absolute()
            or str(Path(original)) != original or '..' in Path(original).parts):
        raise ValueError('invalid original prerequisite directory')
    if (receipt['success'] is not True or receipt['context'] != context
            or type(receipt['budget_seconds']) is not int
            or receipt['budget_seconds'] != BUDGET_SECONDS):
        raise ValueError('native prover prerequisite identity, budget or success mismatch')
    total = _duration(receipt['elapsed_seconds'], 'prerequisite elapsed')
    elapsed = 0
    expected = commands(original, names)
    for stage in STAGES:
        status = _read_json(directory / (stage + '-status.json'))
        _schema(status, ('schema_version', 'command', 'returncode', 'timeout_seconds',
                         'elapsed_seconds', 'timed_out'), stage)
        timeout = _duration(status['timeout_seconds'], stage + ' timeout', positive=True)
        duration = _duration(status['elapsed_seconds'], stage + ' elapsed')
        if (type(status['returncode']) is not int or status['returncode'] != 0
                or status['timed_out'] is not False or status['command'] != expected[stage]
                or timeout > BUDGET_SECONDS - elapsed or duration > timeout):
            raise ValueError(f'{stage}: unsuccessful, over-budget or unexpected command')
        elapsed += duration
        _file_bytes(directory / (stage + '.log'))
    if elapsed > total:
        raise ValueError('prerequisite stage times exceed recorded total')
    live = [line for line in _file_bytes(directory / 'root-harness-list.log').decode().splitlines()
            if line.startswith('Test')]
    if sorted(live) != sorted(names):
        raise ValueError('persisted race harness inventory mismatch')
    harness_sha = digest(directory / HARNESS)
    if receipt['harness_sha256'] != harness_sha:
        raise ValueError('persisted race harness digest mismatch')
    if receipt['success_sha256'] != digest(directory / NATIVE / 'success.json'):
        raise ValueError('native prover success receipt digest mismatch')
    validate_manifest(repo, directory, context, harness_sha, original)
    return receipt

SOURCE_NAMES = ('bdd.oak', 'lower.oak', 'syntax.oak', 'tree.oak', 'protocol.oak',
                'shell.oak', 'lean.oak', 'explore.oak', 'witness.oak', 'driver.oak',
                'lrat.oak', 'sat.oak', 'model.oak', 'cnf.oak', 'certify.oak',
                'main.oak', 'oak.mod')


def native_files():
    return {'recipe.json', 'report.json', 'success.json', 'program.c', 'asm.o', 'solver'} | {
        'source/' + name for name in SOURCE_NAMES}


def source_bytes(repo):
    source = {name: _file_bytes(repo / 'prove/solver' / name) for name in SOURCE_NAMES[:15]}
    oaksolver = _file_bytes(repo / 'oaksolver.go')
    matches = re.findall(rb'const oakSolverDriverSource = `([^`]*)`', oaksolver)
    if len(matches) != 1:
        raise ValueError('cannot establish the exact current Oak solver driver')
    source['main.oak'] = matches[0]
    source['oak.mod'] = b'module oak.prove.solver\noak 0.1.0\n'
    return source


def _fields(value, fields, label):
    if not isinstance(value, dict) or set(value) != set(fields):
        raise ValueError(f'{label}: incorrect manifest fields')


def _inventory(value):
    _fields(value, ('eligible', 'externs'), 'native frontend inventory')
    seen = set()
    for kind, count in (('eligible', 1087), ('externs', 15)):
        rows = value[kind]
        if not isinstance(rows, list) or len(rows) != count:
            raise ValueError(f'expected exactly {count} reviewed native {kind}')
        for row in rows:
            _fields(row, ('name', 'source_sha256', 'extern_symbol'), 'native input')
            name = row['name']
            if not isinstance(name, str) or not name or name in seen:
                raise ValueError('duplicate, missing or malformed native input')
            seen.add(name)
            _hash(row['source_sha256'], 'native input')
            if (not isinstance(row['extern_symbol'], str)
                    or bool(row['extern_symbol']) != (kind == 'externs')):
                raise ValueError('extern classification mismatch')
    return value


def _candidate(value):
    _fields(value, ('name', 'body_sha256', 'recipe_sha256', 'outcome', 'message', 'cached'),
            'native candidate')
    if (not isinstance(value['name'], str) or not value['name']
            or value['outcome'] not in ('refused', 'mismatch', 'trusted', 'witnessed', 'proven')
            or not isinstance(value['message'], str) or value['cached'] is not False):
        raise ValueError('malformed native candidate verdict')
    _hash(value['body_sha256'], 'candidate body')
    _hash(value['recipe_sha256'], 'candidate recipe')


def _report(value, inventory):
    _schema(value, ('schema_version', 'inventory', 'functions'), 'native report')
    if value['inventory'] != inventory:
        raise ValueError('native report changed the independently reviewed frontend inventory')
    functions = value['functions']
    if not isinstance(functions, list) or len(functions) != len(inventory['eligible']):
        raise ValueError('native report omits or duplicates a function')
    native = 0
    declarations = {row['name'] for kind in ('eligible', 'externs') for row in inventory[kind]}
    for row, expected in zip(functions, inventory['eligible']):
        _fields(row, ('input', 'status', 'reason', 'callees', 'considered', 'materialized',
                      'selected', 'validations'), 'native function')
        if row['input'] != expected:
            raise ValueError('native report input identity/order mismatch')
        if row['status'] not in ('proven', 'witnessed', 'trusted', 'c-fallback'):
            raise ValueError('unfinished or erroneous native function')
        if (not isinstance(row['reason'], str) or not row['reason'] or not isinstance(row['callees'], list)
                or any(not isinstance(name, str) or not name for name in row['callees'])
                or any(type(row[key]) is not int or row[key] < 0
                       for key in ('considered', 'materialized'))
                or not isinstance(row['validations'], list)
                or row['materialized'] > row['considered']):
            raise ValueError('malformed native function report')
        if (len(row['callees']) != len(set(row['callees']))
                or not set(row['callees']) <= declarations):
            raise ValueError('unknown or duplicate native callee dependency')
        seen_validations = set()
        for candidate in row['validations']:
            _candidate(candidate)
            key = json.dumps(candidate, sort_keys=True)
            if key in seen_validations:
                raise ValueError('duplicate native validation record')
            seen_validations.add(key)
        if row['selected'] is not None:
            _candidate(row['selected'])
            if row['selected']['outcome'] not in ('proven', 'witnessed', 'trusted'):
                raise ValueError('refused or mismatched final native candidate')
            if row['selected'] not in row['validations']:
                raise ValueError('selected candidate has no actual validation record')
        if row['status'] == 'c-fallback':
            if not row['reason'] or (row['selected'] and row['selected']['outcome'] == 'refused'):
                raise ValueError('C fallback requires its actual reason')
        else:
            native += 1
            if row['selected'] is None or row['selected']['outcome'] != row['status']:
                raise ValueError('native terminal status differs from the selected verdict')
    if native == 0:
        raise ValueError('C-only substitution cannot satisfy the native prerequisite')


def _elf(path, types):
    raw = _file_bytes(path)
    if (len(raw) < 64 or raw[:6] != b'\x7fELF\x02\x01'
            or int.from_bytes(raw[16:18], 'little') not in types
            or int.from_bytes(raw[18:20], 'little') != 183):
        raise ValueError(f'expected a native Linux ARM64 ELF artifact: {path.name}')


def _file_map(value, label):
    if not isinstance(value, dict) or not value:
        raise ValueError(f'{label}: missing toolchain/runtime identities')
    for path, sha in value.items():
        if (not isinstance(path, str) or not Path(path).is_absolute()
                or str(Path(path)) != path or '..' in Path(path).parts):
            raise ValueError(f'{label}: invalid resolved absolute file path')
        _hash(sha, label)


def validate_manifest(repo, directory, context, harness_sha, original_directory):
    native = directory / NATIVE
    _exact_files(native, native_files())
    recipe = _read_json(native / 'recipe.json')
    _schema(recipe, ('schema_version', 'recipe_version', 'context', 'harness_sha256', 'go_build', 'sources', 'support_sources',
                     'inventory', 'platform', 'target', 'asm_mode', 'object_format', 'cpu',
                     'c_opt_level', 'cc', 'toolchain_files', 'link_inputs'), 'native recipe')
    expected_context = {key: value for key, value in context.items() if key != 'schema_version'}
    if recipe['context'] != expected_context or recipe['harness_sha256'] != harness_sha:
        raise ValueError('native recipe belongs to another source/run/attempt/harness')
    expected_support = {name: digest(repo / name) for name in ('stdlib/std.oak', 'stdlib/host.oak')}
    if recipe['support_sources'] != expected_support:
        raise ValueError('native core/host support source bytes differ from checkout')
    expected_sources = source_bytes(repo)
    expected_hashes = {name: hashlib.sha256(raw).hexdigest() for name, raw in expected_sources.items()}
    if recipe['sources'] != expected_hashes:
        raise ValueError('native recipe sources differ from the exact current solver inputs')
    for name, raw in expected_sources.items():
        if _file_bytes(native / 'source' / name) != raw:
            raise ValueError(f'native source bytes differ: {name}')
    inventory = _inventory(_read_json(repo / '.github/scripts/native_prover_inventory.json'))
    if recipe['inventory'] != inventory:
        raise ValueError('native recipe changed the reviewed frontend inventory')
    direct_externs = []
    for raw in expected_sources.values():
        direct_externs.extend((name.decode(), symbol.decode()) for name, symbol in re.findall(
            rb'(?m)^\s*([A-Za-z_][A-Za-z0-9_]*):[^\n]*=\s*c\.extern\("([^"\n]+)"\)\s*$', raw))
    expected_externs = set(direct_externs) | {('host__oak_uhost_uwrite', 'oak_host_write_call')}
    if (len(direct_externs) != 14 or len(set(direct_externs)) != 14
            or {(row['name'], row['extern_symbol']) for row in inventory['externs']} != expected_externs):
        raise ValueError('solver extern inventory must preserve all 14 source externs and the host write shim')
    if (recipe['recipe_version'] != 'hybrid-native-c-v1/fresh-verdicts/default-search/race'
            or recipe['platform'] != 'linux/arm64' or recipe['target'] != 'linux/arm64'
            or recipe['asm_mode'] != 'native' or recipe['object_format'] != 'ELF'
            or recipe['cpu'] != '' or type(recipe['c_opt_level']) is not int
            or recipe['c_opt_level'] != 1):
        raise ValueError('native compilation recipe changed')
    if recipe['link_inputs'] != []:
        raise ValueError('native prover acquired unexpected manifest link inputs')
    _validate_toolchain(recipe, repo)
    report = _read_json(native / 'report.json')
    _report(report, inventory)
    success = _read_json(native / 'success.json')
    _schema(success, ('schema_version', 'recipe_sha256', 'report_sha256', 'program_sha256',
                      'object_sha256', 'solver_sha256', 'link_command', 'runtime_files'), 'native success')
    _validate_link(success, recipe, original_directory)
    for field, filename in (('recipe_sha256', 'recipe.json'), ('report_sha256', 'report.json'),
                            ('program_sha256', 'program.c'), ('object_sha256', 'asm.o'),
                            ('solver_sha256', 'solver')):
        if success[field] != digest(native / filename):
            raise ValueError(f'native output digest mismatch: {filename}')
    if not _file_bytes(native / 'program.c'):
        raise ValueError('empty generated native program')
    _elf(native / 'asm.o', {1})
    _elf(native / 'solver', {2, 3})
    _elf(directory / HARNESS, {2, 3})

CC_ARGS = ['-std=c99', '-ffp-contract=off', '-Wno-parentheses-equality', '-O1']


def _validate_toolchain(recipe, repo):
    cc = recipe['cc']
    _fields(cc, ('path', 'sha256', 'version', 'args'), 'native C compiler')
    _file_map(recipe['toolchain_files'], 'native toolchain')
    if (not isinstance(cc['path'], str) or recipe['toolchain_files'].get(cc['path']) != cc['sha256']
            or not isinstance(cc['version'], str) or 'Free Software Foundation' not in cc['version']
            or cc['args'] != CC_ARGS):
        raise ValueError('native C compiler identity or arguments mismatch')
    _hash(cc['sha256'], 'native C compiler')
    build = recipe['go_build']
    _fields(build, ('version', 'main', 'dependencies', 'settings'), 'native Go compiler')
    if (build['version'] != 'go1.27.1'
            or build['main'] != {'Path': 'github.com/SCKelemen/oak', 'Version': '(devel)'}):
        raise ValueError('native Go compiler version or module mismatch')
    settings = build['settings']
    if not isinstance(settings, dict) or any(not isinstance(k, str) or not isinstance(v, str)
                                             for k, v in settings.items()):
        raise ValueError('invalid Go compiler settings')
    required = {'-race': 'true', '-compiler': 'gc', '-buildmode': 'exe',
                'CGO_ENABLED': '1', 'GOOS': 'linux', 'GOARCH': 'arm64'}
    if any(settings.get(key) != value for key, value in required.items()):
        raise ValueError('native harness was not built with the required race/native settings')
    if any(settings.get(key) for key in ('-tags', '-gcflags', '-ldflags', '-cover', '-overlay',
                                         '-modfile', 'GOEXPERIMENT')):
        raise ValueError('unreviewed Go compiler settings')
    if (settings.get('vcs.revision', recipe['context']['source_sha']) != recipe['context']['source_sha']
            or settings.get('vcs.modified', 'false') != 'false'):
        raise ValueError('native Go compiler source identity mismatch')
    expected = []
    for line in _file_bytes(repo / 'go.sum').decode().splitlines():
        name, version, checksum = line.split()
        if not version.endswith('/go.mod'):
            expected.append({'Path': name, 'Version': version, 'Sum': checksum})
    if build['dependencies'] != expected:
        raise ValueError('native Go compiler dependency identity mismatch')


def _validate_link(success, recipe, original_directory):
    _file_map(success['runtime_files'], 'solver runtime')
    if any(recipe['toolchain_files'].get(path) != sha for path, sha in success['runtime_files'].items()):
        raise ValueError('solver runtime dependency absent from the native toolchain recipe')
    command = success['link_command']
    prefix = [recipe['cc']['path'], *CC_ARGS, '-o', str(Path(original_directory) / NATIVE / 'solver')]
    if (not isinstance(command, list) or len(command) != len(prefix) + 3
            or command[:len(prefix)] != prefix or command[-1] != '-lm'):
        raise ValueError('native prover did not use the actual reviewed compile/link command')
    c_path, object_path = command[-3:-1]
    if (not isinstance(c_path, str) or not isinstance(object_path, str)
            or not Path(c_path).is_absolute() or '..' in Path(c_path).parts
            or Path(c_path).name != 'program.c' or Path(object_path).name != 'asm.o'
            or Path(c_path).parent != Path(object_path).parent
            or not re.fullmatch(r'oak-build-[A-Za-z0-9_-]+', Path(c_path).parent.name)):
        raise ValueError('unexpected actual C/object link inputs')
