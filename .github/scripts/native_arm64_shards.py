#!/usr/bin/env python3
"""Reviewed native ARM64 partitions and fail-closed cross-shard evidence checks.

Only raw Go events and exact invocation/checkout identities establish coverage.
The optional *-passed.json summaries are deliberately never read as evidence.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess


SHARDS = ('compiler-a', 'compiler-b', 'compiler-c', 'support')


def _no_symlinks(path):
    path = Path(path).absolute()
    for component in (path, *path.parents):
        if component.is_symlink():
            raise ValueError(f'symlink evidence is forbidden: {component}')
    return path


def _file_bytes(path):
    path = _no_symlinks(path)
    if not stat.S_ISREG(path.stat().st_mode):
        raise ValueError(f'expected a regular evidence file: {path}')
    return path.read_bytes()


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'duplicate JSON object key: {key}')
        result[key] = value
    return result


def _invalid_constant(value):
    raise ValueError(f'non-JSON numeric constant: {value}')


def _json(text, label):
    try:
        return json.loads(text, object_pairs_hook=_unique_object,
                          parse_constant=_invalid_constant)
    except (ValueError, UnicodeError) as error:
        raise ValueError(f'{label}: invalid JSON: {error}') from error


def _read_json(path):
    return _json(_file_bytes(path), path)


def _schema(value, keys, label):
    if not isinstance(value, dict) or set(value) != set(keys):
        raise ValueError(f'{label}: incorrect evidence fields')
    if type(value['schema_version']) is not int or value['schema_version'] != 1:
        raise ValueError(f'{label}: unsupported schema_version')


def load_shards(selected, manifest, plan_path):
    """Check a reviewed, explicit root partition; children inherit root ownership."""
    plan = _read_json(plan_path)
    if not isinstance(plan, dict) or not isinstance(plan.get('shards'), dict):
        raise ValueError('native ARM64 shard plan must contain a shards object')
    if type(plan.get('schema_version')) is not int or plan['schema_version'] != 1:
        raise ValueError('native ARM64 shard plan requires schema_version 1')
    shards = plan['shards']
    if set(shards) != set(SHARDS):
        raise ValueError(f'expected exactly the reviewed shards: {SHARDS}')
    if not isinstance(selected, dict) or './compiler' not in selected or len(selected) < 2:
        raise ValueError('invalid selected package inventory')
    expected = set()
    for package, names in selected.items():
        if (not isinstance(package, str) or not isinstance(names, list) or not names
                or any(not isinstance(name, str) or not name or '/' in name for name in names)
                or len(names) != len(set(names))):
            raise ValueError(f'invalid selected root inventory: {package}')
        expected.update((package, name) for name in names)

    seen = set()
    result = {}
    for shard in SHARDS:
        packages = shards[shard]
        owners = set(selected) - {'./compiler'} if shard == 'support' else {'./compiler'}
        if not isinstance(packages, dict) or set(packages) != owners:
            raise ValueError(f'{shard}: incorrect compiler/support package ownership')
        result[shard] = {}
        for package, names in packages.items():
            if (not isinstance(names, list) or not names
                    or any(not isinstance(name, str) or not name or '/' in name for name in names)):
                raise ValueError(f'{shard}: empty or invalid root list: {package}')
            for name in names:
                key = package, name
                if key not in expected:
                    raise ValueError(f'{shard}: unknown or excluded root: {package} {name}')
                if key in seen:
                    raise ValueError(f'{shard}: duplicate root ownership: {package} {name}')
                seen.add(key)
            result[shard][package] = sorted(names)
    if seen != expected:
        raise ValueError(f'shard plan omits selected roots: {sorted(expected - seen)}')

    children = manifest.get('children')
    if not isinstance(children, dict):
        raise ValueError('missing required child inventory')
    for package, roots in children.items():
        if package not in selected or not isinstance(roots, dict):
            raise ValueError(f'invalid child package inventory: {package}')
        for root, names in roots.items():
            if ((package, root) not in expected or not isinstance(names, list) or not names
                    or any(not isinstance(name, str) or not name for name in names)
                    or len(names) != len(set(names))):
                raise ValueError(f'invalid required child inventory: {package} {root}')
    return result


def source_contents_digest(repo):
    raw = subprocess.check_output(['git', 'ls-files', '-z'], cwd=repo)
    if not isinstance(raw, bytes) or not raw.endswith(b'\0'):
        raise ValueError('missing tracked source inventory')
    paths = raw[:-1].split(b'\0')
    if not paths or len(paths) != len(set(paths)):
        raise ValueError('empty or duplicate tracked source inventory')
    hasher = hashlib.sha256()
    for raw_path in paths:
        path = Path(os.fsdecode(raw_path))
        if path.is_absolute() or '..' in path.parts:
            raise ValueError('invalid tracked source path')
        sha = hashlib.sha256(_file_bytes(repo / path)).hexdigest()
        hasher.update(str(len(raw_path)).encode() + b':' + raw_path + b':' + sha.encode() + b'\n')
    return hasher.hexdigest()


def identity(repo, manifest_path, plan_path, shard, env=None):
    """Bind evidence to this exact source, reviewed inventory, plan, and CI attempt."""
    if shard not in SHARDS:
        raise ValueError(f'unknown native ARM64 shard: {shard}')
    env = os.environ if env is None else env
    for name in ('GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT'):
        if not isinstance(env.get(name), str) or not re.fullmatch(r'[1-9][0-9]*', env[name]):
            raise ValueError(f'missing or malformed {name}')
    source_sha = subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
    if (not re.fullmatch(r'(?:[0-9a-f]{40}|[0-9a-f]{64})', source_sha)
            or env.get('GITHUB_SHA') != source_sha):
        raise ValueError('checkout HEAD must equal GITHUB_SHA')
    source_tree = subprocess.check_output(
        ['git', 'rev-parse', 'HEAD^{tree}'], cwd=repo, text=True).strip()
    if not re.fullmatch(r'(?:[0-9a-f]{40}|[0-9a-f]{64})', source_tree):
        raise ValueError('invalid checkout source tree')
    return {
        'schema_version': 1,
        'shard': shard,
        'source_sha': source_sha,
        'source_tree': source_tree,
        'source_contents_sha256': source_contents_digest(repo),
        'inventory_sha256': hashlib.sha256(_file_bytes(manifest_path)).hexdigest(),
        'plan_sha256': hashlib.sha256(_file_bytes(plan_path)).hexdigest(),
        'run_id': env['GITHUB_RUN_ID'],
        'run_attempt': env['GITHUB_RUN_ATTEMPT'],
    }


def _events(path):
    raw = _file_bytes(path)
    # Go's JSON encoder terminates every event. Refuse an incomplete last line,
    # even when truncation happens immediately after a closing JSON brace.
    if not raw or not raw.endswith(b'\n'):
        raise ValueError(f'{path}: empty or truncated Go JSON stream')
    actions = {'start', 'run', 'pause', 'cont', 'pass', 'bench', 'fail', 'output', 'skip'}
    for number, line in enumerate(raw.splitlines(), 1):
        event = _json(line, f'{path}:{number}')
        if (not isinstance(event, dict) or not isinstance(event.get('Action'), str)
                or event['Action'] not in actions
                or not isinstance(event.get('Package'), str)
                or ('Test' in event and (not isinstance(event['Test'], str) or not event['Test']))
                or ('Output' in event and not isinstance(event['Output'], str))):
            raise ValueError(f'{path}:{number}: malformed Go test event')
        yield event


def _artifact_files(directory, packages):
    required = {'identity.json', 'source-inventory.json', 'lane-result.json'}
    optional = set()
    for package in packages:
        label = 'root' if package == '.' else package[2:].replace('/', '-')
        required.update((label + '.jsonl', label + '-status.json'))
        optional.add(label + '-passed.json')
    import native_arm64_prerequisite as prerequisite
    if '.' in packages:
        required.update(prerequisite.required_files())
    prerequisite._exact_files(directory, required, optional)


def aggregate(repo, directory, manifest_path, plan_path, matrix_result, env=None):
    """Revalidate every lane's raw evidence; absence or cancellation never passes."""
    # Lazy import keeps the execution runner free to import the shard helpers.
    import native_arm64 as runner
    import native_arm64_prerequisite as prerequisite

    if matrix_result != 'success':
        raise ValueError(f'every native ARM64 matrix child must succeed; result={matrix_result!r}')
    manifest = _read_json(manifest_path)
    selected = runner.select_tests(manifest)
    shards = load_shards(selected, manifest, plan_path)
    context = identity(repo, manifest_path, plan_path, SHARDS[0], env)
    prefix = f'native-arm64-{context["run_id"]}-{context["run_attempt"]}-'
    expected_directories = {prefix + shard for shard in SHARDS}
    directory = _no_symlinks(directory)
    if not directory.is_dir():
        raise ValueError(f'missing native ARM64 artifacts directory: {directory}')
    found = set()
    for path in directory.iterdir():
        _no_symlinks(path)
        if not path.is_dir():
            raise ValueError(f'unexpected non-directory among shard artifacts: {path}')
        found.add(path.name)
    if found != expected_directories:
        raise ValueError(f'incorrect native ARM64 artifact set; '
                         f'missing={sorted(expected_directories - found)}, '
                         f'extra={sorted(found - expected_directories)}')

    root_count = child_count = 0
    for shard, packages in shards.items():
        artifact = directory / (prefix + shard)
        _artifact_files(artifact, packages)
        recorded = _read_json(artifact / 'identity.json')
        _schema(recorded, context, f'{shard} identity')
        expected_identity = dict(context, shard=shard)
        if recorded != expected_identity:
            raise ValueError(f'{shard}: source/inventory/plan/run/shard identity mismatch')
        source = _read_json(artifact / 'source-inventory.json')
        try:
            artifact_selected = runner.check_inventory(manifest, source)
        except (KeyError, TypeError, AttributeError) as error:
            raise ValueError(f'{shard}: malformed source inventory') from error
        if artifact_selected != selected:
            raise ValueError(f'{shard}: source inventory selection mismatch')

        receipt = _read_json(artifact / 'lane-result.json')
        _schema(receipt, ('schema_version', 'shard', 'success', 'packages'), f'{shard} receipt')
        if (receipt['shard'] != shard or receipt['success'] is not True
                or receipt['packages'] != sorted(packages)):
            raise ValueError(f'{shard}: unsuccessful or mismatched lane receipt')

        prepared = None
        if shard == 'support':
            prepared = prerequisite.validate(repo, artifact, packages['.'], expected_identity)
        for package, names in packages.items():
            label = 'root' if package == '.' else package[2:].replace('/', '-')
            status = _read_json(artifact / (label + '-status.json'))
            fields = ['schema_version', 'returncode', 'command']
            if package == '.':
                fields += ['harness_sha256', 'success_sha256', 'environment',
                           'timeout_seconds', 'elapsed_seconds', 'timed_out']
                command = prerequisite.root_command(prepared['directory'], names)
            else:
                command = ['go', 'test', '-json', '-race', '-count=1', '-timeout', runner.TIMEOUTS[package],
                           '-p', '1', package, '-run', runner.pattern(names)]
            _schema(status, fields, f'{shard} {package} status')
            if package == '.' and (
                    status['harness_sha256'] != prepared['harness_sha256']
                    or status['success_sha256'] != prepared['success_sha256']
                    or status['environment'] != {prerequisite.ENVIRONMENT: str(Path(prepared['directory']) / prerequisite.NATIVE)}):
                raise ValueError('root runtime did not use the verified native prover and race harness')
            if package == '.':
                runtime_seconds = int(runner.TIMEOUTS[package][:-1]) * 60
                elapsed = prerequisite._duration(status['elapsed_seconds'], 'root runtime elapsed')
                if (type(status['timeout_seconds']) is not int or status['timeout_seconds'] != runtime_seconds
                        or status['timed_out'] is not False or elapsed > runtime_seconds):
                    raise ValueError('root runtime exceeded or changed its 45-minute wall deadline')
            if type(status['returncode']) is not int or status['returncode'] != 0:
                raise ValueError(f'{shard} {package}: missing successful Go exit status')
            if status['command'] != command:
                raise ValueError(f'{shard} {package}: unexpected Go command/selector')
            children = {root: children for root, children in manifest['children'].get(package, {}).items()
                        if root in names}
            passed = runner.validate_events(_events(artifact / (label + '.jsonl')), package, names, children)
            root_count += len(names)
            child_count += len(passed) - len(names)
        print(f'PASS {shard}: exact identity, source inventory, command, roots and children', flush=True)
    summary = {'shards': list(SHARDS), 'roots': root_count, 'children': child_count}
    print(f'PASS native ARM64 aggregate: {len(SHARDS)} shards, {root_count} roots, '
          f'{child_count} children; zero skips', flush=True)
    return summary


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--aggregate', action='store_true', required=True,
                        help='require successful, complete native ARM64 shard evidence')
    parser.add_argument('--results-dir', type=Path, required=True,
                        help='download directory containing all four named artifacts')
    parser.add_argument('--matrix-result', required=True,
                        help='the exact needs.native-shards.result value')
    args = parser.parse_args(argv)
    repo = Path(__file__).resolve().parents[2]
    scripts = repo / '.github/scripts'
    return aggregate(repo, args.results_dir, scripts / 'native_arm64_inventory.json',
                     scripts / 'native_arm64_shards.json', args.matrix_result)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, subprocess.CalledProcessError, OSError) as error:
        raise SystemExit(str(error))
