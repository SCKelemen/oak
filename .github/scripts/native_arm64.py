#!/usr/bin/env python3
"""Run the reviewed host-only ARM64 inventory; a skipped test is not a pass."""
import argparse
import collections
from contextlib import nullcontext
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import tempfile

from native_arm64_resources import ResourceTelemetry
from native_arm64_shards import identity, load_shards
import native_arm64_prerequisite as prerequisite

REPO = Path(__file__).resolve().parents[2]
MANIFEST = REPO / '.github/scripts/native_arm64_inventory.json'
PLAN = REPO / '.github/scripts/native_arm64_shards.json'
MODULE = 'github.com/SCKelemen/oak'
# These are scope exclusions, never allowed skips in the Linux run. Both remain
# separate, explicitly uncovered platform obligations; Ubuntu ARM is not proof.
EXCLUSIONS = {
    ('./compiler', 'TestE2EExampleSMEPackage'):
        'requires macOS SME detection and SME-capable hardware (e2e_sme_test.go)',
    ('./compiler', 'TestE2EMessageSendFoundation'):
        'requires Darwin/ARM64 Objective-C Foundation (e2e_ffi_objc_test.go)',
}
# Preserve every per-package limit. The reviewed compiler partition avoids a
# cumulative deadline without duplicating any test or widening its selector.
TIMEOUTS = {'./semir': '5m', './compiler': '90m', '.': '45m', './asm': '45m', './testrunner': '45m'}


def normalize(discovered):
    roots, sites = {}, {}
    for item in discovered['roots']:
        key = item['package'], item['test']
        if key[1] in roots.setdefault(key[0], {}):
            raise ValueError(f'duplicate source root: {key}')
        roots[key[0]][key[1]] = item['file']
    for item in discovered['skips']:
        sites.setdefault(item['file'] + '::' + item['function'], []).append(item['call'])
    return {'roots': roots, 'skip_sites': sites}


def check_inventory(manifest, discovered):
    actual = normalize(discovered)
    for field in ('roots', 'skip_sites'):
        if manifest[field] != actual[field]:
            raise ValueError(f'{field} changed: review the new/removed host guard or skip site '
                             'and update native_arm64_inventory.json; no automatic waiver')
    return select_tests(manifest)


def select_tests(manifest):
    selected = {package: sorted(names) for package, names in manifest['roots'].items()}
    if not selected or not any(selected.values()):
        raise ValueError('empty native ARM64 test inventory')
    for (package, name), reason in EXCLUSIONS.items():
        if name not in selected.get(package, []):
            raise ValueError(f'stale platform exclusion: {package} {name}')
        selected[package].remove(name)
        print(f'SEPARATE PLATFORM: {package} {name}: {reason}', flush=True)
    if set(selected) != set(TIMEOUTS):
        raise ValueError('package inventory changed; assign an explicit per-package timeout')
    for package, roots in manifest['children'].items():
        for root, children in roots.items():
            if root not in selected.get(package, []) or not children or len(children) != len(set(children)):
                raise ValueError(f'invalid required child inventory: {package} {root}')
    return selected


def preflight():
    if platform.system() != 'Linux' or platform.machine() not in ('aarch64', 'arm64'):
        raise ValueError('this execution lane requires a native Linux ARM64 host')
    env = json.loads(subprocess.check_output(
        ['go', 'env', '-json', 'GOHOSTARCH', 'GOARCH', 'GOHOSTOS', 'GOOS', 'CGO_ENABLED'], text=True))
    expected = dict(GOHOSTARCH='arm64', GOARCH='arm64', GOHOSTOS='linux', GOOS='linux', CGO_ENABLED='1')
    if env != expected:
        raise ValueError(f'native/race toolchain requirements not met: {env}')
    # A PATH entry alone does not show that cc links working native executables.
    with tempfile.TemporaryDirectory(prefix='oak-native-arm64-') as directory:
        source = REPO / '.github/scripts/native_arm64_host_probe.c'
        binary = Path(directory) / 'smoke'
        subprocess.run(['cc', '-std=c99', '-o', str(binary), str(source)], check=True)
        subprocess.run([str(binary)], check=True)


def pattern(names):
    if not names or len(names) != len(set(names)):
        raise ValueError('empty or duplicate test selector')
    return '^(' + '|'.join(re.escape(name) for name in names) + ')$'


def check_live_roots(package, names):
    result = subprocess.run(['go', 'test', '-race', package, '-list', pattern(names)],
                            check=True, text=True, stdout=subprocess.PIPE)
    live = [line for line in result.stdout.splitlines() if line.startswith('Test')]
    if sorted(live) != sorted(names):
        raise ValueError(f'{package}: Go test inventory does not match selected source roots')


def validate_events(events, package, names, children):
    import_path = MODULE if package == '.' else MODULE + package[1:]
    expected = set(names)
    for root, required in children.items():
        expected.update(root + '/' + child for child in required)
    started, passed = collections.Counter(), collections.Counter()
    package_start = package_pass = 0
    for event in events:
        if not isinstance(event, dict) or not isinstance(event.get('Action'), str):
            raise ValueError('malformed go test event')
        if event.get('Package') != import_path:
            raise ValueError(f'unexpected event package: {event.get("Package")}')
        action, name = event['Action'], event.get('Test')
        if action not in ('start', 'run', 'pause', 'cont', 'pass', 'bench', 'fail', 'output', 'skip'):
            raise ValueError(f'unknown go test action: {action}')
        if name is not None and (not isinstance(name, str) or not name):
            raise ValueError('malformed go test name')
        if action in ('run', 'pause', 'cont') and name is None:
            raise ValueError(f'go test {action} event is missing its test name')
        if action in ('fail', 'skip'):
            raise ValueError(f'{package}: {action}: {name or "package"}')
        if name and name not in expected:
            raise ValueError(f'{package}: unreviewed test/subtest: {name}')
        if action == 'start':
            if name is not None or package_start or started or package_pass:
                raise ValueError(f'{package}: invalid package start ordering')
            package_start += 1
        if action in ('run', 'pass'):
            if package_start != 1 or package_pass:
                raise ValueError(f'{package}: test event outside the package lifecycle')
        if action == 'run' and name:
            root = name.split('/', 1)[0]
            if name != root and (started[root] != 1 or passed[root]):
                raise ValueError(f'{package}: child outside its root lifecycle: {name}')
            started[name] += 1
        if action == 'pass':
            if name:
                if started[name] != 1:
                    raise ValueError(f'{package}: test passed before running: {name}')
                if name in children and any(passed[name + '/' + child] != 1 for child in children[name]):
                    raise ValueError(f'{package}: root passed before its required children: {name}')
                passed[name] += 1
            else:
                if any(passed[name] != 1 for name in expected):
                    raise ValueError(f'{package}: package passed before its required tests')
                package_pass += 1
    if package_pass != 1:
        raise ValueError(f'{package}: expected one successful package completion, got {package_pass}')
    for name in sorted(expected):
        if started[name] != 1 or passed[name] != 1:
            raise ValueError(f'{package}: {name}: expected exactly one run and pass; '
                             f'got {started[name]} and {passed[name]}')
    return sorted(expected)


def run_package(package, names, children, directory):
    label = 'root' if package == '.' else package[2:].replace('/', '-')
    log = directory / (label + '.jsonl')
    # Do not inherit GOFLAGS=-short/-run/-skip, which could silently reduce cases.
    env = dict(os.environ, GOFLAGS='')
    evidence = {}
    if package == '.':
        context = prerequisite._read_json(directory / 'identity.json')
        prepared = prerequisite.validate(REPO, directory, names, context)
        command = prerequisite.root_command(prepared['directory'], names)
        env[prerequisite.ENVIRONMENT] = str(directory.absolute() / prerequisite.NATIVE)
        evidence = {
            'harness_sha256': prepared['harness_sha256'],
            'success_sha256': prepared['success_sha256'],
            'environment': {prerequisite.ENVIRONMENT: env[prerequisite.ENVIRONMENT]},
        }
    else:
        env.pop(prerequisite.ENVIRONMENT, None)
        command = ['go', 'test', '-json', '-race', '-count=1', '-timeout', TIMEOUTS[package],
                   '-p', '1', package, '-run', pattern(names)]
    print(f'RUN {package}: {len(names)} roots, -race, timeout {TIMEOUTS[package]}', flush=True)
    watchdog = None
    with log.open('w') as output:
        kwargs = {'start_new_session': True} if package == '.' else {}
        process = subprocess.Popen(command, stdout=subprocess.PIPE, text=True, env=env, **kwargs)
        if package == '.':
            watchdog = prerequisite.RuntimeDeadline(process, int(TIMEOUTS[package][:-1]) * 60)
        with watchdog if watchdog is not None else nullcontext():
            assert process.stdout is not None
            events = []
            parse_error = None
            for line in process.stdout:
                output.write(line)
                output.flush()
                try:
                    event = json.loads(line)
                    events.append(event)
                    if isinstance(event, dict) and event.get('Output'):
                        print(event['Output'], end='', flush=True)
                except json.JSONDecodeError as error:
                    parse_error = error
            status = process.wait()
    if watchdog is not None:
        evidence.update(watchdog.evidence())
    (directory / (label + '-status.json')).write_text(json.dumps({
        'schema_version': 1, 'returncode': status, 'command': command, **evidence,
    }, indent=2) + '\n')
    if package == '.' and (
            prerequisite.digest(directory / prerequisite.HARNESS) != evidence['harness_sha256']
            or prerequisite.digest(directory / prerequisite.NATIVE / 'success.json') != evidence['success_sha256']):
        raise ValueError('native prover or race harness changed during root runtime')
    if watchdog is not None and (watchdog.timed_out.is_set()
                                  or watchdog.elapsed_seconds > watchdog.timeout_seconds):
        raise ValueError('root runtime exceeded its 45-minute wall deadline')
    if status != 0:
        raise ValueError(f'{package}: go test failed with exit {status}; see {log}')
    if parse_error:
        raise ValueError(f'{package}: invalid JSON test stream: {parse_error}')
    passed = validate_events(events, package, names, children)
    (directory / (label + '-passed.json')).write_text(json.dumps(passed, indent=2) + '\n')
    print(f'PASS {package}: {len(names)} roots, {len(passed) - len(names)} children; zero skips', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='source/inventory checks only; no native claim')
    parser.add_argument('--run', action='store_true', help='require native host and execute the reviewed tests')
    parser.add_argument('--shard', help='required with --run: a reviewed native shard name')
    parser.add_argument('--results-dir', type=Path, default=Path('native-arm64-results'))
    args = parser.parse_args()
    if args.check == args.run:
        parser.error('choose exactly one of --check or --run')
    if args.run and not args.shard:
        parser.error('--run requires an explicit reviewed --shard')
    if args.check and args.shard:
        parser.error('--check validates the complete partition, not one shard')
    with ResourceTelemetry(REPO) if args.run else nullcontext():
        execute(args)


def execute(args):
    os.chdir(REPO)
    manifest = json.loads(MANIFEST.read_text())
    source = subprocess.run(['go', 'run', './.github/scripts/native_arm64'],
                            check=True, text=True, stdout=subprocess.PIPE)
    selected = check_inventory(manifest, json.loads(source.stdout))
    shards = load_shards(selected, manifest, PLAN)
    print('Reviewed native ARM64 roots: ' + str({p: len(n) for p, n in selected.items()}), flush=True)
    print('Reviewed native ARM64 shards: ' + str({s: sum(map(len, p.values())) for s, p in shards.items()}), flush=True)
    if args.check:
        return
    if args.shard not in shards:
        raise ValueError(f'unreviewed native shard: {args.shard}')
    args.results_dir.mkdir(parents=True, exist_ok=True)
    if any(args.results_dir.iterdir()):
        raise ValueError('native results directory must be empty; stale receipts cannot be reused')
    context = identity(REPO, MANIFEST, PLAN, args.shard)
    (args.results_dir / 'identity.json').write_text(json.dumps(context, indent=2) + '\n')
    (args.results_dir / 'source-inventory.json').write_text(source.stdout)
    preflight()
    packages = shards[args.shard]
    failures = []
    prerequisite_failed = False
    if args.shard == 'support':
        try:
            prerequisite.prepare(REPO, args.results_dir, packages['.'], context)
        except (ValueError, subprocess.SubprocessError, OSError) as error:
            prerequisite_failed = True
            failures.append(str(error))
            print(f'FAIL native prerequisite: {error}', file=sys.stderr, flush=True)
    for package in TIMEOUTS:
        if package not in packages:
            continue
        if package == '.' and prerequisite_failed:
            # Root cannot consume a failed prerequisite. Preserve the earlier
            # runner's independent support coverage after a shell/build failure.
            print('FAIL .: prerequisite failed; root runtime was not run', file=sys.stderr, flush=True)
            continue
        names = packages[package]
        children = {root: required for root, required in manifest['children'].get(package, {}).items()
                    if root in names}
        try:
            if package != '.':
                check_live_roots(package, names)
            run_package(package, names, children, args.results_dir)
        except (ValueError, subprocess.CalledProcessError, OSError) as error:
            failures.append(str(error))
            print(f'FAIL {package}: {error}', file=sys.stderr, flush=True)
    if failures:
        raise ValueError('native shard failed:\n' + '\n'.join(failures))
    (args.results_dir / 'lane-result.json').write_text(json.dumps({
        'schema_version': 1, 'shard': args.shard, 'success': True,
        'packages': sorted(packages),
    }, indent=2) + '\n')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, subprocess.CalledProcessError, OSError) as error:
        raise SystemExit(str(error))
