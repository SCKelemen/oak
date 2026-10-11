#!/usr/bin/env python3
"""Linux process-tree bounds for one authenticated, finite proof stage.

The caller places this supervisor beneath an independent GNU timeout. RSS is
sampled (not an address-space limit); the receipt says exactly which guard ran.
An absent or incomplete receipt is always failure. No command is retried.
"""
import ctypes
import hashlib
import json
import math
import os
from pathlib import Path
import resource
import signal
import stat
import subprocess
import sys
import threading
import time

from ownership import OwnedProcesses
from process_observation import ProcessObservation
from observation_acceptance import require_known_joins

GIB = 1024 ** 3
MIB = 1024 ** 2
RSS_CAP = 4026531840
LOG_CAP = 65536
RECEIPT_CAP = 14336
PRODUCT_CAP = 2048
MEMORY_FLOOR = 2 * GIB
DISK_FLOOR = 512 * MIB


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def regular(path, cap=None):
    path = Path(path)
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(descriptor, 'rb') as stream:
        info = os.fstat(stream.fileno())
        require(stat.S_ISREG(info.st_mode), 'nonregular input: ' + str(path))
        require(cap is None or info.st_size <= cap, 'input byte cap: ' + str(path))
        return stream.read() if cap is None else stream.read(cap + 1)


def sha(path):
    digest = hashlib.sha256()
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(descriptor, 'rb') as stream:
        require(stat.S_ISREG(os.fstat(stream.fileno()).st_mode), 'nonregular hash input')
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def publish(path, value, cap):
    raw = encoded(value)
    require(len(raw) <= cap, 'metadata byte cap')
    with Path(path).open('xb') as stream:
        require(stream.write(raw) == len(raw), 'short metadata write')


def available():
    for line in Path('/proc/meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'):
            return int(line.split()[1]) * 1024
    raise RuntimeError('MemAvailable unavailable')


def disk_available(root):
    value = os.statvfs(root)
    return value.f_bavail * value.f_frsize


def bytes_in(root, suffix=None):
    root = Path(root)
    if not root.exists():
        require(not root.is_symlink(), 'dangling output symlink')
        return 0
    require(root.is_dir() and not root.is_symlink(), 'output directory type')
    total = 0
    for path in root.rglob('*'):
        require(not path.is_symlink(), 'output symlink')
        if path.is_file() and (suffix is None or path.suffix == suffix):
            total += path.stat().st_size
    return total


def output_guard(spec):
    work = Path(spec['work'])
    roots = [Path(path) for path in spec.get('artifact_work_roots', [str(work)])]
    if sum(bytes_in(root / 'lib') for root in roots) > GIB:
        return 'aggregate object cap'
    # Every physical path is charged, including duplicate intermediate sources.
    family = {'typed': 0, 'refutation': 0}
    for root in roots:
        for path in (root / 'generated').rglob('*.lean'):
            require(path.is_file() and not path.is_symlink(), 'source output type')
            key = 'refutation' if 'TypedCNFRefutation' in path.parts else 'typed'
            family[key] += path.stat().st_size
    if any(total > 8 * MIB for total in family.values()) or sum(family.values()) > 16 * MIB:
        return 'generated source family cap'
    evidence_bytes = sum(bytes_in(root / 'evidence') for root in roots)
    if spec.get('ledger_root'):
        evidence_bytes += bytes_in(spec['ledger_root'])
    if evidence_bytes + spec.get('observation_reserve_bytes', 0) > 32 * MIB:
        return 'aggregate evidence cap'
    for root in roots:
        for path in (root / 'generated').rglob('*.json'):
            require(not path.is_symlink() and path.stat().st_size <= 65536, 'source metadata cap')
    return None


def sampled_stop(elapsed, seconds, rss, memory, disk, output=None):
    if output:
        return output
    if rss >= RSS_CAP:
        return 'sampled process-tree RSS guard'
    if memory < MEMORY_FLOOR:
        return 'host available memory floor'
    if disk < DISK_FLOOR:
        return 'disk floor'
    if elapsed >= seconds - 4:
        return 'stage wall guard with four-second shutdown reserve'
    return None


def check_inputs(spec):
    for path, expected in spec['inputs']:
        require(sha(path) == expected, 'stage input identity: ' + path)
    check_sources(spec)
    check_dependencies(spec.get('dependencies', []), set())
    for path in spec['products']:
        require(not Path(path).exists() and not Path(path).is_symlink(), 'fresh stage product required')
    for path in spec.get('tree_products', []):
        require(not Path(path).exists() and not Path(path).is_symlink(), 'fresh stage tree required')


def check_sources(spec):
    for path, expected in spec.get('source_manifests', []):
        raw = regular(path, 65536)
        require(hashlib.sha256(raw).hexdigest() == expected, 'source manifest identity')
        for relative, expected_hash in json.loads(raw):
            source = Path(spec['repo']) / relative
            require(source.resolve().is_relative_to(Path(spec['repo'])), 'source escapes repository')
            require(sha(source) == expected_hash, 'repository source identity: ' + relative)


def tree_inventory(root):
    root = Path(root)
    require(root.is_dir() and not root.is_symlink(), 'tree product missing')
    rows = []
    for path in sorted(root.rglob('*')):
        require(not path.is_symlink(), 'tree product symlink')
        if path.is_file():
            require(len(rows) < 1024, 'tree product file count cap')
            rows.append([str(path.relative_to(root)), sha(path), path.stat().st_size])
    return rows


def check_dependencies(dependencies, seen):
    for receipt_path, expected, execution_hash in dependencies:
        if receipt_path in seen:
            continue
        seen.add(receipt_path)
        raw = regular(receipt_path, RECEIPT_CAP)
        require(hashlib.sha256(raw).hexdigest() == expected, 'dependency receipt identity')
        receipt = json.loads(raw)
        require(receipt['returncode'] == 0 and receipt['stop_reason'] is None and
                receipt['supervisor_error'] is None and receipt['remaining_descendants'] == 0,
                'dependency is incomplete')
        directory = Path(receipt_path).parent
        execution_raw = regular(directory / 'execution.json', RECEIPT_CAP)
        require(hashlib.sha256(execution_raw).hexdigest() == execution_hash, 'outer execution identity')
        execution = json.loads(execution_raw)
        require(execution['stage_receipt_sha256'] == expected and execution['returncode'] == 0 and
                execution['error'] is None and execution['remaining_descendants'] == 0 and
                execution['spec_sha256'] == receipt['spec_sha256'], 'outer execution incomplete')
        for record in (receipt, execution):
            if 'process_observation' in record:
                check_observation(record['process_observation'], directory)
                require(record.get('observation_error') is None and record.get('cleanup_error') is None,
                        'dependency observation or cleanup error')
        require(sha(directory / 'stage.log') == receipt['stdout_sha256'], 'dependency stdout identity')
        product_raw = regular(directory / 'products.json', PRODUCT_CAP)
        require(hashlib.sha256(product_raw).hexdigest() == receipt['products_sha256'], 'dependency product binding')
        products = json.loads(product_raw)
        require(products['spec_sha256'] == receipt['spec_sha256'] and products['stage'] == receipt['stage'],
                'dependency stage binding')
        spec_path = directory.parent.parent / 'specifications' / (receipt['stage'] + '.json')
        spec_raw = regular(spec_path, 65536)
        require(hashlib.sha256(spec_raw).hexdigest() == receipt['spec_sha256'], 'dependency specification identity')
        for path, expected_hash, size in products['products']:
            require(Path(path).stat().st_size == size and sha(path) == expected_hash, 'dependency output identity')
        for root, path, expected_hash in products.get('trees', []):
            tree_raw = regular(path, 65536)
            require(hashlib.sha256(tree_raw).hexdigest() == expected_hash, 'tree inventory identity')
            require(tree_inventory(root) == json.loads(tree_raw), 'tree product identity')
        check_dependencies(json.loads(spec_raw).get('dependencies', []), seen)


def subreaper():
    libc = ctypes.CDLL(None, use_errno=True)
    libc.prctl.argtypes = [ctypes.c_int, ctypes.c_ulong, ctypes.c_ulong, ctypes.c_ulong, ctypes.c_ulong]
    libc.prctl.restype = ctypes.c_int
    require(libc.prctl(36, 1, 0, 0, 0) == 0, 'PR_SET_CHILD_SUBREAPER failed')


def check_observation(reference, directory):
    require(isinstance(reference, dict) and set(reference) == {'path', 'sha256', 'bytes', 'complete'},
            'observation reference schema')
    path = Path(reference['path'])
    require(path.parent == directory and reference['complete'] is True and
            0 < reference['bytes'] <= 65536, 'observation reference scope/cap')
    raw = regular(path, 65536)
    require(len(raw) == reference['bytes'] and hashlib.sha256(raw).hexdigest() == reference['sha256'],
            'observation identity')
    require_known_joins(json.loads(raw))


def run(spec_path, expected, started):
    raw = regular(spec_path, 65536)
    require(hashlib.sha256(raw).hexdigest() == expected, 'stage specification identity')
    spec = json.loads(raw)
    seconds = spec['seconds']
    require(isinstance(seconds, int) and 4 < seconds <= 180, 'stage time bound')
    require(math.isfinite(started) and 0 <= time.monotonic() - started < seconds, 'watchdog start')
    directory = Path(spec['directory'])
    directory.mkdir(exist_ok=False)
    process = reader = output = usage = owner = None
    observation = ProcessObservation('stage:' + spec['name'])
    observation_reference = None
    peak = reaped = 0
    reason = error = remaining = None
    cleanup_error = observation_error = None
    memory_min = disk_min = None
    streams = {'bytes': 0, 'overflow': False, 'error': None}

    def drain(pipe):
        try:
            while True:
                block = pipe.read(8192)
                if not block:
                    break
                part = block[:max(0, LOG_CAP - streams['bytes'])]
                output.write(part)
                output.flush()
                streams['bytes'] += len(part)
                if len(part) != len(block):
                    streams['overflow'] = True
        except BaseException as caught:
            streams['error'] = repr(caught)[:512]
        finally:
            pipe.close()

    def interrupted(signum, frame):
        raise InterruptedError('supervisor signal ' + str(signum))

    for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP, signal.SIGQUIT):
        signal.signal(sig, interrupted)
    try:
        check_inputs(spec)
        memory_min, disk_min = available(), disk_available(spec['work'])
        require(memory_min >= MEMORY_FLOOR and disk_min >= DISK_FLOOR, 'initial memory/disk floor')
        require(output_guard(spec) is None, 'initial output guard')
        subreaper()
        owner = OwnedProcesses(observer=observation)
        output = (directory / 'stage.log').open('xb')
        process = subprocess.Popen(spec['command'], cwd=spec['cwd'], env=spec['env'],
                                   stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, start_new_session=True,
                                   preexec_fn=lambda: resource.setrlimit(resource.RLIMIT_FSIZE, (128*MIB, 128*MIB)))
        owner.observe('spawned', owner, process.pid, 'stage workload')
        reader = threading.Thread(target=drain, args=(process.stdout,), daemon=True)
        reader.start()
        while True:
            peak = max(peak, owner.rss(include_ancestors=2))
            memory, disk = available(), disk_available(spec['work'])
            memory_min, disk_min = min(memory_min, memory), min(disk_min, disk)
            problem = output_guard(spec)
            if streams['overflow']:
                problem = 'stdout/stderr cap'
            if streams['error']:
                problem = 'output reader error'
            reason = sampled_stop(time.monotonic() - started, seconds, peak, memory, disk, problem)
            if reason:
                break
            observed, process_rows = owner.snapshot()
            pre_reap_start = (observed.get(process.pid)
                              if process_rows.get(process.pid, {}).get('parent') == owner.root[0] else None)
            waited, status, usage = os.wait4(process.pid, os.WNOHANG)
            if waited:
                owner.observe('joined_raw', waited, status, 'stage.wait4', pre_reap_start)
                process.returncode = os.waitstatus_to_exitcode(status)
                break
            time.sleep(0.02)
    except BaseException as caught:
        reason, error = 'supervisor exception', repr(caught)[:1024]
    finally:
        for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP, signal.SIGQUIT):
            signal.signal(sig, signal.SIG_IGN)
        if owner is not None:
            try:
                cleanup = owner.cleanup(seconds=2)
                reaped, remaining = cleanup['reaped'], cleanup['remaining']
                if process is not None and process.returncode is None:
                    process.returncode = cleanup['statuses'].get(process.pid, 125)
                if remaining:
                    reason = 'descendant cleanup incomplete'
            except BaseException as caught:
                reason, error = 'owned descendant cleanup failed', repr(caught)[:1024]
                cleanup_error = repr(caught)[:1024]
        if reader is not None:
            reader.join(timeout=0.25)
            if reader.is_alive() or streams['error'] or streams['overflow']:
                reason = 'output capture incomplete'
        if output is not None:
            output.close()
        result = process.returncode if process is not None else 125
        try:
            observation_reference = observation.publish(directory / 'stage-processes.json')
        except BaseException as caught:
            observation_error = repr(caught)[:512]
        try:
            check_observation(observation_reference, directory)
            require(observation_error is None and (owner is None or owner.observation_error is None),
                    'stage process observation incomplete')
            for path, expected_hash in spec['inputs']:
                require(sha(path) == expected_hash, 'input changed during stage')
            check_sources(spec)
            check_dependencies(spec.get('dependencies', []), set())
            require(output_guard(spec) is None, 'final output guard')
            require(time.monotonic() - started < seconds, 'total stage wall guard')
            if result == 0 and reason is None:
                require(remaining == 0, 'cleanup evidence missing')
                products = [[path, sha(path), Path(path).stat().st_size] for path in spec['products']]
                trees = []
                for index, root in enumerate(spec.get('tree_products', [])):
                    tree_path = directory / ('tree-%02d.json' % index)
                    publish(tree_path, tree_inventory(root), 65536)
                    trees.append([root, str(tree_path), sha(tree_path)])
                publish(directory / 'products.json', {'stage': spec['name'], 'spec_sha256': expected,
                        'products': products, 'trees': trees}, PRODUCT_CAP)
        except BaseException as caught:
            reason, error = 'terminal validation failure', repr(caught)[:1024]
        if reason is not None:
            result = 125
        receipt = {'schema': 'oak-typed-cnf-bounded-stage-v1', 'stage': spec['name'],
                   'spec_sha256': expected, 'returncode': result,
                   'wall_seconds': time.monotonic() - started,
                   'seconds': seconds, 'sampled_peak_tree_rss_bytes': peak,
                   'rss_stop_bytes': RSS_CAP, 'rss_poll_sleep_seconds': 0.02,
                   'rss_is_sampled_not_hard_limit': True, 'hard_address_space_limit': None,
                   'minimum_host_available_bytes': memory_min, 'minimum_disk_available_bytes': disk_min,
                   'stop_reason': reason, 'supervisor_error': error,
                   'reaped_descendants': reaped, 'remaining_descendants': remaining,
                   'process_observation': observation_reference,
                   'observation_error': observation_error or (owner.observation_error if owner is not None else None),
                   'cleanup_error': cleanup_error,
                   'external_watchdog_term_seconds': seconds - 4,
                   'external_watchdog_kill_seconds': seconds - 1,
                   'shutdown_reserve_seconds': 4, 'stdout_bytes': streams['bytes']}
        receipt['stdout_sha256'] = sha(directory / 'stage.log') if (directory / 'stage.log').exists() else None
        product_path = directory / 'products.json'
        if result == 0:
            receipt['products_sha256'] = sha(product_path)
        publish(directory / 'stage.json', receipt, RECEIPT_CAP)
    return result


if __name__ == '__main__':
    require(len(sys.argv) == 4, 'expected specification, digest and monotonic start')
    raise SystemExit(run(Path(sys.argv[1]), sys.argv[2], float(sys.argv[3])))
