#!/usr/bin/env python3
"""Exact-source reader/APDU abstract-model gate; no update or fallback mode."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import resource
import selectors
import signal
import stat
import subprocess
import sys
import time

from audit_consumer import diagnostics
from support import decode, members, read_regular, require, safe_path, verify_file

HERE = Path(__file__).absolute().parent
REPO = HERE.parents[2]
CONTRACT_SHA256 = 'c1b39dffab66c62449e1cffda580550bafc0eb55a8d26cef49fff5a454d8c015'
FLAGS = ['-j1', '-s65536', '-M1536', '-T200000', '-DmaxHeartbeats=200000',
         '-DmaxRecDepth=2048', '-DElab.async=false', '-DwarningAsError=true', '--json']
WHOLE_SECONDS = 480
FRESH_BYTES = 64 * 1024**2
FLOOR_BYTES = 560 * 1024**2


def load_contract(directory=HERE):
    data = read_regular(directory / 'contract.json', 1024**2)
    require(hashlib.sha256(data).hexdigest() == CONTRACT_SHA256, 'locked contract bytes')
    value = decode(data)
    require(value['schema'] == 'oak-reader-apdu-hosted-contract-v1' and
            value['toolchain'] == 'leanprover/lean4:v4.33.1' and value['flags'] == FLAGS,
            'fixed toolchain and flags')
    return value


def phase_deadline(whole_deadline, seconds, now):
    stop = min(whole_deadline - 30, now + seconds)
    require(stop - now > 5, 'phase has no cleanup reserve')
    return stop


class Capture:
    def __init__(self, stdout_cap):
        self.caps = {'stdout': stdout_cap, 'stderr': 512 * 1024}
        self.data = {'stdout': bytearray(), 'stderr': bytearray()}
        self.overflow = False

    def append(self, stream, block):
        left = self.caps[stream] - len(self.data[stream])
        self.data[stream].extend(block[:left])
        if len(block) > left:
            self.overflow = True
            raise RuntimeError('output cap exceeded')


def leaf_limits():
    resource.setrlimit(resource.RLIMIT_AS, (8 * 1024**3, 8 * 1024**3))
    resource.setrlimit(resource.RLIMIT_FSIZE, (8 * 1024**2, 8 * 1024**2))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    os.umask(0o077)


def proc_bytes(path):
    # Linux procfs reports zero nominal size; use a read cap rather than st_size.
    with path.open('rb', buffering=0) as stream:
        data = stream.read(65537)
    require(len(data) <= 65536, 'bounded proc observation')
    return data


def available_memory():
    data = proc_bytes(Path('/proc/meminfo'))
    for line in data.splitlines():
        if line.startswith(b'MemAvailable:'):
            return int(line.split()[1]) * 1024
    raise RuntimeError('MemAvailable missing')


def physical_guards(work, pid=None):
    storage_usage(work)
    require(available_memory() >= 2 * 1024**3, 'host available-memory floor')
    fs = os.statvfs(work)
    require(fs.f_bavail * fs.f_frsize >= FLOOR_BYTES, 'protected disk floor')
    if pid is not None:
        # The direct child remains unreaped, so this PID cannot be reused.
        data = Path('/proc') / str(pid) / 'status'
        for line in proc_bytes(data).splitlines():
            if line.startswith(b'VmRSS:'):
                rss = int(line.split()[1]) * 1024
                require(rss <= 2 * 1024**3, 'sampled direct Lean RSS cap')
                return rss
    return 0


def storage_usage(work):
    todo = [(safe_path(work), 0)]
    count = logical = 0
    allocated = Path(work).stat(follow_symlinks=False).st_blocks * 512
    require(allocated <= FRESH_BYTES, 'fresh logical/allocated output cap')
    while todo:
        directory, depth = todo.pop()
        require(depth <= 4, 'fresh directory depth cap')
        info = directory.stat(follow_symlinks=False)
        require(stat.S_ISDIR(info.st_mode) and info.st_uid == os.getuid() and
                info.st_mode & 0o077 == 0, 'private owned output directory')
        with os.scandir(directory) as entries:
            for entry in entries:
                count += 1
                require(count <= 64, 'fresh output entry cap')
                item = entry.stat(follow_symlinks=False)
                require(item.st_uid == os.getuid(), 'fresh output owner')
                allocated += item.st_blocks * 512
                if stat.S_ISDIR(item.st_mode):
                    todo.append((Path(entry.path), depth + 1))
                else:
                    require(stat.S_ISREG(item.st_mode) and item.st_nlink == 1,
                            'fresh regular unaliased output')
                    logical += item.st_size
                require(logical <= FRESH_BYTES and allocated <= FRESH_BYTES,
                        'fresh logical/allocated output cap')
    return logical, allocated


def write_new(path, data):
    require(len(data) <= 12 * 1024**2, 'bounded parent output')
    fd = os.open(safe_path(path), os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
    with os.fdopen(fd, 'wb') as stream:
        stream.write(data)


def verify_distribution(root, files, deadline):
    require(len(files) == 6289 and sum(v['bytes'] for v in files.values()) == 1100616161,
            'exact selected distribution size')
    for name, expected in files.items():
        require(not Path(name).is_absolute() and all(p not in ('', '.', '..')
                for p in name.split('/')), 'distribution relative path')
        verify_file(root / name, expected, deadline)


def inspect_objects(root, expected, deadline):
    require(members(root, 2) == {'Oak'} and members(root / 'Oak', 2) == {'Stdlib'},
            'private object directories')
    require(members(root / 'Oak/Stdlib', 3) == set(expected), 'exact object membership')
    for name, value in expected.items():
        observed = verify_file(root / 'Oak/Stdlib' / name,
                               {key: value[key] for key in ('bytes', 'sha256')}, deadline)
        require(observed['snapshot'] == value['snapshot'] and
                observed['snapshot'][3] == os.getuid() and observed['snapshot'][2] & 0o077 == 0,
                'same owned object identity')


def object_identity(path):
    data, snapshot = read_regular(path, 8 * 1024**2, snapshot=True)
    require(data, 'nonempty object')
    require(snapshot[3] == os.getuid() and snapshot[2] & 0o077 == 0, 'owned private object')
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(), 'snapshot': snapshot}


def validate_completion(status, eof, overflow, now, deadline):
    require(type(status) is int and status == 0 and eof == {'stdout', 'stderr'} and
            overflow is False and now < deadline, 'complete successful leaf')


def run_lean(argv, env, work, phase, deadline, stdout_cap):
    capture = Capture(stdout_cap)
    selector = selectors.DefaultSelector()
    child = None
    complete = set()
    error = None
    peak = 0
    status = None
    started = time.monotonic()
    try:
        require(started < deadline - 5, 'leaf launch reserve')
        physical_guards(work)
        child = subprocess.Popen(argv, cwd=work, env=env, stdin=subprocess.DEVNULL,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 start_new_session=True, preexec_fn=leaf_limits)
        for name, stream in (('stdout', child.stdout), ('stderr', child.stderr)):
            os.set_blocking(stream.fileno(), False)
            selector.register(stream, selectors.EVENT_READ, name)
        while True:
            require(time.monotonic() < deadline - 5, 'leaf useful deadline')
            peak = max(peak, physical_guards(work, child.pid))
            for key, _ in selector.select(0.1):
                block = os.read(key.fileobj.fileno(), 65536)
                if block:
                    capture.append(key.data, block)
                else:
                    complete.add(key.data)
                    selector.unregister(key.fileobj)
            # Observe without reaping; keep the owned group ID protected until cleanup.
            done = os.waitid(os.P_PID, child.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
            if done is not None and complete == {'stdout', 'stderr'}:
                break
    except BaseException as exc:
        error = exc
    finally:
        if child is not None:
            # Always signal before wait/reap: this PID still identifies our own session.
            for sig in (signal.SIGTERM, signal.SIGKILL):
                try:
                    os.killpg(child.pid, sig)
                except ProcessLookupError:
                    pass
                except OSError as exc:
                    error = error or exc
            try:
                status = child.wait(timeout=max(0.001, min(5, deadline - time.monotonic())))
            except BaseException as exc:
                error = error or exc
            for stream in (child.stdout, child.stderr):
                stream.close()
        selector.close()
        for name in ('stdout', 'stderr'):
            write_new(work / (phase + '-' + name + '.log'), capture.data[name])
        record = {'phase': phase, 'argv': argv, 'returncode': status,
                  'wall_seconds': time.monotonic() - started, 'peak_direct_rss': peak,
                  'pipe_eof': sorted(complete), 'overflow': capture.overflow,
                  'direct_child_joined': child is not None and status is not None,
                  'arbitrary_descendant_emptiness_established': False}
        write_new(work / (phase + '-execution.json'), (json.dumps(record, sort_keys=True) + '\n').encode())
    if error is not None:
        raise error
    validate_completion(status, complete, capture.overflow, time.monotonic(), deadline)
    return bytes(capture.data['stdout']), bytes(capture.data['stderr']), record


def main():
    started = time.monotonic()
    deadline = started + WHOLE_SECONDS
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', required=True)
    parser.add_argument('--work', required=True)
    args = parser.parse_args()
    def interrupted(signum, frame):
        raise RuntimeError('hosted gate interrupted')
    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    require(sys.platform == 'linux' and platform.machine() == 'x86_64', 'Linux/amd64 hosted gate')
    lean = safe_path(args.lean)
    require(lean.name == 'lean' and lean.parent.name == 'bin' and os.access(lean, os.X_OK),
            'selected executable path')
    sysroot = lean.parent.parent
    work = safe_path(args.work)
    require(not work.exists(), 'fresh work directory required')
    os.umask(0o077)
    work.mkdir(mode=0o700)
    result = {'accepted': False, 'implementation_refinement': False}
    try:
        setup_deadline = min(deadline - 30, started + 30)
        physical_guards(work)
        fs = os.statvfs(work)
        require(fs.f_bavail * fs.f_frsize >= FLOOR_BYTES + FRESH_BYTES,
                'whole fresh output admission')
        contract = load_contract()
        for relative, expected in contract['inputs'].items():
            verify_file(REPO / relative, expected, setup_deadline)
        distribution = decode(read_regular(HERE / 'distribution.json', 2 * 1024**2))
        verify_distribution(sysroot, distribution['files'], setup_deadline)
        objects = work / 'objects'
        (objects / 'Oak/Stdlib').mkdir(parents=True, mode=0o700)
        (work / 'home').mkdir(mode=0o700)
        (work / 'tmp').mkdir(mode=0o700)
        env = {'HOME': str(work / 'home'), 'TMPDIR': str(work / 'tmp'), 'LANG': 'C', 'LC_ALL': 'C',
               'PATH': str(sysroot / 'bin') + ':/usr/bin:/bin', 'LEAN_PATH': str(objects),
               'LEAN_SYSROOT': str(sysroot)}
        expected_objects = {}
        records = []
        require(time.monotonic() < setup_deadline, 'initial setup deadline')
        for phase, module, seconds in [('reader', 'BoundedReaderModel', 120),
                                       ('apdu', 'APDULengthModel', 180)]:
            inspect_objects(objects, expected_objects, deadline)
            source = REPO / 'spec/lean/Oak/Stdlib' / (module + '.lean')
            verify_file(source, contract['inputs'][str(source.relative_to(REPO))], deadline)
            target = objects / 'Oak/Stdlib' / (module + '.olean')
            argv = [str(lean), *FLAGS, '--root=' + str(REPO / 'spec/lean'), '-o', str(target), str(source)]
            stop = phase_deadline(deadline, seconds, time.monotonic())
            stdout, stderr, record = run_lean(argv, env, work, phase, stop, 512 * 1024)
            diagnostics(stdout, stderr, phase, stop, HERE / 'AuditDriver.lean', contract)
            expected_objects[target.name] = object_identity(target)
            inspect_objects(objects, expected_objects, stop)
            records.append(record)
        argv = [str(lean), *FLAGS, '--root=' + str(HERE), str(HERE / 'AuditDriver.lean')]
        verify_file(HERE / 'AuditDriver.lean', contract['inputs']['spec/lean/reader_apdu/AuditDriver.lean'], deadline)
        stop = phase_deadline(deadline, 120, time.monotonic())
        stdout, stderr, record = run_lean(argv, env, work, 'audit', stop, 12 * 1024**2)
        summary = diagnostics(stdout, stderr, 'audit', stop, HERE / 'AuditDriver.lean', contract)
        records.append(record)
        require(summary['candidate_declarations'] == 500, 'locked candidate declaration count')
        final_deadline = min(deadline, time.monotonic() + 30)
        inspect_objects(objects, expected_objects, final_deadline)
        for relative, expected in contract['inputs'].items():
            verify_file(REPO / relative, expected, final_deadline)
        require(load_contract() == contract, 'contract stable after run')
        verify_distribution(sysroot, distribution['files'], final_deadline)
        physical_guards(work)
        expected_names = {'objects', 'home', 'tmp'} | {
            phase + suffix for phase in ('reader', 'apdu', 'audit')
            for suffix in ('-stdout.log', '-stderr.log', '-execution.json')}
        require(members(work, 16) == expected_names and not members(work / 'home', 1) and
                not members(work / 'tmp', 1), 'exact fresh output membership')
        retained = sum((work / name).stat().st_size for name in expected_names - {'objects', 'home', 'tmp'})
        retained += sum(v['bytes'] for v in expected_objects.values())
        require(retained + 65536 <= FRESH_BYTES and time.monotonic() < final_deadline - 1,
                'fresh output/whole deadline bound')
        result.update(accepted=True, audit=summary, objects=expected_objects,
                      direct_processes=records, source_contract_sha256=CONTRACT_SHA256,
                      host_tcb='Ubuntu runner, Python stdlib, system loader/libraries; not local host pins',
                      official_distribution_members=6289, selected_bytes_per_pass=1100616161,
                      imported_distribution_normal_trust=True, whole_seconds=time.monotonic()-started,
                      limits_scope='hard direct-process AS/FSIZE/core; sampled host floor/direct RSS; no escaped-descendant claim')
    except BaseException as exc:
        result['error'] = (type(exc).__name__ + ': ' + str(exc))[:2048]
        raise
    finally:
        write_new(work / 'result.json', (json.dumps(result, sort_keys=True) + '\n').encode())
        print(json.dumps({'accepted': result['accepted'], 'result': str(work / 'result.json')}), flush=True)


if __name__ == '__main__':
    main()
