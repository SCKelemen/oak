#!/usr/bin/env python3
"""One bounded diagnostic; never produces native ARM64 acceptance evidence.

Resource admission and one-second observations are fail-closed cutoffs, not hard
RSS/disk isolation. No cgroup, rlimit, solver allowance or Go GC setting changes.
The dedicated hosted VM remains the isolation boundary. All work is ephemeral;
only the separately named, capped result directory is uploaded.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import selectors
import shutil
import signal
import stat
import subprocess
import sys
import time
import unittest

import native_arm64_resources as resources
from native_arm64 import pattern as test_pattern, validate_events

MiB = 1024 * 1024
GiB = 1024 * MiB
JOB_SECONDS = 1800
SETUP_SECONDS = 420
BUILD_SECONDS = 540
PROFILE_SECONDS = 660
FINAL_SECONDS = 180
CLEANUP_SECONDS = 3
LOG_LIMIT = 2 * MiB
PROFILE_LIMIT = 8 * MiB
RECORD_LIMIT = MiB
RESERVE_LIMIT = 5 * MiB
ARTIFACT_LIMIT = 32 * MiB
WORK_LIMIT = 4 * GiB
RSS_LIMIT = 8 * GiB
MEMORY_RESERVE = 2 * GiB
DISK_RESERVE = 2 * GiB
SOURCE_TOTAL_LIMIT = 512 * MiB
SOURCE_MEMBER_LIMIT = 64 * MiB
SOURCE_MEMBER_COUNT = 32768
INVENTORY_LIMIT = 2 * MiB
STATUS_LIMIT = 256 * 1024
PARSER_LIMIT = 128 * 1024
PROCESS_LIMIT = 4096
PROCESS_STATUS_LIMIT = 8192
WORK_NAME = 'native-scalar-text-profile-work'
RESULT_NAME = 'native-scalar-text-profile-results'
ARTIFACT_NAME = 'native-scalar-text-profile-artifact'
INPUT_NAME = '.github/scripts/native_scalar_text_profile_inputs.json'
PROFILE_NAMES = ('cpu.pprof', 'block.pprof', 'mutex.pprof')
RECORD_NAMES = ('context.json', 'report.json', 'result.json')
CONTROL_NAMES = ('runner-status.json', 'runner-context.json', 'runner-manifest.json',
                 'diagnostic.log', 'cpu-parse.txt', 'block-parse.txt', 'mutex-parse.txt')
FINAL_MARGIN = 60  # Reserve one minute of the final allocation for upload.
GO_CONTROLS = {
    'TestScalarProfileWriterLimits': ['exact_capacity', 'overflow_preserves_prefix',
                                    'short_write', 'write_error', 'sticky_failure', 'concurrent_capacity'],
    'TestScalarProfileInputIdentity': ['exact', 'changed', 'extra', 'missing'],
    'TestScalarProfileBuildIdentity': ['exact', 'version', 'main', 'dependency', 'race', 'arch', 'duplicate'],
    'TestScalarProfileReportContract': ['exact', 'missing_function', 'duplicate_function', 'other_selected',
                                      'missing_candidate', 'extra_candidate', 'candidate_order', 'cached',
                                      'bad_digest', 'bad_outcome', 'missing_selection',
                                      'selection_not_validated', 'wrong_inventory', 'missing_supplied',
                                      'unfinished_supplied'],
    'TestScalarProfileSelectorIsolation': ['fixed_selector', 'restore_absent', 'callback_failure',
                                         'reject_selector', 'production_refuses_selector',
                                         'mode_missing_argument', 'mode_extra_argument'],
    'TestScalarProfileJSONLimits': ['exact', 'overflow', 'preexisting', 'marshal_failure'],
    'TestScalarProfileBoundedRead': ['exact', 'overflow', 'directory', 'missing'],
}
PYTHON_CONTROLS = (
    'test_phase_deadlines_share_original_origin',
    'test_resource_admission_is_measured_and_fail_closed',
    'test_log_cap_keeps_bounded_prefix_and_records_overflow',
    'test_log_write_failure_propagates', 'test_log_flush_failure_propagates',
    'test_bounded_reads_refuse_links_special_files_and_overflow',
    'test_duplicate_json_and_nonfinite_numbers_fail',
    'test_source_tree_count_and_deadline_are_bounded',
    'test_artifact_partitions_and_exact_membership',
    'test_report_requires_full_uncached_three_candidate_search',
    'test_environment_does_not_erase_experiments',
    'test_exact_source_and_support_membership',
    'test_build_settings_bind_native_race_and_disallow_overrides',
    'test_child_receipt_rejects_incomplete_or_unbound_evidence',
    'test_command_success_requires_eof_and_direct_join',
    'test_command_output_overflow_kills_and_joins',
    'test_command_timeout_kills_and_joins', 'test_profile_parser_nonzero_is_not_complete',
    'test_exited_leader_with_inherited_pipe_is_not_success',
    'test_group_is_killed_before_reaping_direct_child',
    'test_waitid_observation_never_reaps',
    'test_bounded_upload_omits_oversized_and_compiled_outputs',
    'test_process_status_reads_are_bounded',
    'test_process_status_metadata_is_strict',
    'test_process_sample_requires_owned_rss',
    'test_resource_snapshot_uses_strict_local_observation',
    'test_tool_environment_binds_authenticated_paths',
    'test_go_environment_matches_bound_compilers',
    'test_cleanup_always_attempts_direct_reap',
)


class DiagnosticError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise DiagnosticError(message)


def no_symlinks(path):
    path = Path(path).absolute()
    for component in (path, *path.parents):
        require(not component.is_symlink(), f'symlink path: {component}')
    return path


def file_bytes(path, limit, *, private=True):
    path = no_symlinks(path)
    info = path.lstat()
    require(stat.S_ISREG(info.st_mode) and (not private or info.st_nlink == 1),
            f'expected a private regular file: {path.name}')
    require(info.st_size <= limit, f'file exceeds byte limit: {path.name}')
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    def identity(value):
        return (value.st_dev, value.st_ino, value.st_mode, value.st_size,
                value.st_mtime_ns, value.st_ctime_ns, value.st_nlink)
    with os.fdopen(fd, 'rb') as source:
        opened = os.fstat(source.fileno())
        require(identity(info) == identity(opened), 'file replaced before bounded read')
        raw = source.read(limit + 1)
        after = os.fstat(source.fileno())
        named = path.lstat()
    require(identity(info) == identity(after) == identity(named)
            and len(raw) <= limit and len(raw) == info.st_size,
            f'file changed or exceeded limit: {path.name}')
    return raw


def digest(path, limit, *, private=True):
    return hashlib.sha256(file_bytes(path, limit, private=private)).hexdigest()


def unique_object(pairs):
    value = {}
    for key, item in pairs:
        require(key not in value, f'duplicate JSON key: {key}')
        value[key] = item
    return value


def read_json(path, limit=RECORD_LIMIT):
    def invalid(value):
        raise DiagnosticError(f'invalid JSON constant: {value}')
    try:
        return json.loads(file_bytes(path, limit), object_pairs_hook=unique_object,
                          parse_constant=invalid)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise DiagnosticError(f'invalid JSON: {path.name}') from error


def write_json(path, value, limit=STATUS_LIMIT):
    raw = (json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + '\n').encode()
    require(len(raw) <= limit, f'JSON exceeds byte limit: {path.name}')
    no_symlinks(path)
    with path.open('wb') as output:
        require(output.write(raw) == len(raw), 'short JSON write')
        output.flush()
        os.fsync(output.fileno())


def checked_number(value, label):
    require(type(value) in (int, float) and math.isfinite(value) and value >= 0,
            f'unknown or invalid {label}')
    return value


def phase_deadline(started, phase, now):
    """No phase may reset the original job deadline or borrow finalization."""
    checked_number(started, 'original monotonic origin')
    checked_number(now, 'current monotonic time')
    require(started <= now < started + JOB_SECONDS, 'expired/invalid job origin')
    endpoints = {'setup': started + SETUP_SECONDS,
                 'build': started + SETUP_SECONDS + BUILD_SECONDS,
                 'profile': started + JOB_SECONDS - FINAL_SECONDS,
                 'final': started + JOB_SECONDS - FINAL_MARGIN}
    allowances = {'setup': SETUP_SECONDS, 'build': BUILD_SECONDS,
                  'profile': PROFILE_SECONDS, 'final': FINAL_SECONDS - FINAL_MARGIN}
    deadline = min(endpoints[phase], now + allowances[phase])
    require(deadline > now + CLEANUP_SECONDS, f'{phase} allocation exhausted')
    return deadline


class CappedOutput:
    def __init__(self, path, limit):
        self.path, self.limit, self.count = path, limit, 0
        self.file = no_symlinks(path).open('xb')
        self.overflow = False

    def write(self, raw):
        available = self.limit - self.count
        kept = raw[:available]
        if kept:
            require(self.file.write(kept) == len(kept), 'short output write')
            self.count += len(kept)
        self.file.flush()
        if len(raw) > available:
            self.overflow = True
            raise DiagnosticError(f'output overflow: {self.path.name}')

    def close(self):
        try:
            self.file.flush()
            os.fsync(self.file.fileno())
        finally:
            self.file.close()


def signal_group(process, sig):
    try:
        os.killpg(process.pid, sig)
    except ProcessLookupError:
        pass


def child_exit(process):
    # Observe without reaping. This pins the child's PID/session identity until
    # every group signal is sent; Popen.poll/wait must not run before then.
    return os.waitid(os.P_PID, process.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)


def terminate_join(process, deadline):
    """Always terminate the owned session and join its direct child.

    Killing descendants is not a claim that an interrupted Go compile goroutine
    joined or finalized its profiles. Such a run cannot be complete evidence.
    """
    previous, cancellations, failures = {}, [], []
    # This runner owns the main Python thread. Defer repeated cancellation only
    # during bounded cleanup; every cancellation still makes the command fail.
    def deferred(signum, _frame):
        if not cancellations:
            cancellations.append(signum)
    try:
        for sig in (signal.SIGTERM, signal.SIGINT):
            previous[sig] = signal.signal(sig, deferred)
        try:
            signal_group(process, signal.SIGTERM)
            grace = min(deadline, time.monotonic() + 1)
            while child_exit(process) is None and time.monotonic() < grace:
                time.sleep(min(0.01, max(0, grace - time.monotonic())))
        except BaseException as error:
            failures.append(f'cleanup termination/observation failed: {error}'[:1024])
    finally:
        try:
            try:
                signal_group(process, signal.SIGKILL)
            except BaseException as error:
                failures.append(f'cleanup kill failed: {error}'[:1024])
        finally:
            # Observation/signalling failures must never bypass the direct reap.
            try:
                process.wait(timeout=max(0.001, min(2.0, deadline - time.monotonic())))
            except BaseException as error:
                failures.append(f'direct child did not join: {error}'[:1024])
            finally:
                for sig, handler in previous.items():
                    signal.signal(sig, handler)
    require(not cancellations and not failures,
            '; '.join(failures + ([f'cancelled during cleanup: {cancellations[0]}']
                                 if cancellations else [])))


def bounded_command(argv, sink, deadline, env, cwd, *, monitor=None,
                    capture_limit=0, evidence=None):
    """Bounded pipe reads; the output cap covers both stdout and stderr."""
    begun = time.monotonic()
    require(deadline - begun > CLEANUP_SECONDS, 'command allocation exhausted')
    end = deadline - CLEANUP_SECONDS
    raw = bytearray()
    process = None
    status = {'argv': list(argv), 'started_monotonic': begun,
              'deadline_monotonic': deadline, 'returncode': None,
              'timed_out': False, 'pipe_eof': False, 'direct_child_joined': False, 'error': ''}
    try:
        process = subprocess.Popen(argv, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   start_new_session=True, close_fds=True)
        os.set_blocking(process.stdout.fileno(), False)
        with selectors.DefaultSelector() as selector:
            selector.register(process.stdout, selectors.EVENT_READ)
            eof = False
            while True:
                now = time.monotonic()
                if now >= end:
                    status['timed_out'] = True
                    raise DiagnosticError('command reached its original deadline')
                if monitor is not None:
                    monitor(now)
                ready = selector.select(min(0.1, end - now)) if not eof else []
                if ready:
                    chunk = os.read(process.stdout.fileno(), 65536)
                    if chunk:
                        sink.write(chunk)
                        if capture_limit:
                            require(len(raw) + len(chunk) <= capture_limit,
                                    'bounded command capture overflow')
                            raw.extend(chunk)
                    else:
                        eof = True
                        status['pipe_eof'] = True
                        selector.unregister(process.stdout)
                exited = child_exit(process)
                if exited is not None and eof:
                    break
                if eof and exited is None:
                    time.sleep(min(0.05, max(0, end - time.monotonic())))
        observed_code = (exited.si_status if exited.si_code == os.CLD_EXITED else -exited.si_status)
        status['returncode'] = observed_code
        require(observed_code == 0, f'command failed with exit {observed_code}')
    except BaseException as error:
        status['error'] = str(error)[:2048]
        raise
    finally:
        try:
            if process is not None:
                try:
                    terminate_join(process, deadline)
                except BaseException as error:
                    status['error'] = f'cleanup failed: {error}'[:2048]
                    raise
                finally:
                    status['direct_child_joined'] = process.returncode is not None
                    status['returncode'] = process.returncode
        finally:
            if process is not None and process.stdout is not None:
                process.stdout.close()
            status['elapsed_seconds'] = time.monotonic() - begun
            if evidence is not None:
                evidence.append(status)
    return bytes(raw)


def tree_sizes(directory, *, max_files, deadline, allowed_dirs=None):
    """Bound logical file bytes; directory blocks are covered by statvfs reserve."""
    found, pending = {}, [(no_symlinks(directory), 0)]
    entries = 0
    while pending:
        require(time.monotonic() < deadline, 'file scan deadline expired')
        root, depth = pending.pop()
        require(depth <= 32, 'file tree exceeds depth limit')
        with os.scandir(root) as children:
            for entry in children:
                entries += 1
                require(entries <= max_files, 'file tree exceeds entry limit')
                if entries % 128 == 0:
                    require(time.monotonic() < deadline, 'file scan deadline expired')
                info = entry.stat(follow_symlinks=False)
                if stat.S_ISDIR(info.st_mode):
                    name = Path(entry.path).relative_to(directory).as_posix()
                    require(allowed_dirs is None or name in allowed_dirs,
                            f'unexpected evidence directory: {name}')
                    pending.append((Path(entry.path), depth + 1))
                else:
                    require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
                            'non-private regular member in evidence/work tree')
                    found[Path(entry.path).relative_to(directory).as_posix()] = info.st_size
    return found


def memory_available(snapshot):
    host = checked_number(snapshot.get('mem_available_bytes'), 'host memory availability')
    require(snapshot.get('cgroup_scope') == 'visible_v2_hierarchy',
            'visible cgroup memory hierarchy unavailable')
    headroom = snapshot.get('cgroup_headroom_bytes')
    if headroom == 'unlimited':
        return host
    return min(host, checked_number(headroom, 'visible cgroup headroom'))


def process_status(path):
    """Read one bounded proc status; only a disappeared PID may be omitted."""
    try:
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    except FileNotFoundError:
        try:
            path.parent.stat()
        except FileNotFoundError:
            return None
        raise DiagnosticError('live process status is unavailable')
    with os.fdopen(fd, 'rb') as source:
        require(stat.S_ISREG(os.fstat(source.fileno()).st_mode), 'non-regular process status')
        raw = source.read(PROCESS_STATUS_LIMIT + 1)
    require(len(raw) <= PROCESS_STATUS_LIMIT and raw.endswith(b'\n'),
            'truncated/oversized process status')
    return raw


def parse_process_status(raw, pid):
    fields = {}
    for line in raw.splitlines():
        key, separator, value = line.partition(b':')
        if key in (b'Pid', b'PPid', b'State', b'VmRSS'):
            require(separator and key not in fields, 'duplicate process status field')
            fields[key] = value.strip()
    def number(key):
        value = fields.get(key, b'')
        require(re.fullmatch(rb'[0-9]{1,10}', value) is not None,
                'missing/invalid process parent or PID')
        result = int(value)
        require(result < 2**31, 'process identity out of range')
        return result
    require(number(b'Pid') == pid, 'process PID differs from directory')
    parent = number(b'PPid')
    require(parent != pid, 'self-parented process')
    state = fields.get(b'State', b'')
    require(re.fullmatch(rb'[A-Za-z](?:[ \t].*)?', state) is not None,
            'missing/invalid process state')
    rss = None
    if b'VmRSS' in fields:
        match = re.fullmatch(rb'([0-9]{1,20})[ \t]+kB', fields[b'VmRSS'])
        require(match is not None and int(match[1]) < 2**54, 'invalid process RSS')
        rss = int(match[1]) * 1024
    elif state[:1] == b'Z':
        rss = 0  # A zombie has already released its address space.
    return parent, rss


def strict_process_rss(pid, deadline):
    """A bounded, non-atomic parent-graph sample, never a descendant census.

    Refuse unreadable/malformed live rows because their parent may be owned.
    A non-owned kernel thread may lack VmRSS; every sampled owned live row must
    supply it. Processes born, reparented or exited between samples remain an
    explicit sampling limitation, as do PID reuse and shared-page overcounting.
    """
    processes, scanned, vanished = {}, 0, 0
    with os.scandir(resources.PROC) as entries:
        for entry in entries:
            if re.fullmatch('[0-9]+', entry.name) is None:
                continue
            scanned += 1
            require(scanned <= PROCESS_LIMIT, 'process inventory exceeds entry cap')
            require(time.monotonic() < deadline, 'process observation deadline expired')
            child = int(entry.name)
            require(0 < child < 2**31 and child not in processes, 'invalid/duplicate process PID')
            raw = process_status(Path(entry.path) / 'status')
            if raw is None:
                vanished += 1
                continue
            processes[child] = parse_process_status(raw, child)
    require(pid in processes, 'owned runner missing from process observation')
    children = {}
    for child, (parent, _) in processes.items():
        children.setdefault(parent, []).append(child)
    descendants, pending = {pid}, [pid]
    while pending:
        for child in children.get(pending.pop(), []):
            if child not in descendants:
                descendants.add(child)
                pending.append(child)
    values = [processes[child][1] for child in descendants]
    require(all(type(value) is int for value in values), 'missing RSS in owned process sample')
    require(time.monotonic() < deadline, 'process observation deadline expired')
    return {'runner_rss_bytes': processes[pid][1], 'tree_rss_sum_bytes': sum(values),
            'tree_max_rss_bytes': max(values), 'tree_processes': len(descendants),
            'process_scan': 'complete', 'process_observation': 'strict_sample_non_atomic',
            'process_entries_scanned': scanned, 'process_entries_vanished': vanished}


def resource_snapshot(pid, directory, deadline):
    # Retain the existing host/cgroup/disk readers, but not its deliberately
    # best-effort process RSS reader. The required native helper is unchanged.
    memory = resources.keyed(resources.read_text(resources.PROC / 'meminfo'))
    result = {field: resources.kib_bytes(memory, key) for field, key in (
        ('mem_total_bytes', 'MemTotal'), ('mem_available_bytes', 'MemAvailable'),
        ('swap_total_bytes', 'SwapTotal'), ('swap_free_bytes', 'SwapFree'))}
    result.update(disk_available_bytes=resources.disk_available(directory),
                  tmp_available_bytes=resources.disk_available('/tmp'))
    result.update(resources.cgroup_memory(pid))
    result.update(strict_process_rss(pid, deadline))
    return result


def admit_resources(snapshot):
    require(memory_available(snapshot) >= RSS_LIMIT + MEMORY_RESERVE,
            'insufficient measured memory for 8 GiB envelope plus 2 GiB reserve')
    require(checked_number(snapshot.get('disk_available_bytes'), 'disk availability')
            >= WORK_LIMIT + 2 * ARTIFACT_LIMIT + DISK_RESERVE,
            'insufficient measured disk for 4 GiB work, raw/staged evidence and 2 GiB reserve')
    require(snapshot.get('process_scan') == 'complete'
            and snapshot.get('process_observation') == 'strict_sample_non_atomic',
            'strict process observation is unavailable')
    require(checked_number(snapshot.get('tree_rss_sum_bytes'), 'process tree RSS') <= RSS_LIMIT,
            'initial process sample exceeds RSS cutoff')


def validate_artifact_sizes(sizes, source_names, *, complete):
    allowed = set(PROFILE_NAMES + RECORD_NAMES + CONTROL_NAMES) | {
        'source/' + name for name in source_names}
    require(not set(sizes) - allowed, 'unexpected diagnostic artifact member')
    require(sum(sizes.values()) <= ARTIFACT_LIMIT, 'artifact exceeds 32 MiB')
    require(all(sizes.get(name, 0) <= PROFILE_LIMIT for name in PROFILE_NAMES),
            'profile exceeds 8 MiB')
    require(sum(sizes.get(name, 0) for name in RECORD_NAMES) <= RECORD_LIMIT,
            'diagnostic records exceed shared 1 MiB')
    require(sizes.get('diagnostic.log', 0) <= LOG_LIMIT, 'combined log exceeds 2 MiB')
    reserve = sum(size for name, size in sizes.items()
                  if name not in PROFILE_NAMES + RECORD_NAMES + ('diagnostic.log',))
    require(reserve <= RESERVE_LIMIT, 'source/status/parse reserve exceeds 5 MiB')
    if complete:
        required = set(PROFILE_NAMES + RECORD_NAMES) | {'source/' + n for n in source_names}
        require(required <= set(sizes), 'missing complete diagnostic artifact member')
        require(all(sizes[name] > 0 for name in required), 'empty complete evidence file')


class ResourceMonitor:
    def __init__(self, work, result, artifact, source_names, deadline):
        self.work, self.result, self.artifact = work, result, artifact
        self.source_names, self.deadline = source_names, deadline
        self.next_sample = self.next_disk_scan = 0
        self.last = None
        self.samples = 0
        self.max_rss = self.max_work = 0

    def __call__(self, now):
        if now < self.next_sample:
            return
        self.next_sample = now + 1
        self.last = resource_snapshot(os.getpid(), self.work, self.deadline)
        self.samples += 1
        require(self.last.get('process_scan') == 'complete', 'resource process scan capped')
        rss = checked_number(self.last.get('tree_rss_sum_bytes'), 'process tree RSS')
        self.max_rss = max(self.max_rss, rss)
        require(rss <= RSS_LIMIT, 'sampled process tree exceeded 8 GiB RSS cutoff')
        require(memory_available(self.last) >= MEMORY_RESERVE,
                'sampled available memory fell below 2 GiB reserve')
        require(checked_number(self.last.get('disk_available_bytes'), 'disk availability')
                >= DISK_RESERVE, 'sampled disk fell below 2 GiB reserve')
        result_sizes = (tree_sizes(self.result, max_files=128, deadline=self.deadline,
                                   allowed_dirs={'source'})
                        if self.result.exists() else {})
        artifact_sizes = tree_sizes(self.artifact, max_files=128, deadline=self.deadline,
                                    allowed_dirs={'source'})
        require(not set(result_sizes).intersection(CONTROL_NAMES),
                'child wrote an outer-controller evidence filename')
        validate_artifact_sizes(result_sizes, self.source_names, complete=False)
        validate_artifact_sizes(artifact_sizes, self.source_names, complete=False)
        require(sum(result_sizes.values()) + sum(artifact_sizes.values()) <= ARTIFACT_LIMIT,
                'combined live evidence exceeds 32 MiB')
        reserve = sum(size for sizes in (result_sizes, artifact_sizes)
                      for name, size in sizes.items()
                      if name not in PROFILE_NAMES + RECORD_NAMES + ('diagnostic.log',))
        require(reserve <= RESERVE_LIMIT, 'combined source/status reserve exceeds 5 MiB')
        if now >= self.next_disk_scan:
            self.next_disk_scan = now + 5
            sizes = tree_sizes(self.work, max_files=100000, deadline=self.deadline)
            self.max_work = max(self.max_work, sum(sizes.values()))
            require(sum(sizes.values()) <= WORK_LIMIT,
                    'sampled work/cache/temp/binary exceeded 4 GiB cutoff')

    def record(self):
        return {'admission_and_cutoff_only': True, 'hard_isolation': False,
                'sample_interval_seconds': 1, 'work_scan_interval_seconds': 5,
                'samples': self.samples, 'max_observed_tree_rss_bytes': self.max_rss,
                'max_observed_work_logical_bytes': self.max_work, 'last': self.last,
                'rss_cutoff_bytes': RSS_LIMIT, 'work_logical_cutoff_bytes': WORK_LIMIT,
                'memory_reserve_bytes': MEMORY_RESERVE, 'disk_reserve_bytes': DISK_RESERVE}


def source_identity(repo, command, env, deadline):
    for field in ('GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT'):
        require(re.fullmatch('[1-9][0-9]*', env.get(field, '')) is not None,
                'missing run/attempt identity')
    head = command(['git', 'rev-parse', 'HEAD'], 256).decode().strip()
    tree = command(['git', 'rev-parse', 'HEAD^{tree}'], 256).decode().strip()
    require(re.fullmatch('[0-9a-f]{40}|[0-9a-f]{64}', head) is not None
            and head == env.get('GITHUB_SHA'), 'checkout differs from GITHUB_SHA')
    require(re.fullmatch('[0-9a-f]{40}|[0-9a-f]{64}', tree) is not None, 'invalid source tree')
    command(['git', 'diff', '--quiet', 'HEAD', '--'], 256)
    command(['git', 'diff', '--quiet', '--cached', '--'], 256)
    untracked = command(['git', 'ls-files', '--others', '--exclude-standard', '-z'], INVENTORY_LIMIT)
    for raw in untracked.split(b'\0'):
        if raw:
            path = Path(os.fsdecode(raw))
            require(not path.is_absolute() and '..' not in path.parts
                    and path.parts[0] in (WORK_NAME, RESULT_NAME, ARTIFACT_NAME),
                    'untracked compiler/embedded input outside diagnostic directories')
    inventory = command(['git', 'ls-files', '-z'], INVENTORY_LIMIT)
    require(inventory and inventory.endswith(b'\0'), 'missing source inventory terminator')
    paths = inventory[:-1].split(b'\0')
    require(len(paths) <= SOURCE_MEMBER_COUNT and len(paths) == len(set(paths)),
            'invalid/oversized tracked source inventory')
    checksum, total = hashlib.sha256(), 0
    for raw_path in paths:
        require(time.monotonic() < deadline, 'source identity deadline expired')
        path = Path(os.fsdecode(raw_path))
        require(not path.is_absolute() and '..' not in path.parts, 'invalid tracked source path')
        raw = file_bytes(repo / path, SOURCE_MEMBER_LIMIT)
        total += len(raw)
        require(total <= SOURCE_TOTAL_LIMIT, 'tracked source exceeds total byte limit')
        checksum.update(str(len(raw_path)).encode() + b':' + raw_path + b':'
                        + hashlib.sha256(raw).hexdigest().encode() + b'\n')
    return {'source_sha': head, 'source_tree': tree,
            'source_contents_sha256': checksum.hexdigest(), 'tracked_source_bytes': total,
            'run_id': env['GITHUB_RUN_ID'], 'run_attempt': env['GITHUB_RUN_ATTEMPT']}


def tool_identity(name, command, env, deadline):
    require(time.monotonic() < deadline, 'tool identity deadline expired')
    selected = shutil.which(name, path=env.get('PATH'))
    require(selected is not None, f'missing tool executable: {name}')
    resolved = Path(selected).resolve(strict=True)
    sha = digest(resolved, 256 * MiB, private=False)
    argv = [str(resolved), 'version'] if name == 'go' else [str(resolved), '--version']
    version = command(argv, 65536).decode()
    require(version.strip(), f'empty tool version output: {name}')
    require(time.monotonic() < deadline, 'tool identity deadline expired')
    require(digest(resolved, 256 * MiB, private=False) == sha, 'tool changed while authenticating')
    return {'path': str(resolved), 'sha256': sha, 'version': version}


def bind_tool_environment(env, tools):
    require(env.get('GOENV') == 'off' and not env.get('CC') and not env.get('CXX'),
            'tool environment was not cleaned before binding')
    paths = {name: tools[name]['path'] for name in ('go', 'cc', 'c++')}
    require(all(isinstance(path, str) and path.startswith('/')
                and not any(char.isspace() or char in "\"'\\" for char in path)
                for path in paths.values()), 'unsupported tool executable path')
    return dict(env, CC=paths['cc'], CXX=paths['c++'])


def validate_tool_environment(observed, env):
    # Go 1.27.1 cfg.EnvFile returns the empty path for GOENV=off; envcmd
    # exposes that path (not the literal string "off") in `go env -json`.
    require(observed == {'GOHOSTARCH': 'arm64', 'GOARCH': 'arm64', 'GOHOSTOS': 'linux',
                         'GOOS': 'linux', 'CGO_ENABLED': '1', 'GOENV': '',
                         'CC': env['CC'], 'CXX': env['CXX']},
            'native CGO host/tool binding mismatch')


def validate_inputs(repo, result, pins, deadline):
    sources, support = pins['sources'], pins['support_sources']
    require(len(sources) == 19,
            'frozen input profile shape changed')
    sizes = tree_sizes(result / 'source', max_files=20, deadline=deadline, allowed_dirs=set())
    require(set(sizes) == set(sources), 'nineteen-source membership mismatch')
    require(sum(sizes.values()) == 909533, 'source byte total mismatch')
    for name, expected in sources.items():
        require(time.monotonic() < deadline, 'input verification deadline expired')
        require(digest(result / 'source' / name, RECORD_LIMIT) == expected,
                f'source hash mismatch: {name}')
    require(set(support) == {'stdlib/host.oak', 'stdlib/std.oak'}, 'support pin membership mismatch')
    for name, expected in support.items():
        require(time.monotonic() < deadline, 'support verification deadline expired')
        require(digest(repo / name, SOURCE_MEMBER_LIMIT) == expected,
                f'support source hash mismatch: {name}')


def validate_report(report, inventory, candidate_names):
    require(isinstance(report, dict) and report.get('schema_version') == 2
            and report.get('inventory') == inventory, 'frontend inventory differs')
    functions, supplied = report.get('functions'), report.get('supplied')
    require(isinstance(functions, list) and len(functions) == len(inventory['eligible']),
            'missing/extra native report rows')
    require(isinstance(supplied, list) and len(supplied) == len(inventory['supplied']),
            'missing/extra supplied obligation rows')
    scalar = []
    for row, expected in zip(functions, inventory['eligible']):
        require(isinstance(row, dict) and row.get('input') == expected,
                'native report input identity/order differs')
        if expected['name'] == 'scalar_text':
            scalar.append(row)
        else:
            require(not row.get('validations') and row.get('selected') is None
                    and row.get('status') == 'c-fallback', 'selector escaped scalar_text')
    require(len(scalar) == 1, 'absent/duplicate scalar_text report row')
    row = scalar[0]
    candidates = row.get('validations')
    require(isinstance(candidates, list) and len(candidates) == 3
            and [c.get('name') for c in candidates] == candidate_names,
            'normal three-candidate order/count differs')
    for candidate in candidates:
        require(candidate.get('cached') is False, 'cached native validation')
        require(candidate.get('outcome') in ('proven', 'witnessed', 'trusted', 'mismatch', 'refused'),
                'incomplete native candidate verdict')
        for key in ('body_sha256', 'recipe_sha256'):
            require(isinstance(candidate.get(key), str)
                    and re.fullmatch('[0-9a-f]{64}', candidate[key]) is not None,
                    'missing candidate body/recipe digest')
    require(row.get('selected') in candidates
            and row['selected']['outcome'] in ('proven', 'witnessed', 'trusted'),
            'final candidate lacks actual validation')
    require(row.get('status') in ('c-fallback', row['selected']['outcome'])
            and isinstance(row.get('reason'), str) and row['reason'], 'unfinished selected row')
    for row, expected in zip(supplied, inventory['supplied']):
        require(isinstance(row, dict)
                and {key: row.get(key) for key in ('input', 'arch', 'body_sha256')} == expected
                and row.get('status') in ('proven', 'witnessed', 'trusted')
                and isinstance(row.get('reason'), str) and row['reason'],
                'incomplete or changed supplied obligation')


def validate_go_build(build, expected, source_sha):
    def module(value):
        require(isinstance(value, dict) and not set(value) - {'Path', 'Version', 'Sum', 'Replace'},
                'invalid Go module identity')
        require(value.get('Replace') is None, 'Go module replacement is not allowed')
        return {key: value.get(key, '') for key in ('Path', 'Version', 'Sum')}
    require(isinstance(build, dict) and build.get('GoVersion') == expected['version']
            and module(build.get('Main')) == module(expected['main'])
            and isinstance(build.get('Deps'), list)
            and list(map(module, build['Deps'])) == list(map(module, expected['dependencies'])),
            'Go compiler/module/dependencies differ')
    rows = build.get('Settings')
    require(isinstance(rows, list), 'Go build settings missing')
    settings = {}
    for row in rows:
        require(isinstance(row, dict) and set(row) in ({'Key'}, {'Key', 'Value'})
                and isinstance(row['Key'], str) and row['Key']
                and isinstance(row.get('Value', ''), str)
                and row['Key'] not in settings, 'invalid/duplicate Go build setting')
        # runtime/debug.BuildSetting omits Value when it is the empty string.
        settings[row['Key']] = row.get('Value', '')
    require(all(settings.get(k) == v for k, v in expected['settings'].items()),
            'Go native/race setting differs')
    require(not any(settings.get(k) for k in ('-tags', '-gcflags', '-ldflags', '-cover',
                                             '-overlay', '-modfile', '-pgo', '-asmflags',
                                             '-gccgoflags', '-asan', '-msan', '-trimpath',
                                             'GOEXPERIMENT')),
            'unreviewed Go build experiment')
    require(settings.get('vcs.revision', source_sha) == source_sha
            and settings.get('vcs.modified', 'false') == 'false', 'Go VCS identity differs')


def validate_child(repo, result, artifact, pins, identity, harness_sha):
    context = read_json(result / 'context.json')
    report = read_json(result / 'report.json')
    receipt = read_json(result / 'result.json')
    fields = {'schema_version', 'kind', 'status', 'error', 'selector', 'comparable',
              'emit_completed', 'report_count', 'candidate_names', 'profiles', 'inputs_sha256',
              'outer_context_sha256', 'harness_sha256', 'block_rate_ns', 'mutex_fraction',
              'elapsed_ns', 'profile_started_unix_ns', 'profile_stopped_unix_ns'}
    require(isinstance(receipt, dict) and set(receipt) == fields and receipt['schema_version'] == 1,
            'incorrect diagnostic receipt schema')
    require(receipt['kind'] == 'scalar-text-profile-diagnostic'
            and receipt['status'] == 'diagnostic_complete_pending_outer_validation'
            and receipt['error'] == '' and receipt['selector'] == 'scalar_text'
            and receipt['comparable'] is True and receipt['emit_completed'] is True
            and type(receipt['report_count']) is int and receipt['report_count'] == 1,
            'child diagnostic is incomplete/non-comparable')
    require(receipt['candidate_names'] == pins['candidate_names']
            and receipt['block_rate_ns'] == 1000000 and receipt['mutex_fraction'] == 100,
            'candidate order or sampling rates differ')
    require(type(receipt['elapsed_ns']) is int and 0 < receipt['elapsed_ns'] <= PROFILE_SECONDS * 10**9
            and type(receipt['profile_started_unix_ns']) is int
            and type(receipt['profile_stopped_unix_ns']) is int
            and 0 < receipt['profile_started_unix_ns'] < receipt['profile_stopped_unix_ns'],
            'invalid profiling boundaries')
    require(receipt.get('harness_sha256') == harness_sha, 'child harness identity differs')
    outer_sha = digest(artifact / 'runner-context.json', 128 * 1024)
    require(receipt['inputs_sha256'] == digest(repo / INPUT_NAME, RECORD_LIMIT)
            and receipt['outer_context_sha256'] == outer_sha, 'child input/outer context binding differs')
    require(context.get('inputs') == pins and context.get('outer_context_sha256') == outer_sha
            and context.get('harness_sha256') == harness_sha and context.get('target') == 'linux/arm64'
            and context.get('c_opt_level') == 1 and context.get('gogc_environment') == '',
            'child production profile recipe differs')
    require(type(context.get('num_cpu')) is int and context['num_cpu'] > 0
            and type(context.get('gomaxprocs')) is int and context['gomaxprocs'] > 0,
            'missing observed Go scheduler context')
    validate_go_build(context.get('go_build'), pins['go_build'], identity['source_sha'])
    require(receipt.get('profiles') == {
        name: {'bytes': (result / name).stat().st_size,
               'sha256': digest(result / name, PROFILE_LIMIT)} for name in PROFILE_NAMES},
        'child profile digest mismatch')
    validate_report(report, read_json(repo / '.github/scripts/native_prover_inventory.json'),
                    pins['candidate_names'])
    return {'context': context, 'report': report, 'result': receipt}


def clean_environment(env, work):
    # Do not silently erase inherited experiments. Ordinary refusal must run
    # before this command adds its sole, observational timing setting.
    for name, value in env.items():
        if value and (name.startswith('OAK_') or name in ('OAKOPT', 'OAKCPU', 'OAKCACHE', 'OAKMODCACHE')):
            raise DiagnosticError(f'unreviewed incoming Oak environment: {name}')
    for name in ('GOFLAGS', 'GOEXPERIMENT', 'GORACE', 'GODEBUG', 'GOGC', 'GOMEMLIMIT', 'GOMAXPROCS',
                 'GOWORK', 'GOENV', 'CC', 'CXX',
                 'CPATH', 'C_INCLUDE_PATH', 'CPLUS_INCLUDE_PATH', 'LIBRARY_PATH', 'COMPILER_PATH',
                 'GCC_EXEC_PREFIX', 'LD_PRELOAD', 'LD_LIBRARY_PATH', 'LD_RUN_PATH', 'LDEMULATION',
                 'CGO_CFLAGS', 'CGO_CPPFLAGS', 'CGO_CXXFLAGS', 'CGO_LDFLAGS'):
        require(not env.get(name), f'unreviewed tool/runtime environment: {name}')
    return dict(env, CGO_ENABLED='1', GOFLAGS='', GOTOOLCHAIN='local',
                GOWORK='off', GOENV='off',
                PYTHONDONTWRITEBYTECODE='1',
                GOCACHE=str(work / 'gocache'), GOMODCACHE=str(work / 'gomodcache'),
                GOTMPDIR=str(work / 'tmp'), TMPDIR=str(work / 'tmp'),
                GIT_NO_LAZY_FETCH='1', GIT_OPTIONAL_LOCKS='0')


def stage_evidence(result, artifact, pins, status, deadline):
    """Upload only bounded known regular files, including on a failed run."""
    allowed = {name: PROFILE_LIMIT for name in PROFILE_NAMES}
    allowed.update({name: RECORD_LIMIT for name in RECORD_NAMES})
    allowed.update({'source/' + name: RECORD_LIMIT for name in pins.get('sources', {})})
    remaining_records, remaining_sources = RECORD_LIMIT, MiB
    omissions = []
    for name, limit in allowed.items():
        if time.monotonic() >= deadline:
            omissions.append('staging deadline')
            break
        path = result / name
        if not path.exists():
            continue
        try:
            require(checked_number(resources.disk_available(artifact), 'staging disk availability')
                    >= DISK_RESERVE, 'staging disk fell below 2 GiB reserve')
            raw = file_bytes(path, limit)
            if name in RECORD_NAMES:
                require(len(raw) <= remaining_records, 'shared JSON budget exhausted')
                remaining_records -= len(raw)
            elif name.startswith('source/'):
                require(len(raw) <= remaining_sources, 'source reserve exhausted')
                remaining_sources -= len(raw)
            destination = artifact / name
            if name.startswith('source/'):
                destination.parent.mkdir(mode=0o700, exist_ok=True)
            with no_symlinks(destination).open('xb') as output:
                require(output.write(raw) == len(raw), 'short staged evidence write')
                output.flush()
                os.fsync(output.fileno())
        except (OSError, DiagnosticError) as error:
            omissions.append(f'{name}: {error}'[:1024])
    if omissions:
        status['diagnostic_complete'] = False
        status['staging_omissions'] = omissions
    if 'original_started_monotonic' in status:
        status['elapsed_seconds'] = time.monotonic() - status['original_started_monotonic']
    require(time.monotonic() < deadline, 'final evidence staging deadline expired')
    write_json(artifact / 'runner-status.json', status)
    sizes = tree_sizes(artifact, max_files=128, deadline=deadline, allowed_dirs={'source'})
    validate_artifact_sizes(sizes, pins.get('sources', {}), complete=status['diagnostic_complete'])
    manifest = {}
    for name, size in sizes.items():
        require(time.monotonic() < deadline, 'final manifest hash deadline expired')
        manifest[name] = {'bytes': size, 'sha256': digest(artifact / name, ARTIFACT_LIMIT)}
    write_json(artifact / 'runner-manifest.json', manifest)
    validate_artifact_sizes(tree_sizes(artifact, max_files=128, deadline=deadline,
                                       allowed_dirs={'source'}),
                            pins.get('sources', {}), complete=status['diagnostic_complete'])


def run(repo, started):
    result, work, artifact = repo / RESULT_NAME, repo / WORK_NAME, repo / ARTIFACT_NAME
    require(not result.exists() and not work.exists() and not artifact.exists(),
            'diagnostic directories must be fresh')
    no_symlinks(repo)
    artifact.mkdir(mode=0o700)
    work.mkdir(mode=0o700)
    log = CappedOutput(artifact / 'diagnostic.log', LOG_LIMIT)
    status = {'schema_version': 1, 'diagnostic_complete': False, 'error': '',
              'original_started_monotonic': started, 'job_seconds': JOB_SECONDS,
              'commands': [], 'profile_invocations': 0, 'profile_parse': {}}
    monitor, pins, final_end = None, {}, None
    try:
        setup_end = phase_deadline(started, 'setup', time.monotonic())
        require(platform.system() == 'Linux' and platform.machine() in ('aarch64', 'arm64'),
                'diagnostic requires native Linux ARM64')
        pins = read_json(repo / INPUT_NAME)
        env = clean_environment(dict(os.environ), work)
        for name in ('gocache', 'gomodcache', 'tmp'):
            (work / name).mkdir(mode=0o700)
        admission = resource_snapshot(os.getpid(), work, setup_end)
        status['resource_admission'] = admission
        admit_resources(admission)
        monitor = ResourceMonitor(work, result, artifact, pins['sources'], setup_end)
        def command(argv, cap=0, deadline=None, sink=None, command_env=None):
            return bounded_command(argv, sink or log, deadline or setup_end,
                                   command_env or env, repo, monitor=monitor,
                                   capture_limit=cap, evidence=status['commands'])
        tools = {name: tool_identity(name, command, env, setup_end)
                 for name in ('go', 'cc', 'c++', 'clang')}
        env = bind_tool_environment(env, tools)
        go = tools['go']['path']
        status['tool_executables'] = tools
        status['toolchain_trust_scope'] = 'setup-go official distribution and hosted Ubuntu runtime; no linker/loader closure claim'
        require(tools['go']['version'].strip() == 'go version go1.27.1 linux/arm64',
                'unexpected Go compiler/version')
        tool = json.loads(command([go, 'env', '-json', 'GOHOSTARCH', 'GOARCH', 'GOHOSTOS',
                                   'GOOS', 'CGO_ENABLED', 'GOENV', 'CC', 'CXX'], 4096))
        validate_tool_environment(tool, env)
        command([go, 'mod', 'download'])
        command([go, 'mod', 'verify'])
        command([sys.executable, str(repo / '.github/scripts/native_scalar_text_profile.py'), '--controls'],
                deadline=min(setup_end, time.monotonic() + 60))
        status['python_controls'] = {'methods': 29, 'subtest_contexts': 130, 'skips': 0}
        identity = source_identity(repo, command, env, setup_end)
        status['source_identity'] = identity
        build_end = phase_deadline(started, 'build', time.monotonic())
        monitor.deadline = build_end
        harness = work / 'root-harness'
        command([go, 'test', '-c', '-race', '-mod=readonly', '-o', str(harness), '.'], deadline=build_end)
        harness_sha = digest(harness, 128 * MiB)
        status['harness_sha256'] = harness_sha
        status['harness_go_version_m'] = command([go, 'version', '-m', str(harness)],
                                               65536, deadline=build_end).decode()
        control_end = min(build_end, time.monotonic() + 60)
        raw_controls = command([go, 'tool', 'test2json', '-t', '-p', 'github.com/SCKelemen/oak',
                                '--', str(harness), '-test.v=test2json', '-test.count=1',
                                '-test.timeout=45s', '-test.run=' + test_pattern(sorted(GO_CONTROLS))],
                               RECORD_LIMIT, deadline=control_end)
        require(raw_controls.endswith(b'\n'), 'truncated harness control event stream')
        events = [json.loads(line, object_pairs_hook=unique_object)
                  for line in raw_controls.splitlines()]
        validate_events(events, '.', sorted(GO_CONTROLS), GO_CONTROLS)
        status['harness_controls'] = {'roots': 7, 'children': 47, 'skips': 0,
                                      'deadline_monotonic': control_end}
        profile_end = phase_deadline(started, 'profile', time.monotonic())
        monitor.deadline = profile_end
        outer = dict(identity, schema_version=1, harness_sha256=harness_sha,
                     input_profile_sha256=digest(repo / INPUT_NAME, RECORD_LIMIT),
                     tool_executables=tools)
        write_json(artifact / 'runner-context.json', outer, 128 * 1024)
        profile_env = dict(env, OAK_NATIVE_TIMING='1',
                           SCALAR_PROFILE_CONTEXT=str(artifact / 'runner-context.json'),
                           SCALAR_PROFILE_DEADLINE_UNIX_NS=str(time.time_ns() + int(
                               (profile_end - CLEANUP_SECONDS - time.monotonic()) * 10**9)))
        status['profile_invocations'] = 1
        command([str(harness), 'native-scalar-text-profile', str(result)],
                deadline=profile_end, command_env=profile_env)
        require(digest(harness, 128 * MiB) == harness_sha, 'harness bytes changed during diagnostic')
        final_end = phase_deadline(started, 'final', time.monotonic())
        monitor.deadline = final_end
        validate_artifact_sizes(tree_sizes(result, max_files=128, deadline=final_end,
                                           allowed_dirs={'source'}),
                                pins['sources'], complete=True)
        validate_inputs(repo, result, pins, final_end)
        validate_child(repo, result, artifact, pins, identity, harness_sha)
        for name in PROFILE_NAMES:
            parse_path = artifact / (name.removesuffix('.pprof') + '-parse.txt')
            parse = CappedOutput(parse_path, PARSER_LIMIT)
            try:
                command([go, 'tool', 'pprof', '-top', '-symbolize=none', str(result / name)],
                        deadline=final_end, sink=parse)
            finally:
                parse.close()
            status['profile_parse'][name] = {'success': True, 'output_bytes': parse.count}
        current = source_identity(repo, lambda a, c: command(a, c, deadline=final_end), env, final_end)
        require(current == identity, 'source identity changed during diagnostic')
        for tool in tools.values():
            require(time.monotonic() < final_end, 'final tool identity deadline expired')
            require(digest(Path(tool['path']), 256 * MiB, private=False) == tool['sha256'],
                    'authenticated tool executable changed during diagnostic')
        status['diagnostic_complete'] = True
    except (Exception, KeyboardInterrupt) as error:
        status['error'] = f'{type(error).__name__}: {error}'[:4096]
    finally:
        if final_end is None:
            final_end = min(started + JOB_SECONDS - FINAL_MARGIN,
                            time.monotonic() + FINAL_SECONDS - FINAL_MARGIN)
        try:
            log.close()
        except (OSError, ValueError) as error:
            status['diagnostic_complete'] = False
            status['error'] = f'log flush/close failed: {error}'[:4096]
        status['log_bytes'] = log.count
        status['log_overflow'] = log.overflow
        status['elapsed_seconds'] = time.monotonic() - started
        if monitor is not None:
            status['resources'] = monitor.record()
        if time.monotonic() >= final_end:
            status['diagnostic_complete'] = False
            status['error'] = 'original job/finalization deadline exhausted'
        try:
            stage_evidence(result, artifact, pins, status, final_end)
            require(time.monotonic() < final_end,
                    'final evidence publication crossed the original finalization deadline')
        except (Exception, KeyboardInterrupt) as error:
            status['diagnostic_complete'] = False
            status['error'] = f'bounded evidence staging failed: {error}'[:4096]
            (artifact / 'runner-manifest.json').unlink(missing_ok=True)
            write_json(artifact / 'runner-status.json', status)
    # An incomplete diagnostic is an explicit failed check, never a green skip.
    return 0 if status['diagnostic_complete'] else 1


def run_controls():
    import test_native_scalar_text_profile as controls
    case = controls.ScalarProfileOwnerTests
    actual = unittest.defaultTestLoader.getTestCaseNames(case)
    require(len(PYTHON_CONTROLS) == 29 and len(set(PYTHON_CONTROLS)) == 29
            and sorted(PYTHON_CONTROLS) == actual, 'Python control method inventory changed')
    suite = unittest.TestSuite(case(name) for name in PYTHON_CONTROLS)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if (result.wasSuccessful() and result.testsRun == 29 and not result.skipped
                 and not result.expectedFailures and not result.unexpectedSuccesses) else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--run', action='store_true')
    mode.add_argument('--controls', action='store_true')
    args = parser.parse_args()
    def interrupted(signum, _frame):
        raise DiagnosticError(f'runner interrupted by signal {signum}')
    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    try:
        if args.controls:
            return run_controls()
        started = float(os.environ['SCALAR_TEXT_JOB_STARTED'])
        return run(Path(__file__).absolute().parents[2], started)
    except (Exception, KeyboardInterrupt) as error:
        print(f'scalar_text diagnostic failed/inconclusive: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
