#!/usr/bin/env python3
"""Best-effort, bounded Linux resource observations for the native ARM64 job.

One flushed line every 30 seconds, at most 481 samples plus a cleanup notice
(under 1 MiB) across the existing four-hour job. No commands, environment values, or process names are
logged. RSS is a sum for the runner and its descendants, not physical memory.
Only the visible cgroup v2 hierarchy is observable; absent fields stay explicit.
Cgroup headroom is the minimum memory.max minus memory.current across visible
ancestors, without estimating reclaimable cache; it is not host MemAvailable.
"""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

INTERVAL_SECONDS = 30
MAX_SAMPLES = 481
MAX_LINE_BYTES = 2048
MAX_PROCESSES = 4096
UNSUPPORTED = 'unsupported'
PROC = Path('/proc')
CGROUP_FIELDS = ('cgroup_current_bytes', 'cgroup_limit_bytes', 'cgroup_headroom_bytes',
                 'cgroup_oom', 'cgroup_oom_kill', 'cgroup_oom_group_kill')


def read_text(path, limit=8192):
    try:
        with path.open() as source:
            text = source.read(limit + 1)
        return text if len(text) <= limit else ''
    except (OSError, UnicodeError):
        return ''


def number(value):
    try:
        result = int(value)
        return result if 0 <= result < 2**64 else UNSUPPORTED
    except (ValueError, TypeError):
        return UNSUPPORTED


def keyed(text):
    return {parts[0].rstrip(':'): parts[1] for line in text.splitlines()
            if len(parts := line.split()) >= 2}


def kib_bytes(fields, key):
    value = number(fields.get(key))
    return value * 1024 if isinstance(value, int) else UNSUPPORTED


def disk_available(path):
    try:
        disk = os.statvfs(path)
        return disk.f_bavail * disk.f_frsize
    except OSError:
        return UNSUPPORTED


def process_rss(pid):
    """Read a capped numeric process inventory; never inspect command lines."""
    processes = {}
    complete = True
    with os.scandir(PROC) as entries:
        for entry in entries:
            if not entry.name.isdecimal():
                continue
            if len(processes) >= MAX_PROCESSES:
                complete = False
                break
            fields = keyed(read_text(Path(entry.path) / 'status'))
            processes[int(entry.name)] = (number(fields.get('PPid')), kib_bytes(fields, 'VmRSS'))
    descendants = {pid}
    # Each PID is considered once via the parent -> children index.
    children = {}
    for child, (parent, _) in processes.items():
        children.setdefault(parent, []).append(child)
    pending = [pid]
    while pending:
        for child in children.get(pending.pop(), []):
            if child not in descendants:
                descendants.add(child)
                pending.append(child)
    rss = [processes[child][1] for child in descendants if child in processes
           and isinstance(processes[child][1], int)]
    return {'runner_rss_bytes': processes.get(pid, (None, UNSUPPORTED))[1],
            'tree_rss_sum_bytes': sum(rss) if rss else UNSUPPORTED,
            'tree_max_rss_bytes': max(rss) if rss else UNSUPPORTED,
            'tree_processes': len(descendants), 'process_scan': 'complete' if complete else 'capped'}


def root_without_memory_limit(root, mount):
    # Linux exposes cgroup.type and memory.current/max only on non-root
    # cgroups, including namespace roots. Require a live core interface and
    # genuine absence of all three; unreadable/delegated roots stay unknown.
    # https://www.kernel.org/doc/html/latest/admin-guide/cgroup-v2.html
    try:
        if root != Path('/') or not (mount / 'cgroup.controllers').is_file():
            return False
        for name in ('cgroup.type', 'memory.current', 'memory.max'):
            try:
                (mount / name).stat()
            except FileNotFoundError:
                continue
            return False
    except OSError:
        return False
    return True


def cgroup_memory(pid):
    result = dict.fromkeys(CGROUP_FIELDS, UNSUPPORTED)
    result['cgroup_scope'] = UNSUPPORTED
    membership = next((line[3:] for line in read_text(PROC / str(pid) / 'cgroup').splitlines()
                       if line.startswith('0::')), None)
    if membership is None or '..' in Path(membership).parts:
        return result
    for line in read_text(PROC / 'self/mountinfo', 65536).splitlines():
        before, separator, after = line.partition(' - ')
        fields = before.split()
        if not separator or not after.startswith('cgroup2 ') or len(fields) < 5:
            continue
        # mountinfo escapes whitespace and backslashes with octal codes.
        def unescape(value):
            for code, char in (('040', ' '), ('011', '\t'), ('012', '\n'), ('134', '\\')):
                value = value.replace('\\' + code, char)
            return value
        root, mount = map(Path, map(unescape, fields[3:5]))
        try:
            leaf = mount / Path(membership).relative_to(root)
        except ValueError:
            continue
        current = number(read_text(leaf / 'memory.current').strip())
        limit = read_text(leaf / 'memory.max').strip()
        result.update(cgroup_scope='visible_v2_hierarchy', cgroup_current_bytes=current,
                      cgroup_limit_bytes='unlimited' if limit == 'max' else number(limit))
        events = keyed(read_text(leaf / 'memory.events'))
        for field in ('oom', 'oom_kill', 'oom_group_kill'):
            result['cgroup_' + field] = number(events.get(field))
        available = []
        path = leaf
        for _ in range(64):
            if path == mount and root_without_memory_limit(root, mount):
                result['cgroup_headroom_bytes'] = min(available) if available else 'unlimited'
                break
            usage = number(read_text(path / 'memory.current').strip())
            maximum = read_text(path / 'memory.max').strip()
            if not isinstance(usage, int) or (maximum != 'max' and not isinstance(number(maximum), int)):
                break
            if maximum != 'max':
                available.append(max(0, int(maximum) - usage))
            if path == mount:
                result['cgroup_headroom_bytes'] = min(available) if available else 'unlimited'
                break
            path = path.parent
        return result
    return result


def snapshot(pid, directory):
    memory = keyed(read_text(PROC / 'meminfo'))
    result = {field: kib_bytes(memory, source) for field, source in (
        ('mem_total_bytes', 'MemTotal'), ('mem_available_bytes', 'MemAvailable'),
        ('swap_total_bytes', 'SwapTotal'), ('swap_free_bytes', 'SwapFree'))}
    result.update(disk_available_bytes=disk_available(directory),
                  tmp_available_bytes=disk_available('/tmp'))
    try:
        result.update(process_rss(pid))
    except OSError:
        result.update(runner_rss_bytes=UNSUPPORTED, tree_rss_sum_bytes=UNSUPPORTED,
                      tree_max_rss_bytes=UNSUPPORTED, tree_processes=UNSUPPORTED,
                      process_scan=UNSUPPORTED)
    result.update(cgroup_memory(pid))
    return result


def emit(fields):
    fields = dict(fields, timestamp=datetime.now(timezone.utc).isoformat(timespec='seconds'))
    line = 'NATIVE_ARM64_RESOURCE ' + json.dumps(fields, sort_keys=True, separators=(',', ':')) + '\n'
    if len(line.encode()) > MAX_LINE_BYTES:
        raise ValueError('resource record exceeds output bound')
    sys.stderr.write(line)
    sys.stderr.flush()


def notice(status):
    try:
        emit({'status': status})
    except Exception:
        pass  # Even a closed job log must not replace the test result.


def sample(pid, directory):
    for index in range(MAX_SAMPLES):
        if os.getppid() != pid:
            return  # Do not remain orphaned after an interrupted runner.
        try:
            emit(dict(snapshot(pid, directory), sample=index + 1))
        except Exception:
            notice('sampler_failed')
            return
        if index + 1 < MAX_SAMPLES:
            time.sleep(INTERVAL_SECONDS)


class ResourceTelemetry:
    """Own only the observer process. Never change the runner/test exit status."""
    def __init__(self, directory):
        self.directory = directory
        self.process = None

    def __enter__(self):
        try:
            self.process = subprocess.Popen(
                [sys.executable, str(Path(__file__).resolve()), '--pid', str(os.getpid()),
                 '--directory', str(self.directory)], stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL, close_fds=True)
        except Exception:
            notice('sampler_start_failed')
        return self

    def __exit__(self, *_):
        if self.process is not None:
            try:
                self.process.terminate()
            except Exception:
                pass
            try:
                self.process.wait(timeout=1)
            except Exception:
                try:
                    self.process.kill()
                    self.process.wait(timeout=1)
                except Exception:
                    notice('sampler_cleanup_failed')
        return False


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pid', type=int, required=True)
    parser.add_argument('--directory', type=Path, required=True)
    args = parser.parse_args()
    signal.signal(signal.SIGTERM, lambda *_: sys.exit(0))
    sample(args.pid, args.directory)
