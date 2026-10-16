"""Own only descendants of this live process; signal pinned Linux pidfds.

Numeric PIDs are never kill targets. A process first enters the owned set through
an observed parent chain rooted at this process. Its /proc start time then stays
part of its identity, including after subreaper adoption. Reused PIDs refuse.
"""
import os
from pathlib import Path
import signal
import time


def state(pid):
    if not isinstance(pid, int) or pid <= 0:
        raise RuntimeError('positive process identity required')
    try:
        raw = Path('/proc', str(pid), 'stat').read_text()
    except (FileNotFoundError, ProcessLookupError):
        return None
    fields = raw[raw.rfind(')') + 2:].split()
    return {'pid': pid, 'parent': int(fields[1]), 'start': int(fields[19]),
            'rss': max(0, int(fields[21])) * os.sysconf('SC_PAGE_SIZE')}


def table():
    found = {}
    for path in Path('/proc').iterdir():
        if path.name.isdigit():
            item = state(int(path.name))
            if item is not None:
                found[item['pid']] = item
    return found


def select_owned(root, known, processes):
    """Pure ownership transition, also used by finite negative controls."""
    pid, start = root
    if not isinstance(pid, int) or pid <= 0 or start <= 0:
        raise RuntimeError('invalid root identity')
    current = processes.get(pid)
    if current is None or current['start'] != start:
        raise RuntimeError('owned root identity disappeared or changed')
    result = {pid: start}
    for child, child_start in known.items():
        item = processes.get(child)
        if item is not None and item['start'] == child_start:
            result[child] = child_start
    while True:
        added = False
        for child, item in processes.items():
            if child > 0 and child not in result and item['parent'] in result:
                # A numeric PID previously owned by this process cannot be
                # silently accepted again with a different start time.
                if child in known and known[child] != item['start']:
                    raise RuntimeError('owned descendant PID reused')
                result[child] = item['start']
                added = True
        if not added:
            return result


def signal_identity(pid, expected_start, signum):
    if pid <= 0 or pid == os.getpid() or expected_start <= 0:
        raise RuntimeError('invalid descendant signal identity')
    before = state(pid)
    if before is None:
        return False
    if before['start'] != expected_start:
        raise RuntimeError('refusing reused signal PID')
    try:
        descriptor = os.pidfd_open(pid, 0)
    except ProcessLookupError:
        return False
    try:
        after = state(pid)
        if after is None:
            return False
        if after['start'] != expected_start:
            raise RuntimeError('signal identity changed while opening pidfd')
        try:
            signal.pidfd_send_signal(descriptor, signum, None, 0)
            return True
        except ProcessLookupError:
            return False
    finally:
        os.close(descriptor)


def link_matches(child, child_identity, parent_before, parent_after, parent_identity):
    """Both live parent observations must bracket the child's live PPid read."""
    pid, started = child_identity
    parent, parent_started = parent_identity
    return (child is not None and parent_before is not None and parent_after is not None and
            child['pid'] == pid and child['start'] == started and child['parent'] == parent and
            parent_before['pid'] == parent_after['pid'] == parent and
            parent_before['start'] == parent_after['start'] == parent_started)


def confirm_link(child_identity, parent_identity):
    descriptors = []
    try:
        # The handles prevent signalling a later reused child identity; these
        # fresh reads also reject parent-chain inference from a stale /proc scan.
        for pid, _ in (parent_identity, child_identity):
            if pid <= 0:
                raise RuntimeError('nonpositive ownership edge')
            descriptors.append(os.pidfd_open(pid, 0))
        before = state(parent_identity[0])
        child = state(child_identity[0])
        after = state(parent_identity[0])
        return link_matches(child, child_identity, before, after, parent_identity)
    except ProcessLookupError:
        return False
    finally:
        for descriptor in descriptors:
            os.close(descriptor)


class OwnedProcesses:
    def __init__(self, observer=None):
        if not hasattr(os, 'pidfd_open') or not hasattr(signal, 'pidfd_send_signal'):
            raise RuntimeError('Linux pidfd signalling is required')
        current = state(os.getpid())
        if current is None:
            raise RuntimeError('cannot establish live owner identity')
        self.root = (current['pid'], current['start'])
        self.known = {self.root[0]: self.root[1]}
        self.observer = observer
        self.observation_error = None
        self._cleaning = False
        self.observe('bind', self.root)

    def observe(self, method, *args):
        """Observation failure cannot interrupt or broaden owned cleanup."""
        if self.observer is None:
            return
        try:
            getattr(self.observer, method)(*args)
        except BaseException as error:
            self.observation_error = repr(error)[:256]
            try:
                self.observer.failed(self.observation_error)
            except BaseException:
                pass
            if not self._cleaning and isinstance(error, (InterruptedError, KeyboardInterrupt, SystemExit)):
                raise

    def snapshot(self):
        processes = table()
        candidates = select_owned(self.root, self.known, processes)
        current = {pid: started for pid, started in candidates.items() if self.known.get(pid) == started}
        while True:
            added = False
            for pid, started in candidates.items():
                if pid in current:
                    continue
                parent = processes[pid]['parent']
                if parent in current and confirm_link((pid, started), (parent, current[parent])):
                    current[pid] = started
                    added = True
            if not added:
                break
        self.known.update(current)
        self.observe('snapshot', self.root, current, processes)
        return current, processes

    def rss(self, include_ancestors=0):
        owned, processes = self.snapshot()
        members = set(owned)
        current = self.root[0]
        for _ in range(include_ancestors):
            current = processes.get(current, {}).get('parent', 0)
            if current <= 0:
                break
            members.add(current)
        return sum(processes.get(pid, {}).get('rss', 0) for pid in members)

    def cleanup(self, seconds=2):
        deadline = time.monotonic() + seconds
        reaped, statuses = 0, {}
        self._cleaning = True
        try:
            while True:
                owned, processes = self.snapshot()
                reap_identities = {pid: started for pid, started in owned.items()
                                   if processes.get(pid, {}).get('parent') == self.root[0]}
                for pid, started in owned.items():
                    if pid != self.root[0]:
                        signal_identity(pid, started, signal.SIGKILL)
                while True:
                    try:
                        pid, status, _ = os.wait4(-1, os.WNOHANG)
                    except ChildProcessError:
                        owned, _ = self.snapshot()
                        result = {'reaped': reaped, 'remaining': len(owned)-1, 'statuses': statuses}
                        self.observe('cleanup_result', result)
                        return result
                    if not pid:
                        break
                    self.observe('joined_raw', pid, status, 'cleanup.wait4', reap_identities.pop(pid, None))
                    reaped += 1
                    statuses[pid] = os.waitstatus_to_exitcode(status)
                if time.monotonic() >= deadline:
                    owned, _ = self.snapshot()
                    result = {'reaped': reaped, 'remaining': max(1, len(owned)-1), 'statuses': statuses}
                    self.observe('cleanup_result', result)
                    return result
                time.sleep(0.01)
        finally:
            self._cleaning = False
