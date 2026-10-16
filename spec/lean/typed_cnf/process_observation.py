"""Bounded observations only; this module never decides ownership or signals.

Capture the owner, direct positively owned children, and explicit joined child
identities. Grandchildren remain in the unchanged ownership/RSS machinery;
they enter this record if adopted as direct children. Missing observations are
null, never reconstructed from an exit status or a process name.
"""
import json
import os
from pathlib import Path

BYTE_CAP = 65536
IDENTITY_CAP = 64
EVENT_CAP = 128
COMMAND_BYTES = 256


class ProcessObservation:
    def __init__(self, scope):
        self.scope = str(scope)[:128]
        self.root = None
        self.identities = {}
        self.spawn_identities = {}
        self.events = []
        self.errors = []
        self.overflow = False
        self.dropped = 0

    def failed(self, error):
        # Callers invoke this only after an observation failure. It cannot
        # authorize a signal, reap a child, or turn incomplete evidence true.
        if len(self.errors) < 8:
            self.errors.append(str(error)[:256])
        else:
            self.overflow = True

    def _event(self, item):
        if len(self.events) >= EVENT_CAP:
            self.overflow = True
            self.dropped += 1
        else:
            self.events.append(item)

    def bind(self, root):
        self.root = list(root)

    def _details(self, pid, started):
        try:
            with Path('/proc', str(pid), 'stat').open('rb') as stream:
                before = stream.read(4097)
            if len(before) > 4096:
                self.failed('stat exceeds observation cap')
                return None
            end = before.rfind(b')')
            fields = before[end + 2:].split()
            if int(fields[19]) != started:
                return None
            with Path('/proc', str(pid), 'cmdline').open('rb') as stream:
                command = stream.read(COMMAND_BYTES + 1)
            with Path('/proc', str(pid), 'stat').open('rb') as stream:
                after = stream.read(4097)
            if len(after) > 4096:
                self.failed('second stat exceeds observation cap')
                return None
            after_fields = after[after.rfind(b')') + 2:].split()
            if int(after_fields[19]) != started:
                return None
            return {'parent': int(fields[1]), 'group': int(fields[2]),
                    'session': int(fields[3]), 'state': fields[0].decode('ascii'),
                    'comm': before[before.find(b'(') + 1:end][:64].decode(errors='backslashreplace'),
                    'command_prefix': command[:COMMAND_BYTES].decode(errors='backslashreplace'),
                    'command_truncated': len(command) > COMMAND_BYTES,
                    'command_available': bool(command)}
        except (FileNotFoundError, ProcessLookupError):
            return None

    def snapshot(self, root, owned, processes):
        self.bind(root)
        for pid, started in owned.items():
            item = processes.get(pid)
            if item is None or (pid != root[0] and item['parent'] != root[0]):
                continue
            key = (pid, started)
            if key not in self.identities:
                if len(self.identities) >= IDENTITY_CAP:
                    self.overflow = True
                    self.dropped += 1
                    continue
                self.identities[key] = {'pid': pid, 'start': started,
                                        'identity_basis': 'prior positively owned snapshot',
                                        'first': None, 'latest': None}
            details = self._details(pid, started)
            if details is not None:
                details['observed_parent_start'] = owned.get(details['parent'])
                record = self.identities[key]
                if record['first'] is None:
                    record['first'] = details
                record['latest'] = details

    def spawned(self, owner, pid, role):
        # snapshot establishes the identity using the existing parent-chain
        # checks before _details may read command bytes.
        owned, _ = owner.snapshot()
        started = owned.get(pid)
        if len(self.spawn_identities) >= IDENTITY_CAP and pid not in self.spawn_identities:
            self.overflow = True
        else:
            self.spawn_identities[pid] = started
        self._event({'kind': 'spawn', 'role': str(role)[:128], 'pid': pid,
                     'observed_identity': [pid, started] if started is not None else None})

    def _join(self, pid, raw, decoded, role, supported_start, basis):
        candidates = [[p, start] for p, start in self.identities if p == pid]
        self._event({'kind': 'join', 'role': str(role)[:128], 'pid': pid,
                     'raw_wait4_status': raw, 'decoded_status': decoded,
                     'observed_identity': [pid, supported_start] if supported_start is not None else None,
                     'historical_candidates': candidates,
                     'identity_basis': basis if supported_start is not None else 'unknown'})

    def joined_raw(self, pid, raw_status, role, pre_reap_start=None):
        # The caller supplies only a current direct-child identity observed
        # before this wait4, and consumes it after the first matching reap.
        # owner.known and archived records are not sufficient for this field.
        self.spawn_identities.pop(pid, None)
        self._join(pid, raw_status, os.waitstatus_to_exitcode(raw_status), role,
                   pre_reap_start, 'current direct-child observation before wait4')

    def joined_decoded(self, pid, returncode, role):
        # A separately observed Popen child cannot have its PID reused until
        # that direct child is joined. Consume the spawn association once.
        started = self.spawn_identities.pop(pid, None)
        self._join(pid, None, returncode, role, started, 'observed direct Popen spawn')

    def cleanup_result(self, result):
        # This is the actual existing decoded PID map, without reconstruction.
        pairs = sorted(result['statuses'].items())
        if len(pairs) > IDENTITY_CAP:
            self.overflow = True
            pairs = pairs[:IDENTITY_CAP]
        self._event({'kind': 'cleanup-result', 'joining_owner': self.root,
                     'reaped': result['reaped'], 'remaining': result['remaining'],
                     'decoded_statuses': pairs})

    def document(self):
        value = {'schema': 'oak-owned-process-observation-v1', 'scope': self.scope,
                 'owner_identity': self.root,
                 'observation_scope': 'owner and direct positively owned children; actual joins',
                 'complete': not self.overflow and not self.errors,
                 'overflow': self.overflow, 'dropped': self.dropped, 'errors': self.errors,
                 'identities': [self.identities[key] for key in sorted(self.identities)],
                 'events': self.events}
        raw = (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()
        if len(raw) > BYTE_CAP:
            # Keep a bounded partial artifact; overflow refuses acceptance only
            # after the unchanged cleanup has completed.
            value['complete'] = False
            value['overflow'] = True
            while len(raw) > BYTE_CAP and (value['events'] or value['identities']):
                if value['events']:
                    value['events'] = value['events'][:-1]
                else:
                    value['identities'] = value['identities'][:-1]
                value['dropped'] += 1
                raw = (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()
        return value

    def publish(self, path):
        # Publication is deliberately separate from observation and cleanup.
        # The caller persists this sidecar even when the workload failed.
        import hashlib
        value = self.document()
        raw = (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()
        if len(raw) > BYTE_CAP:
            raise RuntimeError('observation metadata cap')
        with Path(path).open('xb') as stream:
            if stream.write(raw) != len(raw):
                raise RuntimeError('short observation publication')
        return {'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(),
                'bytes': len(raw), 'complete': value['complete']}
