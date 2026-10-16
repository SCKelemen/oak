"""One private allocation persists across corrected work directories.

Reserve before spawning. An interrupted attempt without an authenticated final
receipt consumes its full reservation; it can never reset or refund the budget.
"""
import fcntl
import json
import math
import os
from pathlib import Path
import time

from supervise import publish, regular, require, sha

TOTAL_SECONDS = 9000


class Ledger:
    def __init__(self, requested):
        requested = Path(requested)
        require(requested.is_absolute() and requested.name not in {'.', '..'}, 'absolute ledger path required')
        parent = requested.parent.resolve(strict=True)
        self.root = parent / requested.name
        require(not self.root.is_symlink(), 'ledger symlink')
        if not self.root.exists():
            self.root.mkdir(mode=0o700)
            (self.root / 'attempts').mkdir(mode=0o700)
            publish(self.root / 'allocation.json', {'schema': 'typed-cnf-portable-allocation-v1',
                    'seconds': TOTAL_SECONDS, 'created_unix_ns': time.time_ns(),
                    'historical_proof_seconds_added': 0}, 2048)
        require(self.root.is_dir() and self.root.stat().st_mode & 0o077 == 0, 'ledger must be private')
        self.lock = (self.root / 'lock').open('a+b')
        fcntl.flock(self.lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        self.identity = sha(self.root / 'allocation.json')
        allocation = json.loads(regular(self.root / 'allocation.json', 2048))
        require(allocation['schema'] == 'typed-cnf-portable-allocation-v1' and
                allocation['seconds'] == TOTAL_SECONDS and allocation['historical_proof_seconds_added'] == 0,
                'allocation identity')
        self.spent()
        require(not self.blocked, 'allocation blocked pending separately authenticated descendant cleanup')

    def records(self):
        directory = self.root / 'attempts'
        require(directory.is_dir() and not directory.is_symlink(), 'ledger attempts directory')
        starts = sorted(directory.glob('*-start.json'))
        require(len(starts) <= 4096, 'ledger attempt count cap')
        expected_files = set()
        self.blocked = (self.root / 'blocked.json').exists()
        if self.blocked:
            block = json.loads(regular(self.root / 'blocked.json', 2048))
            require(block['allocation_sha256'] == self.identity, 'cleanup block allocation binding')
        rows = []
        for number, path in enumerate(starts):
            require(path.name == '%04d-start.json' % number, 'ledger sequence gap')
            expected_files.add(path.name)
            start = json.loads(regular(path, 4096))
            require(start['allocation_sha256'] == self.identity and start['number'] == number,
                    'attempt allocation binding')
            require(sha(start['configuration']) == start['configuration_sha256'] and
                    sha(start['specification']) == start['specification_sha256'], 'attempt source identity')
            finish_path = directory / ('%04d-finish.json' % number)
            if finish_path.exists():
                expected_files.add(finish_path.name)
                finish = json.loads(regular(finish_path, 4096))
                require(finish['start_sha256'] == sha(path), 'finish/start binding')
                raw = regular(finish['receipt'], 14336)
                require(sha(finish['receipt']) == finish['receipt_sha256'], 'attempt receipt binding')
                receipt = json.loads(raw)
                require(receipt['spec_sha256'] == start['specification_sha256'] and
                        receipt['stage'] == start['stage'], 'attempt receipt identity')
                duration = receipt['wall_seconds']
                if receipt.get('remaining_descendants') != 0:
                    self.blocked = True
                require(isinstance(duration, (int, float)) and math.isfinite(duration) and duration >= 0,
                        'attempt duration')
            else:
                duration = start['reserved_seconds']
                self.blocked = True
            require(isinstance(start['reserved_seconds'], int) and 4 < start['reserved_seconds'] <= 180,
                    'attempt reservation')
            rows.append(duration)
        require({p.name for p in directory.iterdir()} == expected_files, 'unexpected ledger record')
        return rows

    def spent(self):
        return sum(self.records())

    def work_roots(self, current):
        self.records()
        roots = {str(Path(current))}
        for path in sorted((self.root / 'attempts').glob('*-start.json')):
            row = json.loads(regular(path, 4096))
            roots.add(str(Path(row['configuration']).parent.parent))
        return sorted(roots)

    def tool_manifest_references(self):
        # A settled failure can authenticate immutable input metadata, never a
        # compiler product. records() checks every config/spec/receipt binding.
        self.records()
        require(not self.blocked, 'allocation blocked pending separately authenticated descendant cleanup')
        configs = {}
        roots = set()
        for path in sorted((self.root / 'attempts').glob('*-start.json')):
            start = json.loads(regular(path, 4096))
            config_path = Path(start['configuration'])
            if str(config_path) in configs:
                continue
            config = json.loads(regular(config_path, 65536))
            work = config_path.parent.parent
            require(config.get('work') == str(work), 'prior configuration work identity')
            roots.add(work / 'evidence/manifests')
            configs[str(config_path)] = config
        references = {}
        for config in configs.values():
            for path, expected in config.get('toolchain_manifests', []):
                source = Path(path)
                require(source.is_absolute() and source.parent in roots and
                        source.resolve(strict=True) == source and not source.is_symlink(),
                        'prior tool manifest must be a regular owned artifact')
                raw = regular(source, 65536)
                require(sha(source) == expected, 'prior tool manifest identity')
                references[str(source)] = expected
        return sorted(references.items())

    def reserve(self, stage, seconds, config, specification):
        rows = self.records()
        require(not self.blocked, 'allocation blocked pending separately authenticated descendant cleanup')
        require(sum(rows) + seconds <= TOTAL_SECONDS, 'cumulative allocation exhausted')
        number = len(rows)
        path = self.root / 'attempts' / ('%04d-start.json' % number)
        publish(path, {'number': number, 'allocation_sha256': self.identity,
                'stage': stage, 'reserved_seconds': seconds,
                'configuration': str(config), 'configuration_sha256': sha(config),
                'specification': str(specification), 'specification_sha256': sha(specification)}, 4096)
        return path

    def finish(self, start, receipt):
        number = json.loads(regular(start, 4096))['number']
        path = self.root / 'attempts' / ('%04d-finish.json' % number)
        publish(path, {'start_sha256': sha(start), 'receipt': str(receipt),
                       'receipt_sha256': sha(receipt)}, 4096)
        require(self.spent() <= TOTAL_SECONDS, 'cumulative allocation exceeded')

    def close(self):
        fcntl.flock(self.lock, fcntl.LOCK_UN)
        self.lock.close()

    def poison(self, owner_identity, reason):
        path = self.root / 'blocked.json'
        if not path.exists():
            publish(path, {'allocation_sha256': self.identity, 'owner_identity': list(owner_identity),
                           'reason': reason, 'requires_separately_authenticated_cleanup': True}, 2048)
        self.blocked = True
