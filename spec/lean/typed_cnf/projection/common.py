"""Bounded, deterministic source-only projection support.

Receipts authenticate bytes; they never assert a Lean theorem or SAT verdict.
The checked-in expected inventories pin the reviewed logical source closure.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import stat
import time

SOURCE_CAP = 8 * 1024 * 1024
TOTAL_CAP = 16 * 1024 * 1024
WORK_CAP = 16777216
METADATA_CAP = 65536
STAGES = ('refutation', 'data', 'checks', 'permutation', 'nodes',
          'bits031', 'bits145', 'reuse', 'assemble')
MODULE = re.compile(r'(?:Oak|TypedCNFInstance|TypedCNFRefutation)\.[A-Za-z][A-Za-z0-9]*')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def encode(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True,
                       separators=(',', ':')) + '\n').encode('utf-8')


def module_path(module):
    require(MODULE.fullmatch(module) is not None, 'module name')
    return Path(*module.split('.')).with_suffix('.lean')


def regular_read(path, cap):
    # Reject symlinks in every component, including the caller-supplied roots.
    path = Path(path)
    require(path.is_absolute(), 'absolute source path required')
    require(not any(p.is_symlink() for p in (path, *path.parents)), 'source symlink')
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(fd, 'rb') as stream:
        info = os.fstat(stream.fileno())
        require(stat.S_ISREG(info.st_mode) and info.st_size <= cap, 'input shape/cap')
        raw = stream.read(cap + 1)
    require(len(raw) <= cap, 'input cap')
    return raw


def expected_rows(family, budget=None):
    path = Path(__file__).absolute().parent / ('expected-' + family + '.json')
    raw = regular_read(path, METADATA_CAP)
    if budget is not None:
        budget.charge(len(raw))
    obj = json.loads(raw)
    require(obj['schema'] == 'typed-cnf-expected-source-v1', 'expected inventory schema')
    rows = obj['modules']
    require(len({r[0] for r in rows}) == len(rows), 'duplicate expected source')
    for module, sha, size in rows:
        module_path(module)
        require(re.fullmatch('[0-9a-f]{64}', sha) and type(size) is int and 0 < size <= SOURCE_CAP,
                'expected source record')
    return rows


class Stage:
    def __init__(self, name, repo, initial, work):
        require(name in STAGES, 'unknown stage')
        self.name = name
        self.repo, self.initial, self.work_root = map(Path, (repo, initial, work))
        for root in (self.repo, self.initial, self.work_root):
            require(root.is_absolute() and root.is_dir(), 'existing absolute root required')
            require(not any(p.is_symlink() for p in (root, *root.parents)), 'root symlink')
            require(root == root.resolve(), 'canonical absolute root required')
        require(self.repo != self.work_root and self.initial != self.work_root,
                'distinct source and work roots required')
        self.output = self.work_root / name
        require(not self.output.exists() and not self.output.is_symlink(), 'fresh stage output required')
        self.started, self.work = time.monotonic(), 0
        self.outputs, self.input_records, self.receipts = {}, {}, {}
        predecessors = set(STAGES[:STAGES.index(name)])
        require({p.name for p in self.work_root.iterdir()} == predecessors,
                'exact completed stage directory inventory required')
        require(all((self.work_root / p).is_dir() for p in predecessors), 'prior stage directory')
        self.initial_pins = {m: (h, n) for m, h, n in expected_rows('initial', self)}
        expected = {module_path(m).as_posix() for m in self.initial_pins}
        actual = {p.relative_to(self.initial).as_posix() for p in self.entries(self.initial)}
        require(actual == expected | {'TypedCNFInstance'}, 'exact initial source inventory required')
        self.check_physical_caps()

    def charge(self, n=1):
        require(type(n) is int and n >= 0 and n <= WORK_CAP - self.work, 'projection work cap')
        self.work += n
        require(time.monotonic() - self.started < 180, 'projection wall cap')

    def read_file(self, path, sha=None, size=None, cap=SOURCE_CAP):
        raw = regular_read(path, cap)
        self.charge(len(raw))
        require(sha is None or digest(raw) == sha, 'input source identity: ' + str(path))
        require(size is None or len(raw) == size, 'input source size: ' + str(path))
        self.input_records[str(path)] = [digest(raw), len(raw)]
        return raw

    def entries(self, root):
        for count, path in enumerate(root.rglob('*'), 1):
            self.charge(1)
            require(count <= 2048, 'filesystem entry work cap')
            require(not path.is_symlink() and (path.is_file() or path.is_dir()), 'source entry shape')
            yield path

    def raw(self, module):
        require(module in self.initial_pins, 'unknown initial source')
        sha, size = self.initial_pins[module]
        return self.read_file(self.initial / module_path(module), sha, size)

    def receipt(self, origin):
        require(origin in STAGES and STAGES.index(origin) < STAGES.index(self.name), 'stage dependency order')
        if origin not in self.receipts:
            root = self.work_root / origin
            obj = json.loads(self.read_file(root / 'PROJECTION.json', cap=METADATA_CAP))
            require(obj['schema'] == 'typed-cnf-source-projection-v1' and obj['stage'] == origin,
                    'prior receipt schema/stage')
            require(obj['kernel_checked'] is False and obj['work'] <= WORK_CAP, 'prior receipt limits')
            rows = obj['modules']
            require(len({r[0] for r in rows}) == len(rows), 'prior module uniqueness')
            paths = {module_path(r[0]).as_posix() for r in rows} | {'PROJECTION.json'}
            actual = {p.relative_to(root).as_posix() for p in self.entries(root)}
            directories = {str(module_path(r[0]).parent) for r in rows}
            require(actual == paths | directories, 'prior stage inventory')
            self.receipts[origin] = {m: (h, n) for m, h, n in rows}
        return self.receipts[origin]

    def source(self, origin, module):
        pins = self.receipt(origin)
        require(module in pins, 'missing prior source: ' + module)
        sha, size = pins[module]
        return self.read_file(self.work_root / origin / module_path(module), sha, size)

    def save(self, module, raw):
        raw = raw.encode('utf-8') if isinstance(raw, str) else raw
        require(module not in self.outputs and type(raw) is bytes, 'duplicate source/type')
        require(len(raw) <= SOURCE_CAP, 'source size cap')
        self.charge(len(raw))
        require(sum(len(v) for v in self.outputs.values()) + len(raw) <= SOURCE_CAP,
                'stage source family cap')
        module_path(module)
        self.outputs[module] = raw
        return {'file': module, 'sha256': digest(raw), 'bytes': len(raw)}

    def check_physical_caps(self, pending=0):
        sizes = {'typed': 0, 'refutation': 0}
        for root in (self.initial, self.work_root):
            for path in self.entries(root):
                if path.is_file() and path.suffix == '.lean':
                    require(path.stat().st_size <= SOURCE_CAP, 'physical source file cap')
                    family = 'refutation' if 'TypedCNFRefutation' in path.parts else 'typed'
                    sizes[family] += path.stat().st_size
                elif path.is_file():
                    require(path.suffix == '.json' and path.stat().st_size <= METADATA_CAP,
                            'physical metadata file cap')
        family = 'refutation' if self.name == 'refutation' else 'typed'
        sizes[family] += pending
        require(all(n <= SOURCE_CAP for n in sizes.values()) and sum(sizes.values()) <= TOTAL_CAP,
                'aggregate physical source family/total cap')
        return sizes

    def finish(self, expected_count, facts=None):
        require(len(self.outputs) == expected_count, 'fixed stage output count')
        total = sum(len(v) for v in self.outputs.values())
        sizes = self.check_physical_caps(total)
        # Reserve the verification read and bounded metadata before publication.
        self.charge(total + METADATA_CAP)
        rows = [[m, digest(raw), len(raw)] for m, raw in sorted(self.outputs.items())]
        receipt = encode({'schema': 'typed-cnf-source-projection-v1', 'stage': self.name,
                          'modules': rows, 'source_bytes': total, 'physical_source_bytes': sizes,
                          'work': self.work, 'work_cap': WORK_CAP, 'kernel_checked': False,
                          'facts': facts or {}})
        require(len(receipt) <= METADATA_CAP, 'projection metadata cap')
        self.output.mkdir(mode=0o700)
        for module, raw in self.outputs.items():
            self.charge(0)
            path = self.output / module_path(module)
            path.parent.mkdir(mode=0o700, exist_ok=True)
            with path.open('xb') as stream:
                require(stream.write(raw) == len(raw), 'short source write')
        with (self.output / 'PROJECTION.json').open('xb') as stream:
            require(stream.write(receipt) == len(receipt), 'short receipt write')
        for module, raw in self.outputs.items():
            self.charge(0)
            require(regular_read(self.output / module_path(module), SOURCE_CAP) == raw,
                    'published source identity')
        require(regular_read(self.output / 'PROJECTION.json', METADATA_CAP) == receipt,
                'published receipt identity')
        print(encode({'stage': self.name, 'modules': len(rows), 'source_bytes': total,
                      'work': self.work, 'kernel_checked': False}).decode().strip())
