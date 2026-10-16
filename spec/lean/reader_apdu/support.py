"""Small bounded input helpers for the reader/APDU CI gate."""
import hashlib
import json
import math
import os
from pathlib import Path
import stat
import time


def require(condition, reason):
    if not condition:
        raise RuntimeError(reason)


def decode(data):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'duplicate JSON key')
            result[key] = value
        return result

    def bad(value):
        raise RuntimeError('nonfinite JSON')

    def depth(value, level):
        require(level <= 16, 'bounded metadata depth')
        require(type(value) is not float or math.isfinite(value), 'nonfinite JSON')
        if type(value) is dict:
            for item in value.values():
                depth(item, level + 1)
        elif type(value) is list:
            for item in value:
                depth(item, level + 1)

    value = json.loads(data.decode('utf-8', 'strict'), object_pairs_hook=pairs,
                       parse_constant=bad)
    depth(value, 0)
    return value


def safe_path(path):
    path = Path(path)
    require(path.is_absolute() and '..' not in path.parts and
            len(str(path).encode('utf-8')) <= 4096, 'absolute input path')
    require(not any(p.is_symlink() for p in (path, *path.parents)), 'input alias')
    return path


def identity(info):
    return (info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_nlink,
            info.st_size, info.st_mtime_ns, info.st_ctime_ns)


def read_regular(path, cap, snapshot=False):
    path = safe_path(path)
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        before = os.fstat(fd)
        require(stat.S_ISREG(before.st_mode) and before.st_nlink == 1 and
                before.st_uid in (0, os.getuid()) and 0 <= before.st_size <= cap,
                'regular bounded input')
        chunks = []
        size = 0
        while size <= cap:
            block = os.read(fd, min(65536, cap + 1 - size))
            if not block:
                break
            chunks.append(block)
            size += len(block)
        require(identity(before) == identity(os.fstat(fd)) ==
                identity(path.stat(follow_symlinks=False)) and size == before.st_size,
                'stable bounded input')
        data = b''.join(chunks)
        return (data, list(identity(before))) if snapshot else data
    finally:
        os.close(fd)


def verify_file(path, expected, deadline):
    require(type(expected) is dict and set(expected) == {'bytes', 'sha256'} and
            type(expected['bytes']) is int and 0 <= expected['bytes'] <= 256 * 1024**2 and
            type(expected['sha256']) is str and len(expected['sha256']) == 64 and
            all(c in '0123456789abcdef' for c in expected['sha256']), 'exact leaf identity')
    path = safe_path(path)
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        before = os.fstat(fd)
        require(stat.S_ISREG(before.st_mode) and before.st_nlink == 1 and
                before.st_uid in (0, os.getuid()) and before.st_size == expected['bytes'],
                'selected exact type/length')
        digest = hashlib.sha256()
        size = 0
        while size <= before.st_size:
            require(time.monotonic() < deadline, 'authentication original deadline')
            block = os.read(fd, min(65536, before.st_size + 1 - size))
            if not block:
                break
            digest.update(block)
            size += len(block)
        require(identity(before) == identity(os.fstat(fd)) ==
                identity(path.stat(follow_symlinks=False)) and size == before.st_size and
                digest.hexdigest() == expected['sha256'], 'selected source/tool drift')
        return {'bytes': size, 'sha256': digest.hexdigest(), 'snapshot': list(identity(before))}
    finally:
        os.close(fd)


def members(path, cap):
    path = safe_path(path)
    info = path.stat(follow_symlinks=False)
    require(stat.S_ISDIR(info.st_mode) and info.st_uid == os.getuid(), 'owned directory')
    result = set()
    with os.scandir(path) as entries:
        for entry in entries:
            require(len(result) < cap, 'directory entry cap')
            result.add(entry.name)
    return result
