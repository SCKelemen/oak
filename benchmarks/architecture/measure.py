#!/usr/bin/env python3
"""Measure one command using Linux wait4 resource accounting. Preserve failure; never infer proof success."""
import argparse
import datetime
import json
import os
from pathlib import Path
import platform
import subprocess
import time


def capture(command):
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return {'exit_code': result.returncode, 'output': result.stdout.strip()}


def measure(command, output, cache_state):
    if platform.system() != 'Linux':
        raise RuntimeError('Linux is required for RSS units and wait4 accounting')
    if not command:
        raise ValueError('a command is required')
    record = {'schema_version': 1, 'command': command, 'cwd': os.getcwd(),
              'started_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'cache_state': cache_state, 'platform': platform.platform(),
              'machine': platform.machine(), 'cpu_count': os.cpu_count(),
              'revision': capture(['git', 'rev-parse', 'HEAD']),
              'worktree': capture(['git', 'status', '--porcelain']),
              'ci': {k: os.environ.get(k) for k in ('GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT', 'GITHUB_JOB', 'RUNNER_ARCH')},
              'toolchains': {}}
    for tool in ('go', 'lean', 'lake'):
        try:
            record['toolchains'][tool] = capture([tool, '--version' if tool != 'go' else 'version'])
        except FileNotFoundError:
            record['toolchains'][tool] = {'unavailable': True}
    start = time.monotonic()
    try:
        child = subprocess.Popen(command)
    except FileNotFoundError as error:
        record.update(exit_code=127, error=str(error), wall_seconds=time.monotonic() - start)
    else:
        _, status, usage = os.wait4(child.pid, 0)
        child.returncode = os.waitstatus_to_exitcode(status)
        record.update(exit_code=child.returncode, wall_seconds=time.monotonic() - start,
                      user_seconds=usage.ru_utime, system_seconds=usage.ru_stime,
                      max_rss_kib=usage.ru_maxrss,
                      memory_metric='Linux wait4 maximum child RSS; not aggregate concurrent tree RSS')
    Path(output).parent.mkdir(parents=True, exist_ok=True)
    Path(output).write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    return record['exit_code']


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True)
    parser.add_argument('--cache-state', required=True, choices=['cold-build', 'warm-build', 'unspecified'])
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    code = measure(command, args.output, args.cache_state)
    parser.exit(code if code >= 0 else 128 - code)


if __name__ == '__main__':
    main()
