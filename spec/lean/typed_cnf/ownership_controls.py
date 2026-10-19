"""Finite cleanup controls: an unrelated sibling sentinel must stay alive.

No proof source, compiler or solver is evaluated. The missing-receipt control
invokes the actual Gate.stage exceptional path with a deliberately failing
watchdog executable inside a private temporary fixture.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from ownership import OwnedProcesses, select_owned, link_matches
from supervise import subreaper, publish, sha, require, regular


def child(mode):
    subreaper()
    owner = OwnedProcesses()
    if mode == 'no-child':
        result = owner.cleanup()
        require(result['remaining'] == 0 and result['reaped'] == 0, 'no-child cleanup result')
        print('no-child passed', flush=True)
        return
    require(mode == 'missing-receipt', 'control mode')
    from ledger import Ledger
    from run import Gate
    with tempfile.TemporaryDirectory(prefix='typed-cnf-ownership-') as temp:
        root = Path(temp)
        ledger = Ledger(root / 'allocation')
        work = root / 'work'
        work.mkdir(mode=0o700)
        for name in ['evidence', 'evidence/runs', 'evidence/specifications', 'tmp', 'lib', 'generated']:
            (work / name).mkdir()
        python = str(Path(sys.executable).resolve())
        # Python refuses GNU timeout's flags and exits without a supervisor
        # receipt. This tests missing receipt cleanup without a long timeout.
        tools = {name: python for name in ['python', 'timeout', 'go', 'lean', 'cc', 'cxx']}
        config = {'work': str(work), 'repo': str(root), 'tools': tools,
                  'tool_hashes': {name: sha(path) for name, path in tools.items()},
                  'modcache': str(root), 'source_manifests': [],
                  'ledger': str(ledger.root), 'allocation_sha256': ledger.identity}
        publish(work / 'evidence/config.json', config, 65536)
        gate = Gate(config, ledger, owner)
        try:
            gate.stage('missing', [python, '-c', 'pass'], seconds=10)
        except RuntimeError as error:
            require(str(error) == 'outer execution failed: missing', 'unexpected failure path')
        else:
            raise RuntimeError('missing receipt accepted')
        receipt = json.loads(regular(work / 'evidence/runs/missing/execution.json', 14336))
        require(receipt['returncode'] != 0 and receipt['error'] == 'missing terminal supervisor receipt' and
                receipt['remaining_descendants'] == 0 and receipt['stage_receipt_sha256'] is None,
                'missing-receipt cleanup evidence')
        require(ledger.spent() > 0, 'failed attempt was not charged')
        pending = work / 'evidence/specifications/pending.json'
        publish(pending, {'stage': 'pending'}, 2048)
        ledger.reserve('pending', 5, work / 'evidence/config.json', pending)
        try:
            ledger.reserve('again', 5, work / 'evidence/config.json', pending)
        except RuntimeError as error:
            require('allocation blocked' in str(error), 'unexpected pending-cleanup failure')
        else:
            raise RuntimeError('unfinished reservation permitted another process')
        require(ledger.spent() >= 5, 'unfinished reservation was not fully charged')
        ledger.close()
        print('missing-receipt passed', flush=True)


def main():
    processes = {1: {'pid': 1, 'parent': 0, 'start': 1},
                 50: {'pid': 50, 'parent': 1, 'start': 50},
                 99: {'pid': 99, 'parent': 1, 'start': 99},
                 100: {'pid': 100, 'parent': 99, 'start': 100}}
    require(select_owned((99, 99), {99: 99}, processes) == {99: 99, 100: 100}, 'unrelated PID selected')
    for root, known in [((0, 1), {}), ((99, 98), {}), ((99, 99), {100: 98})]:
        try:
            select_owned(root, known, processes)
        except RuntimeError:
            pass
        else:
            raise RuntimeError('invalid or reused process identity accepted')
    require(not link_matches(processes[100], (100, 100), processes[99],
                             {'pid': 99, 'parent': 1, 'start': 101}, (99, 99)),
            'stale parent identity accepted')
    subreaper()
    owner = OwnedProcesses()
    sentinel = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(30)'],
                                stdin=subprocess.DEVNULL)
    owner.snapshot()
    try:
        for mode in ['no-child', 'missing-receipt']:
            result = subprocess.run([sys.executable, '-B', str(Path(__file__).resolve()), mode],
                                    stdin=subprocess.DEVNULL, timeout=8)
            require(result.returncode == 0 and sentinel.poll() is None, 'unrelated sentinel was targeted')
    finally:
        cleanup = owner.cleanup()
        require(cleanup['remaining'] == 0, 'control cleanup incomplete')
    print('owned cleanup controls passed; unrelated sentinel survived both child owners', flush=True)


if __name__ == '__main__':
    if len(sys.argv) == 2:
        child(sys.argv[1])
    else:
        require(len(sys.argv) == 1, 'control arguments')
        main()
