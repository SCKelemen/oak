#!/usr/bin/env python3
"""Deterministic CI obligation inventory, not a theorem or CI success oracle."""
import argparse
import hashlib
import json
from pathlib import Path
import yaml

ROOT = Path(__file__).resolve().parents[2]
LEDGER = ROOT / 'docs/spec/proof-obligations.json'


def inventory(root):
    workflows = []
    workflow_dir = root / '.github/workflows'
    for path in sorted([*workflow_dir.glob('*.yml'), *workflow_dir.glob('*.yaml')]):
        # BaseLoader preserves YAML's `on` key and scalar spelling.
        data = yaml.load(path.read_text(), Loader=yaml.BaseLoader)
        workflows.append({'path': str(path.relative_to(root)),
                          'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                          'definition': data})
    sources = []
    for directory in ('spec/lean', 'spec/lean-sail'):
        for path in sorted((root / directory).rglob('*.lean')):
            if any(part.startswith('.') for part in path.relative_to(root).parts):
                continue
            sources.append({'path': str(path.relative_to(root)),
                            'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                            'status': 'source-inventoried-not-discharge-evidence'})
    return {'schema_version': 1,
            'scope': 'CI job obligations and Lean source inventory; not individual theorem closure',
            'workflows': workflows, 'lean_sources': sources}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    expected = json.dumps(inventory(ROOT), indent=2, sort_keys=True) + '\n'
    if args.write:
        LEDGER.write_text(expected)
    elif not LEDGER.exists() or LEDGER.read_text() != expected:
        parser.exit(1, 'Obligation ledger is stale: python3 benchmarks/architecture/ledger.py --write\n')


if __name__ == '__main__':
    main()
