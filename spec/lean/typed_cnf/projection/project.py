#!/usr/bin/env python3
"""Project one finite stage; never run Lean, Go, a solver, or another process.

Use the stages in STAGES order. --instance-root contains TypedCNFInstance,
and --work-root is an existing fresh projection workspace. Each invocation
exclusively creates --work-root/STAGE. assemble publishes source inventories
referencing the immutable stage files, without copying the Lean sources.
"""
import argparse
import importlib
import sys

sys.dont_write_bytecode = True
from common import Stage, STAGES


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stage', choices=STAGES)
    parser.add_argument('--repo-root', required=True)
    parser.add_argument('--instance-root', required=True)
    parser.add_argument('--work-root', required=True)
    args = parser.parse_args()
    stage = Stage(args.stage, args.repo_root, args.instance_root, args.work_root)
    source = 'bits' if args.stage in ('bits031', 'bits145') else args.stage
    importlib.import_module(source).project(stage)


if __name__ == '__main__':
    main()
