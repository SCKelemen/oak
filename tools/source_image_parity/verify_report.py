#!/usr/bin/env python3
"""Fail closed unless the complete, exactly inventoried source-image gate finished."""
import json
from pathlib import Path
import sys
from check import validate_report

if len(sys.argv) != 2:
    raise SystemExit('usage: verify_report.py REPORT.json')
report=json.loads(Path(sys.argv[1]).read_text())
validate_report(report)
print('Required source-image composition gate completed with exact case/root inventories.')
