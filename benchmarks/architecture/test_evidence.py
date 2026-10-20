import contextlib
import io
import json
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import ledger
from ledger import inventory
from measure import measure


class EvidenceTests(unittest.TestCase):
    def test_workflow_extensions_and_ledger_drift(self):
        for suffix in ('.yml', '.yaml'):
            with self.subTest(suffix=suffix), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                workflows = root / '.github/workflows'
                workflows.mkdir(parents=True)
                # Mixed suffixes must share one deterministic path ordering.
                (workflows / 'z-last.yml').write_text('on: [push]\n')
                (workflows / 'b-middle.yaml').write_text('on: [pull_request]\n')
                (workflows / 'ignored.txt').write_text('not a workflow\n')
                output = root / 'ledger.json'
                with patch.object(ledger, 'ROOT', root), patch.object(ledger, 'LEDGER', output):
                    def run(*args):
                        with patch.object(sys, 'argv', ['ledger.py', *args]):
                            ledger.main()

                    def stale():
                        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
                            run()
                        self.assertEqual(error.exception.code, 1)

                    run('--write')
                    run()
                    workflow = workflows / ('a-first' + suffix)
                    workflow.write_text('on: [push]\njobs:\n  proof:\n    steps:\n      - run: lake build\n')
                    stale()  # Adding either suffix invalidates the saved ledger.
                    run('--write')
                    run()
                    self.assertEqual(
                        [entry['path'] for entry in inventory(root)['workflows']],
                        ['.github/workflows/a-first' + suffix,
                         '.github/workflows/b-middle.yaml', '.github/workflows/z-last.yml'])
                    workflow.write_text(workflow.read_text().replace('lake build', 'lake build Proof'))
                    stale()
                    run('--write')
                    run()
                    workflow.unlink()
                    stale()
                    run('--write')
                    run()

    def test_workflow_semantics_and_source_drift(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / '.github/workflows').mkdir(parents=True)
            workflow = root / '.github/workflows/proof.yml'
            workflow.write_text('on: [pull_request]\njobs:\n  arm64:\n    if: false\n    steps:\n      - run: lake build\n        env:\n          REQUIRE: "1"\n')
            (root / 'spec/lean').mkdir(parents=True)
            source = root / 'spec/lean/Proof.lean'
            source.write_text('theorem example : True := by trivial\n')
            before = inventory(root)
            definition = before['workflows'][0]['definition']
            self.assertIn('on', definition)
            self.assertEqual(definition['jobs']['arm64']['if'], 'false')
            self.assertEqual(definition['jobs']['arm64']['steps'][0]['env']['REQUIRE'], '1')
            source.write_text('axiom example : False\n')
            self.assertNotEqual(before, inventory(root))
            workflow.unlink()
            self.assertFalse(inventory(root)['workflows'])

    def test_failure_keeps_measurement_and_exit_status(self):
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / 'failure.json'
            self.assertEqual(measure([sys.executable, '-c', 'raise SystemExit(7)'], output, 'unspecified'), 7)
            data = json.loads(output.read_text())
            self.assertEqual(data['exit_code'], 7)
            self.assertGreaterEqual(data['wall_seconds'], 0)
            self.assertGreater(data['max_rss_kib'], 0)

    def test_success_and_signal_cli(self):
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / 'sample.json'
            self.assertEqual(measure([sys.executable, '-c', 'print("sample")'], output, 'warm-build'), 0)
            result = subprocess.run([sys.executable, str(Path(__file__).with_name('measure.py')),
                                     '--output', str(output), '--cache-state', 'unspecified', '--',
                                     sys.executable, '-c', 'import os, signal; os.kill(os.getpid(), signal.SIGTERM)'])
            self.assertEqual(result.returncode, 143)
            self.assertEqual(json.loads(output.read_text())['exit_code'], -15)

    def test_missing_command_is_failure(self):
        with tempfile.TemporaryDirectory() as temp:
            self.assertEqual(measure(['/no/such/oak-command'], Path(temp) / 'missing.json', 'unspecified'), 127)


if __name__ == '__main__':
    unittest.main()
