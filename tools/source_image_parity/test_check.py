#!/usr/bin/env python3
"""Lightweight fail-closed inventory/report controls; no Lean or fixture build."""
import json
import os
import subprocess
import tempfile
from pathlib import Path
import sys
import unittest
from unittest.mock import patch
import check

class GateControls(unittest.TestCase):
    def test_pinned_lean_environment_overrides_inherited_selection(self):
        with patch.dict(os.environ, {'ELAN_TOOLCHAIN':'unrelated-toolchain', 'LEAN_PATH':'unrelated-library'}):
            env=check.lean_environment(Path('/isolated/evidence'))
            self.assertEqual(env['ELAN_TOOLCHAIN'],check.PINNED_TOOLCHAIN)
            self.assertEqual(env['LEAN_PATH'],os.pathsep.join([
                '/isolated/evidence',str(check.LEAN/'.lake/build/lib/lean')]))
            self.assertEqual(env['PATH'],os.environ['PATH'])
            self.assertEqual(os.environ['ELAN_TOOLCHAIN'],'unrelated-toolchain')
            self.assertEqual(os.environ['LEAN_PATH'],'unrelated-library')

    def test_wrong_or_missing_toolchain_fails_before_launch(self):
        with tempfile.TemporaryDirectory() as temp:
            directory=Path(temp)
            with patch.object(check,'LEAN',directory), patch.object(check,'run') as launch, \
                    patch.object(sys,'argv',['check.py',temp,'--output',str(directory/'evidence')]):
                for pin in [None,'leanprover/lean4:v4.33.0','',check.PINNED_TOOLCHAIN+'\nother']:
                    if pin is not None:(directory/'lean-toolchain').write_text(pin)
                    with self.subTest(pin=pin), self.assertRaises(SystemExit):check.main()
                launch.assert_not_called()

    def test_main_passes_pinned_environment_to_launcher(self):
        class StopAfterVersion(Exception):pass
        with tempfile.TemporaryDirectory() as temp:
            output=Path(temp).resolve()
            with patch.dict(os.environ,{'ELAN_TOOLCHAIN':'unrelated-toolchain'}), \
                    patch.object(sys,'argv',['check.py',temp,'--output',temp]), \
                    patch.object(check,'run',side_effect=StopAfterVersion) as launch:
                with self.assertRaises(StopAfterVersion):check.main()
                args=launch.call_args.args
                self.assertEqual(args[:3],(['lean','--version'],check.LEAN,output/'lean-version.log'))
                self.assertEqual(args[3],check.lean_environment(output))

    def test_no_default_shim_in_isolated_evidence_directory(self):
        # Model elan's relevant selection rules without installing a toolchain in
        # this lightweight suite. The mandatory hosted gate uses the real shim.
        with tempfile.TemporaryDirectory() as temp:
            directory=Path(temp).resolve()
            evidence=directory/'evidence';evidence.mkdir()
            home=directory/'empty-elan-home';home.mkdir()
            project=directory/'project';project.mkdir()
            (project/'lean-toolchain').write_text(check.PINNED_TOOLCHAIN+'\n')
            shim=directory/'lean'
            shim.write_text('#!'+sys.executable+'\n'+'''import json, os, sys
from pathlib import Path
selected=os.environ.get('ELAN_TOOLCHAIN')
if not selected:
    for parent in [Path.cwd(),*Path.cwd().parents]:
        pin=parent/'lean-toolchain'
        if pin.exists():
            selected=pin.read_text().strip()
            break
if not selected:
    print('error: no default toolchain configured')
    sys.exit(1)
print(json.dumps(dict(toolchain=selected,cwd=str(Path.cwd()),args=sys.argv[1:])))
''')
            shim.chmod(0o755)
            with patch.dict(os.environ,{'ELAN_HOME':str(home)}), patch.object(check,'LEAN',project):
                bare=dict(os.environ);bare.pop('ELAN_TOOLCHAIN',None)
                failed=subprocess.run([str(shim),'--version'],cwd=evidence,env=bare,
                                      text=True,capture_output=True,timeout=10)
                self.assertNotEqual(failed.returncode,0)
                self.assertIn('no default toolchain configured',failed.stdout)
                env=check.lean_environment(evidence)
                flags=['-j1','-M3000','--trust=0','Request.lean']
                for cwd in [project,evidence]:
                    output=check.run([str(shim),*flags],cwd,evidence/(cwd.name+'.log'),env)
                    self.assertEqual(json.loads(output),dict(toolchain=check.PINNED_TOOLCHAIN,
                                     cwd=str(cwd),args=flags))
                self.assertFalse((evidence/'lean-toolchain').exists())
                self.assertEqual(list(home.iterdir()),[])

    def report(self):
        p=check.case_inventory()
        roots=json.loads((check.ROOT/'tools/source_image_parity/expected-roots.json').read_text())
        native=json.loads((check.NATIVE/'evidence.json').read_text())
        inputs={}
        for pair in p['pairs']:
            for arch in ['arm64','riscv64']:
                pin=native[arch+'_'+pair[0]]
                item=dict(image_length=pin['length'],image_sha256=pin['sha256'],source_sha256=pin['source_sha256'])
                if arch=='arm64': item['wasm_sha256']='2'*64
                inputs[arch+'_'+pair[0]]=item
        return dict(p['counts'],schema='oak.source-image-parity.tests.v1',complete=True,
                    cases={k:p[k] for k in ['pairs','source_refusals','auditor_refusals','late_failures']},
                    seconds=1.0,max_child_rss_kib=1,scope='test',inputs=inputs,
                    model_sha256=roots['model_sha256'],audit_sha256=roots['audit_sha256'])

    def test_complete_report(self):
        check.validate_report(self.report())

    def test_missing_report_fields(self):
        for key in self.report():
            r=self.report(); del r[key]
            with self.assertRaises(SystemExit): check.validate_report(r)

    def test_unfinished_or_wrong_schema(self):
        for key,value in [('complete',False),('complete',1),('schema','other')]:
            r=self.report();r[key]=value
            with self.assertRaises(SystemExit):check.validate_report(r)

    def test_missing_extra_skipped_counts(self):
        for key,count in check.case_inventory()['counts'].items():
            for replacement in [count-1,count+1,True,None]:
                r=self.report();r[key]=replacement
                with self.assertRaises(SystemExit):check.validate_report(r)

    def test_exact_case_inventories(self):
        for key in ['pairs','source_refusals','auditor_refusals','late_failures']:
            actual=check.case_inventory()[key]
            check.require_cases(key,actual)
            for changed in [actual[:-1],actual+actual[:1],list(reversed(actual)) if len(actual)>1 else []]:
                with self.assertRaises(SystemExit):check.require_cases(key,changed)

    def test_wrong_model_or_auditor(self):
        for key in ['model_sha256','audit_sha256']:
            r=self.report();r[key]='f'*64
            with self.assertRaises(SystemExit):check.validate_report(r)

    def test_missing_or_changed_case_identity(self):
        r=self.report();r['cases']['auditor_refusals']=r['cases']['auditor_refusals'][:-1]
        with self.assertRaises(SystemExit):check.validate_report(r)

    def test_missing_input_and_bad_hash(self):
        r=self.report();r['inputs'].pop('riscv64_mix_and')
        with self.assertRaises(SystemExit):check.validate_report(r)
        r=self.report();r['inputs']['arm64_mix_and']['image_sha256']='bad'
        with self.assertRaises(SystemExit):check.validate_report(r)

    def test_architecture_source_disagreement(self):
        r=self.report();r['inputs']['riscv64_mix_and']['source_sha256']='3'*64
        with self.assertRaises(SystemExit):check.validate_report(r)

    def test_changed_valid_input_hashes_and_lengths(self):
        for key,value in [('image_sha256','0'*64),('source_sha256','0'*64),
                          ('image_length',True),('image_length',4648.0),('image_length',4647)]:
            r=self.report();r['inputs']['arm64_mix_and'][key]=value
            with self.assertRaises(SystemExit):check.validate_report(r)

    def test_fresh_generated_inputs_require_actual_bytes(self):
        with tempfile.TemporaryDirectory() as temp:
            directory=Path(temp)
            ident='arm64_test'
            image=b'\x01'+bytes(3976)+b'\x02'
            (directory/(ident+'.elf')).write_bytes(image)
            (directory/(ident+'.oak')).write_bytes(b'a')
            lines=['namespace '+ident,'def source : List UInt8 := [97]',
                   'def header : Bytes := [1]','def suffix : Bytes := [2]',
                   'def image : Bytes := header ++ (List.replicate 3976 0 ++ suffix)',
                   'end '+ident]
            check.require_current_inputs(lines,directory,{ident})
            for filename,changed in [(ident+'.elf',image[:-1]+b'\x03'),(ident+'.oak',b'b')]:
                path=directory/filename;original=path.read_bytes();path.write_bytes(changed)
                with self.assertRaises(SystemExit):check.require_current_inputs(lines,directory,{ident})
                path.write_bytes(original)
            with self.assertRaises(SystemExit):check.require_current_inputs([],directory,{ident})
            with self.assertRaises(SystemExit):check.require_current_inputs(lines+lines,directory,{ident})

    def test_source_predicates_are_pinned(self):
        roots=json.loads((check.ROOT/'tools/source_image_parity/expected-roots.json').read_text())
        for field,file in [('model_sha256','BitwiseSourceImageParity.lean'),('audit_sha256','BitwiseSourceImageParityAudit.lean')]:
            self.assertEqual(roots[field],check.sha((check.LEAN/'Oak'/file).read_bytes()))
        self.assertEqual(len(roots['model']),14)
        self.assertEqual(set(roots['model']),set(roots['statements']))

if __name__=='__main__':
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(GateControls)
    if suite.countTestCases()!=16:raise SystemExit('Changed required harness-test inventory')
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    if result.testsRun!=16 or result.skipped or not result.wasSuccessful():sys.exit(1)
