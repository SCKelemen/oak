#!/usr/bin/env python3
"""Failure controls for the separate external-file/literal acquisition boundary."""
import pathlib
import json
import tempfile
import unittest
from unittest.mock import patch
import copy_decoder_source_pages as copy
import decoder_partition as partition
import check_decoder_partition as replay

SOURCE=pathlib.Path(__file__).resolve().parent/'decoder_classification_source.sail'

class CopyControls(unittest.TestCase):
    def test_exact_all_original_bytes(self):
        with tempfile.TemporaryDirectory() as d,patch.object(copy,'OUT',pathlib.Path(d)):
            self.assertEqual(copy.check(SOURCE,True),SOURCE.read_bytes())
    def mutate(self,action):
        with tempfile.TemporaryDirectory() as d,patch.object(copy,'OUT',pathlib.Path(d)):
            copy.check(SOURCE,True);action(pathlib.Path(d))
            with self.assertRaises(RuntimeError):copy.check(SOURCE)
    def test_missing_page(self):self.mutate(lambda d:(d/'SourceBatch001.lean').unlink())
    def test_extra_page(self):self.mutate(lambda d:(d/'SourceBatch999.lean').write_text('extra'))
    def test_duplicate_page(self):self.mutate(lambda d:(d/'SourceBatch001.lean').write_bytes((d/'SourceBatch000.lean').read_bytes()))
    def test_changed_literal(self):
        def change(d):
            p=d/'SourceBatch000.lean';p.write_text(p.read_text().replace('List Nat := [','List Nat := [0, ',1))
        self.mutate(change)
    def test_reordered_pages(self):
        def change(d):
            a=d/'SourceBatch000.lean';b=d/'SourceBatch001.lean';x=a.read_bytes();a.write_bytes(b.read_bytes());b.write_bytes(x)
        self.mutate(change)
    def test_packed_range(self):
        for words,n in [([-1],1),([256**128],128),([True],1),([],1),([1,2],1),([256],1)]:
            with self.assertRaises(RuntimeError):copy.decode_words(words,n)
    def test_literal_byte_identity(self):
        self.assertEqual(copy.decode_words([16961],2),b'AB')
        self.assertNotEqual(copy.decode_words([16960],2),b'AB')
    def test_complete_inventory_lengths(self):
        pre,clauses,pages,parts,pre_cells=partition.inventory(SOURCE.read_bytes())
        self.assertEqual(len(pre),400975)
        self.assertEqual(len(clauses),917)
        self.assertEqual(sum(len(''.join(c['chunks'])) for c in clauses),431483)
        self.assertEqual(sum(b-a for pc in pages.values() for _,a,b in pc),833374)
        self.assertEqual(sum(name=='lf' for pc in pages.values() for name,_,_ in pc),916)
        self.assertEqual(sorted(parts),list(range(1026,1943)))
    def test_independent_copy_has_no_inventory_import(self):
        self.assertNotIn('import decoder_classification',pathlib.Path(copy.__file__).read_text())
        self.assertNotIn('import decoder_partition',pathlib.Path(copy.__file__).read_text())

class ReceiptControls(unittest.TestCase):
    def fixture(self,root):
        lean=root/'lean';old=root/'old';base=lean/'Oak/ArmDecoderClassification';base.mkdir(parents=True)
        obj=old/'Oak/ArmDecoderClassification';obj.mkdir(parents=True)
        sources={'Checker':'','Batch000':'import Oak.ArmDecoderClassification.Checker\n',
                 'Selection':'import Oak.ArmDecoderClassification.Batch000\n',
                 'Controls':'import Oak.ArmDecoderClassification.Checker\n'}
        for name,text in sources.items():
            (base/(name+'.lean')).write_text(text);(obj/(name+'.olean')).write_text('checked '+name)
        (lean/'Oak/Core.lean').write_text('');(old/'Oak/Core.olean').write_text('core')
        bridge=base/'ByteBinding.lean';bridge.write_text('import Oak.ArmDecoderClassification.Selection\nimport Oak.Core\n')
        (obj/'ByteBinding.olean').write_text('bridge')
        receipts={}
        for name in sources:
            source=base/(name+'.lean');deps=replay.dependencies(source)
            receipts[name]={'identity':{'source_sha256':replay.sha(source),'lean':'test',
                'dependencies':{n.rsplit('.',1)[1]:replay.sha(p) for n,p in deps.items()}},
                'olean_sha256':replay.sha(obj/(name+'.olean')),'measurement':{'exit':0,'reason':'exited'}}
        summary={'lean':'test','sources':{n+'.lean':replay.sha(base/(n+'.lean')) for n in sources},'receipts':receipts}
        byte={'source_sha256':replay.sha(bridge),'olean_sha256':replay.sha(obj/'ByteBinding.olean'),
              'core':{'Oak.Core':{'source':replay.sha(lean/'Oak/Core.lean'),'olean':replay.sha(old/'Oak/Core.olean')}}}
        (old/'validated.json').write_text(json.dumps(summary));(old/'byte-binding.json').write_text(json.dumps(byte))
        return old,summary,byte
    def check_fixture(self,mutation=None):
        with tempfile.TemporaryDirectory() as d:
            root=pathlib.Path(d)
            with patch.object(replay,'LEAN',root/'lean'):
                old,summary,byte=self.fixture(root)
                replay.validate_classifier(old,'test')
                if mutation:
                    mutation(root,summary,byte)
                    (old/'validated.json').write_text(json.dumps(summary));(old/'byte-binding.json').write_text(json.dumps(byte))
                    with self.assertRaises((RuntimeError,FileNotFoundError)):replay.validate_classifier(old,'test')
    def test_complete_receipt_graph(self):self.check_fixture()
    def test_missing_source_receipt(self):self.check_fixture(lambda r,s,b:s['sources'].pop('Batch000.lean'))
    def test_missing_module_receipt(self):self.check_fixture(lambda r,s,b:s['receipts'].pop('Batch000'))
    def test_extra_module_receipt(self):self.check_fixture(lambda r,s,b:s['receipts'].update(Extra=s['receipts']['Checker']))
    def test_failed_module(self):self.check_fixture(lambda r,s,b:s['receipts']['Batch000']['measurement'].update(exit=1))
    def test_incomplete_module(self):self.check_fixture(lambda r,s,b:s['receipts']['Batch000']['measurement'].update(reason='resource ceiling'))
    def test_missing_dependency(self):self.check_fixture(lambda r,s,b:s['receipts']['Batch000']['identity'].update(dependencies={}))
    def test_changed_object(self):self.check_fixture(lambda r,s,b:(r/'old/Oak/ArmDecoderClassification/Batch000.olean').write_text('changed'))
    def test_missing_core(self):self.check_fixture(lambda r,s,b:b.update(core={}))
    def test_extra_core(self):self.check_fixture(lambda r,s,b:b['core'].update(Extra=b['core']['Oak.Core']))
    def test_changed_core(self):self.check_fixture(lambda r,s,b:(r/'old/Oak/Core.olean').write_text('changed'))
    def test_receipt_recheck_rejects_drift(self):
        with tempfile.TemporaryDirectory() as d:
            root=pathlib.Path(d);source=root/'Module.lean';source.write_text('')
            out=root/'Oak/ArmDecoderPartition';out.mkdir(parents=True);(out/'Module.olean').write_text('checked')
            receipt={'identity':replay.module_identity(source,root,'test'),'olean':replay.sha(out/'Module.olean'),'measurement':{'exit':0,'reason':'exited'}}
            replay.verify_receipt(source,root,'test',receipt)
            source.write_text('changed')
            with self.assertRaises(RuntimeError):replay.verify_receipt(source,root,'test',receipt)

if __name__=='__main__':unittest.main()
