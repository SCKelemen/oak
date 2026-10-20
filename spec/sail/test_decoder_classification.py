#!/usr/bin/env python3
"""Negative controls for the explicitly trusted whole-file extractor."""
import pathlib
import unittest
import decoder_classification as d

class ExtractionControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw=d.SOURCE.read_bytes();cls.prefix,cls.clauses,cls.gaps=d.inventory(cls.raw)
    def assemble(self,clauses):
        return (self.prefix+''.join(c['raw']+'\n' for c in clauses)).encode()
    def rejected(self,data):
        with self.assertRaises(RuntimeError):d.inventory(data)
    def test_original_exact_reconstruction(self):
        self.assertEqual(d.digest(self.raw),d.PIN)
        self.assertEqual(self.prefix+''.join(''.join(c['chunks'])+g for c,g in zip(self.clauses,self.gaps)),self.raw.decode())
    def test_missing_clause(self):self.rejected(self.assemble(self.clauses[1:]))
    def test_extra_duplicate_clause(self):self.rejected(self.assemble(self.clauses+[self.clauses[0]]))
    def test_duplicate_replaces_clause(self):self.rejected(self.assemble([self.clauses[1]]+self.clauses[1:]))
    def test_reordered_clauses(self):self.rejected(self.assemble([self.clauses[1],self.clauses[0]]+self.clauses[2:]))
    def test_guard_operator(self):self.rejected(self.raw.replace(b'if SEE < 1026',b'if SEE <= 1026',1))
    def test_guard_index(self):self.rejected(self.raw.replace(b'if SEE < 1026',b'if SEE < 1027',1))
    def test_width(self):self.rejected(self.raw.replace(b'0b10011011001 @ _ : bits(5)',b'0b10011011001 @ _ : bits(6)',1))
    def test_unknown_region_comment(self):self.rejected(self.raw.replace(b'function clause decode64 ',b'/* hidden text */\nfunction clause decode64 ',1))
    def test_skipped_region_text(self):self.rejected(self.raw+b'let hidden = 1\n')
    def test_string_in_region(self):self.rejected(self.raw+b'"function clause decode64 fake"\n')
    def test_multiline_header(self):self.rejected(self.raw.replace(b'function clause decode64 ',b'function clause\ndecode64 ',1))
    def test_prefix_hidden_declaration(self):self.rejected(b'/* function clause decode64 fake */\n'+self.raw)
    def test_arg_order(self):
        raw=self.clauses[0]['raw'];changed=raw.replace('Rd, Rn','Rn, Rd')
        self.assertNotEqual(raw,changed)
        with self.assertRaises(RuntimeError):d.parse_clause(changed)
    def test_callee_change_is_not_pinned(self):
        changed=self.raw.replace(b'integer_logical_shiftedreg_decode(',b'other_decode(',1)
        self.assertNotEqual(d.digest(changed),d.PIN)

if __name__=='__main__':unittest.main()
