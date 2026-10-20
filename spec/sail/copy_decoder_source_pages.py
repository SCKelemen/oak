#!/usr/bin/env python3
"""Copy original source bytes into fixed-size octet pages, without clause parsing.
External-file acquisition and exact comparison are explicit non-kernel inputs.
This module deliberately does not import the inventory/certificate generator.
"""
import argparse
import hashlib
import ast
import re
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / 'spec/lean/Oak/ArmDecoderPartition'
PIN = '61a57876f4ac9b10849bf90bcd9bb74f6336737015cb3a5b1e1ebd85f11e6ae7'
PAGE_SIZE = 1024

def page_text(i, page):
    words = [int.from_bytes(page[j:j+128], 'little') for j in range(0,len(page),128)]
    return (f'def words{i} : List Nat := ' + repr(words) + '\n'
            + f'def page{i} : Bytes := (unpackBlocks 128 words{i}).take {len(page)}\n'
            + f'theorem size{i} : page{i}.length = {len(page)} := by\n  rw [page{i}, List.length_take, unpackBlocks_length]; rfl\n'
            + f'def input{i} : SizedBytes := ⟨page{i}, {len(page)}, size{i}⟩\n')

def decode_words(words, length):
    if len(words) != (length+127)//128: raise RuntimeError('packed word count')
    if any(type(v) is not int or v < 0 or v >= 256**128 for v in words):
        raise RuntimeError('packed word range')
    octets = b''.join(v.to_bytes(128,'little') for v in words)
    if any(octets[length:]): raise RuntimeError('noncanonical high octets')
    return octets[:length]

def check(source, generate=False):
    data = source.read_bytes()
    if hashlib.sha256(data).hexdigest() != PIN:
        raise RuntimeError('wrong original source pin')
    expected = {}
    pages = [data[j:j+PAGE_SIZE] for j in range(0,len(data),PAGE_SIZE)]
    for start in range(0,len(pages),16):
        text = ('import Oak.ArmDecoderPartition.Bytes\n\n'
                'namespace Oak.ArmDecoderPartition.Source\n')
        text += ''.join(page_text(i,pages[i]) for i in range(start,min(start+16,len(pages))))
        text += 'end Oak.ArmDecoderPartition.Source\n'
        expected[f'SourceBatch{start//16:03}.lean'] = text
    OUT.mkdir(parents=True, exist_ok=True)
    if generate:
        for stale in OUT.glob('Source*.lean'):
            if stale.name not in expected: stale.unlink()
        for name, text in expected.items():
            (OUT / name).write_text(text)
    if {p.name for p in OUT.glob('Source*.lean')} != set(expected):
        raise RuntimeError('missing or extra independent source page module')
    copied = bytearray()
    next_index = 0
    for name, text in expected.items():
        actual = (OUT / name).read_text()
        if actual != text:
            raise RuntimeError('independent exact-byte page mismatch: ' + name)
        # A second, direct octet round trip checks every copied natural literal.
        # It does not call the clause inventory or reconstruct any clause.
        for index, words_text in re.findall(r'^def words(\d+) : List Nat := (\[.*\])$', actual, re.M):
            index = int(index)
            if index != next_index: raise RuntimeError('independent page order')
            words = ast.literal_eval(words_text)
            length = len(pages[index])
            copied.extend(decode_words(words,length));next_index += 1
    if bytes(copied) != data: raise RuntimeError('original-file/literal octet mismatch')
    return data

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--source',type=pathlib.Path,required=True)
    p.add_argument('--generate',action='store_true')
    args=p.parse_args();data=check(args.source,args.generate)
    print(f'Independent original-file copy checked: {len(data)} bytes in fixed {PAGE_SIZE}-byte pages.')

if __name__=='__main__':main()
