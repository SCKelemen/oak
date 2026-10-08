#!/usr/bin/env python3
"""Reproduce a pinned Sail exporter defect, without patching generated bodies.
All emitted files and process logs are retained in --output-dir.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
parser = argparse.ArgumentParser()
parser.add_argument('--output-dir', type=Path, required=True)
args = parser.parse_args()
OUT = args.output_dir.resolve()
OUT.mkdir(parents=True, exist_ok=True)
SAIL = os.environ.get('SAIL', 'sail')
VERSION = 'Sail 0.20.2 (sail2 @ 3b7af38d66466ecadad563158b07ce2f82fe05da)'

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def run(argv, cwd, log):
    process = subprocess.run(argv, cwd=cwd, text=True, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, timeout=180)
    (OUT / log).write_text(process.stdout)
    require(process.returncode == 0, f'{argv[0]} failed; see {OUT / log}')
    return process.stdout

version = run([SAIL, '--version'], OUT, 'version.log').strip()
require(version == VERSION, f'unexpected Sail generator: {version}')
run(['lean', '--version'], ROOT / 'spec/sail/lean', 'lean-version.log')
commands = 'initialize_registers()\n:run\nmain()\n:run\n:quit\n'
(OUT / 'run.isail').write_text(commands)
manifest = {'sail_version': version, 'proof_toolchain': 'leanprover/lean4:v4.33.1',
            'support_revision': '79b4d08505af29d88b3918f32d29840fae1fa191',
            'support_patch': 'spec/sail/lean-sail-4.33.patch', 'files': {}}

# Two independent source executions, plus kernel-checking the unchanged exports.
for case, evidence in [('total', 'TotalEvidence.lean'), ('incomplete', 'IncompleteEvidence.lean')]:
    name = f'minimal_{case}.sail'
    shutil.copyfile(HERE / name, OUT / name)
    source_log = run([SAIL, name, '--is', 'run.isail'], OUT, f'{case}-source.log')
    require('repro(false,1) -> 55' in source_log and 'Error:' not in source_log,
            f'{case}: source evaluator did not produce 55')
    if case == 'total':
        require('Incomplete pattern match' not in source_log,
                'total reproducer unexpectedly has an incomplete match')
    generated = OUT / f'generated-{case}'
    generated.mkdir()
    run([SAIL, name, '--lean', '--lean-single-file', '--lean-output-dir', str(generated),
         '--lean-lib-path', str(ROOT.parent / 'external/lean-sail')], OUT, f'{case}-export.log')
    project = generated / 'out'
    # Change package metadata only, matching Oak's reviewed ARM proof toolchain.
    # The generated Lean source remains byte-for-byte compiler output.
    (project / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
    shutil.copyfile(HERE / evidence, project / 'Evidence.lean')
    run(['lake', 'update'], project, f'{case}-lake-update.log')
    run(['lake', 'build'], project, f'{case}-build.log')
    lean_log = run(['lake', 'env', 'lean', 'Evidence.lean'], project, f'{case}-lean.log')
    audit = 'does not depend on any axioms' if case == 'total' else 'depends on axioms: [propext, Quot.sound]'
    require(re.search(r'^63$', lean_log, re.M) is not None and audit in lean_log,
            f'{case}: unchanged generated result/kernel proof not confirmed')
    for path in [OUT / name, project / 'Out.lean', project / 'Out/Defs.lean']:
        manifest['files'][str(path.relative_to(OUT))] = sha(path.read_bytes())

# Intact original AddrTop declaration and body, under explicit EL1/A64/no-PAC fixture.
model = ROOT / 'external/sail-arm/arm-v8.5-a/model/aarch_mem.sail'
original = model.read_bytes()
require(sha(original) == '5764f0a9282825f63edf30b5fd50811ae5c85ab2a3f6104334e00d26cf6d5592',
        'pinned aarch_mem.sail mismatch')
source = original.decode()
def declaration(kind, name):
    starts = list(re.finditer(r'^' + kind + ' ' + re.escape(name) + r'(?=[\s:(=])', source, re.M))
    require(len(starts) == 1, f'nonunique declaration {name}')
    rest = source[starts[0].start():]
    end = re.search(r'\n(?:val|function|register|type|enum|struct|overload|let|union) ', rest[1:])
    require(end is not None, f'unterminated declaration {name}')
    return rest[:end.start() + 1].strip() + '\n\n'
license_text = source[:source.index('\nval ', source.index('/**************************************************************************/', 5))]
fixture = license_text + '\n' + '''default Order dec
$include <flow.sail>
$include <vector.sail>
$include <arith.sail>
$include <string.sail>
overload ~ = {not_bool, not_vec}
'''
for name in ['TCR_EL1', 'TCR_EL2', 'TCR_EL3']:
    fixture += declaration('register', name)
for name in ['EL1', 'EL2', 'EL3']:
    fixture += declaration('let', name)
fixture += '''val HaveEL : bits(2) -> bool
function HaveEL(el) = true
val S1TranslationRegime : bits(2) -> bits(2)
function S1TranslationRegime(el) = 0b01
val ELUsingAArch32 : bits(2) -> bool
function ELUsingAArch32(el) = false
val HavePACExt : unit -> bool
function HavePACExt() = false
val HaveVirtHostExt : unit -> bool
function HaveVirtHostExt() = false
val ELIsInHost : bits(2) -> bool
function ELIsInHost(el) = false
'''
for kind in ['val', 'function']:
    text = declaration(kind, 'AddrTop')
    fixture += text
    manifest[f'original_AddrTop_{kind}_sha256'] = sha(text.encode())
fixture += '''val observe : bits(64) -> int
function observe(tcr) = {
 TCR_EL1 = tcr;
 AddrTop(0x0000000000000000, true, 0b01)
}
val main : unit -> unit
function main() = {
 print_int("TBI0=0 -> ", observe(0x0000000000000000));
 print_int("TBI0=1 -> ", observe(0x0000002000000000))
}
'''
(OUT / 'original_addr_top.sail').write_text(fixture)
addr_log = run([SAIL, 'original_addr_top.sail', '--is', 'run.isail'], OUT, 'addr-top-source.log')
require('TBI0=0 -> 63' in addr_log and 'TBI0=1 -> 55' in addr_log and 'Error:' not in addr_log,
        'original AddrTop source evaluator results changed')
generated = OUT / 'generated-addr-top'
generated.mkdir()
run([SAIL, 'original_addr_top.sail', '--lean', '--lean-single-file', '--lean-output-dir', str(generated),
     '--lean-lib-path', str(ROOT.parent / 'external/lean-sail')], OUT, 'addr-top-export.log')
# Preserve the separate raw-full-fixture elaboration limitation; do not patch
# unused binders to manufacture a runtime result for the intact AddrTop export.
project = generated / 'out'
(project / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
run(['lake', 'update'], project, 'addr-top-lake-update.log')
failed_build = subprocess.run(['lake', 'build'], cwd=project, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
(OUT / 'addr-top-build.log').write_text(failed_build.stdout)
require(failed_build.returncode != 0 and 'Application type mismatch' in failed_build.stdout,
        'intact AddrTop raw elaboration behavior changed; re-audit before updating expected evidence')
manifest['addr_top_raw_build'] = 'fails elaboration; no executable raw AddrTop result claimed'
for path in [OUT / 'original_addr_top.sail', generated / 'out/Out.lean', generated / 'out/Out/Defs.lean']:
    manifest['files'][str(path.relative_to(OUT))] = sha(path.read_bytes())

# Focused impact audit: original reviewed scalar/RET source, with explicit fixture
# queries and a BranchTo request recorder (not a hardware return implementation).
fragment = (ROOT / 'spec/sail/scalar_execution.sail').read_text()
manifest['reviewed_scalar_source_sha256'] = sha(fragment.encode())
# The source fragment's compatibility equality adapter originally names only its
# Lean backend. Bind the same generic equality to Sail's interpreter primitive.
fragment = fragment.replace('lean: "_lean_beq"', 'lean: "_lean_beq", interpreter: "eq_anything"')
shutil.copyfile(ROOT / 'spec/sail/scalar_execution_vector.sail', OUT / 'scalar_execution_vector.sail')
fragment += '''
function HaveBTIExt() = false
function UsingAArch32() = false
function HavePACExt() = false
register AuditReturn : bits(64)
register AuditBranchKind : BranchType
function BranchTo(target, branch_type) = {
 AuditReturn = ZeroExtend(target,64);
 AuditBranchKind = branch_type
}
val main : unit -> unit
function main() = {
'''
expected = []
for i, (a, b) in enumerate([(0, 0), (0xffffffffffffffff, 0), (0xffffffffffffffff, 0xffffffff),
                            (0xdeadbeef80000000, 0xfeedface7fffffff),
                            (0x1234567887654321, 0xfedcba98a5a55a5a)]):
    for op, word in [('and', 0x0a010000), ('or', 0x2a010000), ('xor', 0x4a010000)]:
        x, y = a & 0xffffffff, b & 0xffffffff
        result = {'and': x & y, 'or': x | y, 'xor': x ^ y}[op]
        expected.append(f'case{i}-{op} -> {result}')
        fragment += f''' _R[0] = 0x{a:016x};
 _R[1] = 0x{b:016x};
 _R[30] = 0x0000000012345678;
 SEE = -1;
 decode64(0x{word:08x});
 assert(_R[0] == 0x{result:016x});
 assert(_R[1] == 0x{b:016x});
 SEE = -1;
 decode64(0xd65f03c0);
 assert(AuditReturn == 0x0000000012345678);
 assert(AuditBranchKind == BranchType_RET);
 assert(BTypeNext == 0b00);
 print_int("case{i}-{op} -> ", UInt(_R[0]));
'''
fragment += ' ()\n}\n'
(OUT / 'selected.sail').write_text(fragment)
selected_log = run([SAIL, 'selected.sail', '--is', 'run.isail'], OUT, 'selected-source.log')
require(all(line in selected_log for line in expected) and 'Error:' not in selected_log,
        'selected scalar/RET source audit failed')
manifest['selected_fixture_sha256'] = sha(fragment.encode())
manifest['selected_results'] = expected
expected_manifest = json.loads((HERE / 'evidence/manifest.json').read_text())
require(manifest == expected_manifest, 'pinned evidence manifest changed; review before updating')
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print('Confirmed: total and incomplete source55 versus unchanged exported Lean63.')
print('Confirmed: original AddrTop source63/55 for TBI0 disabled/enabled.')
print('Confirmed: 15 selected scalar/RET source cases; no broader equivalence claimed.')
print(f'Artifacts: {OUT}')
