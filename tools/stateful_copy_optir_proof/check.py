#!/usr/bin/env python3
"""Fresh actual-raw-CFG proof gate; source/export correspondence is tested.

The Go equipped test regenerates the module from the ordinary package Check
and the owned raw artifact. This script independently checks field-for-field
JSON -> Lean reification, then overrides the committed development snapshot
with that fresh module in a trust-zero isolated build. A stale snapshot cannot
satisfy the equipped test merely because its old proof still builds.
"""
import argparse
import copy
import subprocess
import hashlib
import json
import os
import re
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
from wasm_module_proof.check import audit_reports, dependency_order, run
from stateful_copy_proof.check import check_bindings

SOURCE = ROOT / 'spec' / 'lean'
GENERATED = 'Oak.OptIRStatefulCopyGenerated'
VALIDATION = 'Oak.OptIRStatefulCopyValidation'
MODULE = 'Oak.OptIRStatefulCopyControls'
THEOREMS = (
    'Oak.OptIRExecution.Env.set_same',
    'Oak.OptIRExecution.Env.set_other',
    'Oak.OptIRExecution.writeByte_same',
    'Oak.OptIRExecution.writeByte_other',
    'Oak.OptIRExecution.represented_live',
    'Oak.OptIRExecution.byte_read_refines',
    'Oak.OptIRExecution.byte_store_refines',
    'Oak.OptIRExecution.result_value_exact',
    'Oak.OptIRExecution.run_more',
    'Oak.OptIRExecution.advance_run',
    'Oak.OptIRExecution.advance_add',
    'Oak.OptIRStatefulCopy.one_toNat',
    'Oak.OptIRStatefulCopy.zero_toNat',
    'Oak.OptIRStatefulCopy.iteration_header',
    'Oak.OptIRStatefulCopy.iteration',
    'Oak.OptIRStatefulCopy.loop_exit',
    'Oak.OptIRStatefulCopy.writeByte_writeWindow',
    'Oak.OptIRStatefulCopy.source_read_writeWindow',
    'Oak.OptIRStatefulCopy.destination_store_writeWindow',
    'Oak.OptIRStatefulCopy.toUInt32_toNat',
    'Oak.OptIRStatefulCopy.loop_refines_extracted',
    'Oak.OptIRStatefulCopy.enter_callee',
    'Oak.OptIRStatefulCopy.success_entry',
    'Oak.OptIRStatefulCopy.short_entry',
    'Oak.OptIRStatefulCopy.callee_return',
    'Oak.OptIRStatefulCopy.copy_cfg_prefix',
    'Oak.OptIRStatefulCopy.find_callee',
    'Oak.OptIRStatefulCopy.find_caller',
    'Oak.OptIRStatefulCopy.copy_cfg_refines_extracted',
    'Oak.OptIRStatefulCopy.copy_cfg_fuel',
    'Oak.OptIRStatefulCopy.enter_caller',
    'Oak.OptIRStatefulCopy.caller_call',
    'Oak.OptIRStatefulCopy.call_returns',
    'Oak.OptIRStatefulCopy.caller_finish',
    'Oak.OptIRStatefulCopy.caller_cfg_fuel',
    'Oak.OptIRStatefulCopy.caller_cfg_refines_extracted',
    'Oak.OptIRStatefulCopy.caller_cfg_total_observes',
    'Oak.OptIRStatefulCopy.generated_projection_accepted',
    'Oak.OptIRStatefulCopy.check_projection_sound',
    'Oak.OptIRStatefulCopy.accepted_caller_cfg_total_observes',
    'Oak.OptIRStatefulCopy.copy_cfg_short',
    'Oak.OptIRStatefulCopy.caller_cfg_short',
    'Oak.OptIRStatefulCopy.copy_cfg_empty',
    'Oak.OptIRStatefulCopy.caller_cfg_empty',
    'Oak.OptIRStatefulCopy.caller_zero_fuel',
    'Oak.OptIRStatefulCopy.projection_closed_functions',
    'Oak.OptIRStatefulCopy.caller_cfg_total_observes_with_fuel',
    'Oak.OptIRStatefulCopy.Controls.inhabited_windows',
    'Oak.OptIRStatefulCopy.Controls.same_owner_window_frame',
    'Oak.OptIRStatefulCopy.Controls.short_case',
    'Oak.OptIRStatefulCopy.Controls.one_past_empty_case',
    'Oak.OptIRStatefulCopy.Controls.exhausted_not_error',
    'Oak.OptIRStatefulCopy.Controls.missing_closure_refused',
    'Oak.OptIRStatefulCopy.Controls.inactive_payload_fault',
    'Oak.OptIRStatefulCopy.Controls.unmapped_byte_fault',
    'Oak.OptIRStatefulCopy.Controls.unmapped_store_fault',
)


def quote(text):
    return json.dumps(text, ensure_ascii=False)


def seq(items, render):
    return '[' + ', '.join(render(item) for item in (items or [])) + ']'


def record(fields):
    return '{ ' + ', '.join(name + ' := ' + value for name, value in fields) + ' }'


def source(s):
    return record([('context', quote(s['Context'])), ('line', str(s['Line'])), ('column', str(s['Column']))])


def value(v):
    return record([('id', str(v['ID'])), ('ty', quote(v['Type'])), ('name', quote(v['Name'])), ('source', source(v['Source']))])


def attribute(a):
    return record([('name', quote(a['Name'])), ('value', quote(a['Value']))])


def fact(f):
    return record([('id', quote(f['ID'])), ('name', quote(f['Name'])), ('values', seq(f['Values'], str)),
                   ('provenance', quote(f['Provenance'])), ('witness', quote(f['Witness'])),
                   ('scope', quote(f['Scope'])), ('dependencies', seq(f['Dependencies'], quote))])


def operation(o):
    return record([('code', quote(o['Code'])), ('results', seq(o['Results'], value)),
                   ('operands', seq(o['Operands'], str)), ('effects', seq(o['Effects'], quote)),
                   ('attributes', seq(o['Attributes'], attribute)), ('facts', seq(o['Facts'], fact)),
                   ('source', source(o['Source'])), ('memoryAccessID', quote(o['MemoryAccessID'])),
                   ('memoryCallID', quote(o['MemoryCallID']))])


def edge(e):
    return record([('target', str(e['Target'])), ('arguments', seq(e['Arguments'], str))])


def terminator(t):
    return record([('kind', quote(t['Kind'])), ('condition', str(t['Condition'])),
                   ('trueEdge', edge(t['True'])), ('falseEdge', edge(t['False'])), ('values', seq(t['Values'], str))])


def block(b):
    return record([('id', str(b['ID'])), ('parameters', seq(b['Parameters'], value)),
                   ('operations', seq(b['Operations'], operation)), ('terminator', terminator(b['Terminator']))])


def cfg(c):
    return record([('name', quote(c['Name'])), ('entry', str(c['Entry'])), ('results', seq(c['Results'], quote)),
                   ('blocks', seq(c['Blocks'], block)), ('facts', seq(c['Facts'], fact))])


def reification_envelope(export):
    prefix = '-- Generated from Compilation.Check + StatefulCopyOptIR. Do not hand edit.\nimport Oak.OptIRExecution\n\nnamespace Oak.OptIRStatefulCopy.Generated\nopen Oak.OptIRExecution\n\ndef program : Program := [\n'
    prefix += ',\n'.join(cfg(f['CFG']) for f in export['Functions'])
    prefix += '\n]\n\n-- Exact custody data, not a proof callback or acceptance hash.\ndef custodyJSON : String := '
    suffix = '\n\nend Oak.OptIRStatefulCopy.Generated\n'
    return prefix, suffix


def render_export(export):
    prefix, suffix = reification_envelope(export)
    return prefix + quote(json.dumps(export, ensure_ascii=False, separators=(',', ':'))) + suffix


def validate_export(generated_text, export):
    if export['Profile'] != 'oak.optir.stateful-copy.raw.v1' or export['Root'] != 'copy_checked':
        raise ValueError('wrong raw profile/root')
    if [f['CFG']['Name'] for f in export['Functions']] != ['bytes__copy_uinto', 'copy_checked']:
        raise ValueError('wrong executable closure')
    prefix, suffix = reification_envelope(export)
    if not generated_text.startswith(prefix) or not generated_text.endswith(suffix):
        raise ValueError('Lean reification omits/changes a raw CFG field')
    custody_literal = generated_text[len(prefix):-len(suffix)]
    if json.loads(json.loads(custody_literal)) != export:
        raise ValueError('Lean custody data differs from full exported artifact')
    sources = export['Sources']
    if len(sources) != 3:
        raise ValueError('wrong dependency source inventory')
    expected = [ROOT / 'stdlib/bytes.oak', ROOT / 'compiler/testdata/stateful_copy/main.oak', ROOT / 'stdlib/std.oak']
    if sources[0]['Package'] != 'bytes' or sources[2]['Package'] != 'std' or sources[2]['Path'] != 'stdlib.oak':
        raise ValueError('wrong dependency package identities')
    for entry, path in zip(sources, expected):
        if entry['Text'] != path.read_text():
            raise ValueError('export dependency bytes differ: ' + str(path))
    root_file = Path(sources[1]['Path'])
    if not root_file.is_absolute() or root_file.read_text() != sources[1]['Text']:
        raise ValueError('export root bytes differ from the ordinary package file')
    return root_file


def semantic_mutations(export):
    # These mutate freshly generated ordinary operations/edges, not a fake copy
    # evaluator. The same kernel translation validator must reject each graph.
    changes = (
        ('increment-two', lambda x: x['Functions'][0]['CFG']['Blocks'][5]['Operations'][2]['Attributes'][0].update(Value='2')),
        ('short-guard-reversed', lambda x: x['Functions'][0]['CFG']['Blocks'][0]['Terminator'].update({'True':copy.deepcopy(x['Functions'][0]['CFG']['Blocks'][0]['Terminator']['False']), 'False':copy.deepcopy(x['Functions'][0]['CFG']['Blocks'][0]['Terminator']['True'])})),
        ('loop-condition', lambda x: x['Functions'][0]['CFG']['Blocks'][4]['Operations'][0].update(Code='compare.equal')),
        ('store-before-load', lambda x: x['Functions'][0]['CFG']['Blocks'][5]['Operations'].__setitem__(slice(0,2), list(reversed(x['Functions'][0]['CFG']['Blocks'][5]['Operations'][:2])))),
        ('loop-backedge', lambda x: x['Functions'][0]['CFG']['Blocks'][5]['Terminator']['True'].update(Arguments=[8])),
        ('result-count', lambda x: x['Functions'][0]['CFG']['Blocks'][6]['Operations'][0].update(Operands=[4])),
        ('call-target', lambda x: x['Functions'][1]['CFG']['Blocks'][0]['Operations'][1]['Attributes'][0].update(Value='copy_checked')),
        ('caller-live-value', lambda x: x['Functions'][1]['CFG']['Blocks'][1]['Operations'][1].update(Operands=[6,6])),
        ('nested-error', lambda x: x['Functions'][0]['CFG']['Blocks'][1]['Operations'][0]['Attributes'][0].update(Value='bytes__CopyError.Invalid')),
    )
    for name, change in changes:
        changed = copy.deepcopy(export)
        change(changed)
        yield name, changed


def acceptance_lines(text):
    """Locate the one actual-validator acceptance theorem, not an alternate check."""
    lines = text.splitlines()
    starts = [i for i, line in enumerate(lines) if line.startswith('theorem generated_projection_accepted')]
    if len(starts) != 1:
        raise ValueError('validator must have one named generated acceptance theorem')
    start = starts[0]
    end = next((i for i in range(start + 1, len(lines))
                if re.match(r'^(?:theorem|def|end)\b', lines[i])), len(lines))
    return set(range(start + 1, end + 1))


def require_validator_refusal(diagnostics, returncode, expected_lines):
    if returncode != 1:
        raise RuntimeError('mutation did not end with the Lean error exit code 1: ' + str(returncode))
    if any(message in diagnostics.lower() for message in (
            'unknown module prefix', 'object file', 'failed to open file',
            'maximum memory', 'interrupted', 'heartbeat', 'maxrecdepth',
            'maximum recursion', 'deep recursion', 'out of memory', 'timeout',
            'time limit', 'deterministic timeout')):
        raise RuntimeError('mutation refusal was a resource/import failure: ' + diagnostics)
    errors = re.findall(r'OptIRStatefulCopyValidation\.lean:(\d+):\d+: error:', diagnostics)
    if not errors or any(int(line) not in expected_lines for line in errors):
        raise RuntimeError('mutation did not fail the exact validator acceptance theorem: ' + diagnostics)
    if diagnostics.count('error:') != len(errors) or 'decide' not in diagnostics or 'false' not in diagnostics:
        raise RuntimeError('mutation was not a decidable false acceptance verdict: ' + diagnostics)


def require_semantic_mutations_rejected(lean, build, env, export):
    output = build / 'Oak/OptIRStatefulCopyGenerated.olean'
    validation = SOURCE / 'Oak/OptIRStatefulCopyValidation.lean'
    expected_lines = acceptance_lines(validation.read_text())
    # Recheck the same positive acceptance theorem before trying changed inputs.
    # The complete arbitrary-Invocation refinement has already checked this graph.
    command = [str(lean), '-j1', '-t0', '-M1600', '-R', str(SOURCE), str(validation)]
    log = run(command, cwd=SOURCE, env=env)
    if log.strip():
        raise RuntimeError('fresh actual CFG did not satisfy checkProjection: ' + log)
    for name, changed in semantic_mutations(export):
        mutation_root = build / 'mutations' / name
        path = mutation_root / 'Oak/OptIRStatefulCopyGenerated.lean'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(render_export(changed))
        # Reification remains lossless even for a semantically wrong candidate.
        validate_export(path.read_text(), changed)
        log = run([str(lean), '-j1', '-t0', '-M1600', '-R', str(mutation_root), '-o', str(output), str(path)], cwd=SOURCE, env=env)
        if log.strip():
            raise RuntimeError('mutation fixture failed to typecheck: ' + name + ': ' + log)
        result = subprocess.run(command, cwd=SOURCE, env=env, text=True, capture_output=True, timeout=90)
        diagnostics = result.stdout + result.stderr
        try:
            require_validator_refusal(diagnostics, result.returncode, expected_lines)
        except RuntimeError as exc:
            raise RuntimeError(name + ': ' + str(exc)) from exc
        first_error = next(line for line in diagnostics.splitlines() if 'error:' in line)
        print('checkProjection rejected actual CFG mutation ' + name + ': ' + first_error, flush=True)


def audit_source():
    if not THEOREMS:
        raise ValueError('raw-CFG theorem inventory is not frozen')
    return 'import ' + MODULE + '\nset_option format.width 100000\n' + ''.join('#print axioms ' + name + '\n' for name in THEOREMS)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--generated', required=True, type=Path)
    parser.add_argument('--export-json', required=True, type=Path)
    args = parser.parse_args()
    check_bindings()
    generated = args.generated.resolve()
    exported = args.export_json.resolve()
    export = json.loads(exported.read_text())
    root_file = validate_export(generated.read_text(), export)
    prefix = run([args.lake, 'env', 'lean', '--print-prefix'], cwd=SOURCE).strip().splitlines()[-1]
    if not Path(prefix).is_absolute():
        raise RuntimeError('lake returned a nonabsolute installation prefix')
    lean = Path(prefix) / 'bin/lean'
    version = run([str(lean), '--version']).strip()
    if not version.startswith('Lean (version 4.33.1,'):
        raise RuntimeError('raw-CFG gate requires Lean4.33.1: ' + version)
    audit_path = SOURCE / 'Oak/OptIRStatefulCopyAudit.lean'
    if audit_path.read_text() != audit_source():
        raise RuntimeError('raw-CFG committed audit differs from exact public inventory')
    order = dependency_order(MODULE, SOURCE)
    if not {GENERATED, VALIDATION}.issubset(name for name, _ in order):
        raise RuntimeError('proof does not import actual generated CFG and validator')
    order = [(name, generated if name == GENERATED else path) for name, path in order]
    paths = [path for _, path in order] + [exported, root_file, audit_path, Path(__file__).resolve(), Path(__file__).with_name('test_check.py').resolve()]
    paths += [ROOT / p for p in ('compiler/optir.go', 'compiler/optir_stateful.go', 'compiler/optir_stateful_export.go', 'compiler/optir_stateful_proof_test.go', 'compiler/modules.go', 'optir/ir.go', 'optir/project.go', 'optir/stateful_profile.go', 'optir/stateful_execution.go')]
    identities = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}
    print('fresh generated module sha256 ' + identities[str(generated)], flush=True)
    print('fresh exported custody sha256 ' + identities[str(exported)], flush=True)
    with tempfile.TemporaryDirectory(prefix='oak-stateful-raw-proof-') as tmp:
        build = Path(tmp)
        env = dict(os.environ, LEAN_PATH=str(build), LEAN_NUM_THREADS='1')
        generated_root = build / 'source'
        generated_copy = generated_root / 'Oak/OptIRStatefulCopyGenerated.lean'
        generated_copy.parent.mkdir(parents=True, exist_ok=True)
        generated_copy.write_bytes(generated.read_bytes())
        for name, path in order:
            output = build.joinpath(*name.split('.')).with_suffix('.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            compile_root = generated_root if name == GENERATED else SOURCE
            compile_path = generated_copy if name == GENERATED else path
            log = run([str(lean), '-j1', '-t0', '-M1600', '-R', str(compile_root), '-o', str(output), str(compile_path)], cwd=SOURCE, env=env)
            if log.strip():
                raise RuntimeError('unexpected Lean diagnostics: ' + log)
            print('kernel checked ' + name, flush=True)
        audit = build / 'RawCopyAudit.lean'
        audit.write_text(audit_source())
        log = run([str(lean), '-j1', '-t0', '-M1600', '-R', str(build), str(audit)], cwd=SOURCE, env=env)
        audit_reports(log, THEOREMS)
        print(log, end='', flush=True)
        require_semantic_mutations_rejected(lean, build, env, export)
    check_bindings()
    for path, digest in identities.items():
        if hashlib.sha256(Path(path).read_bytes()).hexdigest() != digest:
            raise RuntimeError('input changed during raw-CFG proof: ' + path)
    print(f'fresh actual raw CFG: {len(order)} trust-zero modules; {len(THEOREMS)} exact public roots; source/export trust boundary retained', flush=True)


if __name__ == '__main__':
    main()
