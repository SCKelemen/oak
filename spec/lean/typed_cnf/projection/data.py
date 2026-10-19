"""Exact typed literal factoring; Word/root/context declarations stay verbatim."""
import hashlib
import re

BLOCK = 128
PER_MODULE = 4
MAX_BYTES = 8 * 1024 * 1024
UNCHANGED = ['Checks.lean'] + ['Nodes%02d.lean' % i for i in range(15)] + ['Final.lean']
from common import require

ctx = None

def refuse(message):
    raise ValueError(message)

def charge(amount=1):
    ctx.charge(amount)

def digest(raw):
    charge(len(raw))
    return hashlib.sha256(raw).hexdigest()

def split_top(text):
    """Split commas only outside matched delimiters and quoted strings.

    This is a deliberately restricted lexical reader for the pinned literal
    source, not a general Lean parser. Comments and excessive nesting refuse.
    """
    charge(len(text))
    pairs = {']': '[', ')': '(', '⟩': '⟨', '}': '{'}
    stack = []
    quoted = escaped = False
    result = []
    start = 0
    for index, character in enumerate(text):
        if quoted:
            if escaped:
                escaped = False
            elif character == '\\':
                escaped = True
            elif character == '"':
                quoted = False
            continue
        if character == '"':
            quoted = True
        elif text[index:index + 2] in ('--', '/-', '-/'):
            refuse('comments are outside the pinned literal grammar')
        elif character in '[({⟨':
            stack.append(character)
            if len(stack) > 64:
                refuse('literal nesting cap')
        elif character in pairs:
            if not stack or stack.pop() != pairs[character]:
                refuse('literal delimiter mismatch')
        elif character == ',' and not stack:
            item = text[start:index].strip()
            if not item:
                refuse('empty literal element')
            result.append(item)
            start = index + 1
    if stack or quoted or escaped:
        refuse('unterminated literal')
    last = text[start:].strip()
    if not last:
        refuse('empty final literal element')
    result.append(last)
    charge(len(result))
    return result


def render_list(entries):
    charge(len(entries))
    return '[' + ', '.join(entries) + ']'


def literal_list(text, count):
    if not text.startswith('[') or not text.endswith(']'):
        refuse('expected literal list')
    entries = [] if text == '[]' else split_top(text[1:-1])
    if len(entries) != count or render_list(entries) != text:
        refuse('literal list count or exact reconstruction')
    return entries


def tuple_fields(text, count):
    if not text.startswith('⟨') or not text.endswith('⟩'):
        refuse('expected constructor tuple')
    fields = split_top(text[1:-1])
    if len(fields) != count or '⟨' + ', '.join(fields) + '⟩' != text:
        refuse('tuple count or exact reconstruction')
    return fields


def declaration(lines, prefix):
    matches = [(index, line) for index, line in enumerate(lines) if line.startswith(prefix)]
    if len(matches) != 1:
        refuse('declaration inventory: ' + prefix)
    index, line = matches[0]
    if not line.endswith('\n'):
        refuse('declaration newline')
    return index, line[len(prefix):-1]


def balanced(names):
    charge(1)
    if not names:
        refuse('empty append assembly')
    if len(names) == 1:
        return names[0]
    middle = len(names) // 2
    return '(' + balanced(names[:middle]) + ' ++ ' + balanced(names[middle:]) + ')'


def project(stage):
    global ctx
    ctx = stage
    original_raw = stage.raw('TypedCNFInstance.Data')
    original = original_raw.decode('utf-8')
    if len(original_raw) != 609248 or '\r' in original:
        refuse('pinned Data size or newline form')
    unchanged = {name: stage.raw('TypedCNFInstance.' + name[:-5]) for name in UNCHANGED}
    lines = original.splitlines(keepends=True)
    allocation_prefix = 'def allocation : CNFDenseAllocation.Snapshot := '
    trace_prefix = 'def trace : CNFClauseTrace.Snapshot := '
    allocation_index, allocation_text = declaration(lines, allocation_prefix)
    trace_index, trace_text = declaration(lines, trace_prefix)
    context_index, _ = declaration(lines, 'def context : Context := ')
    if (len(lines) != 776 or allocation_index != 11 or context_index != 772 or
            trace_index != 773 or lines[-2:] != ['\n', 'end TypedCNFInstance\n']):
        refuse('pinned declaration layout')
    preamble = ''.join(lines[:allocation_index])
    expected_preamble = (
        'import Oak.CNFTypedBridge\nimport TypedCNFRefutation.Original\n\n'
        'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n'
        'namespace TypedCNFInstance\nopen Oak\n'
        'open Oak.RupCheck Oak.TseitinCNF Oak.CNFReplayApply Oak.CNFReplayTerm\n'
        'open Oak.CNFTypedCircuit Oak.CNFTypedNode Oak.CNFTypedMemory Oak.CNFTypedBridge\n\n')
    if preamble != expected_preamble:
        refuse('pinned preamble')
    preserved = lines[allocation_index + 1:context_index + 1]
    word_root = preserved[:-1]
    if len(word_root) != 760 or any(
            re.match(r'def [nr][0-9]+(?:[A-Za-z]+)? : ', line) is None
            for line in word_root):
        refuse('word/root declaration inventory')
    names = [line.split(' ', 2)[1] for line in word_root]
    if len(set(names)) != 760 or any(name not in names for i in range(375)
                                    for name in ('n%d' % i, 'r%d' % i)):
        refuse('word/root declaration coverage')

    allocation = tuple_fields(allocation_text, 5)
    if allocation[:2] != ['2890', 'false']:
        refuse('allocation header')
    inputs = literal_list(allocation[2], 353)
    gates = literal_list(allocation[3], 2537)
    memo = literal_list(allocation[4], 2537)
    trace = tuple_fields(trace_text, 4)
    if trace[0] != 'allocation' or trace[2] != '[5781]':
        refuse('trace allocation or obligation')
    clauses = literal_list(trace[1], 10351)
    emitted = literal_list(trace[3], 10352)
    charge(len(emitted))
    if emitted[:-1] != clauses or emitted[-1] != '[-2890]':
        refuse('emitted is not the exact builder prefix plus final singleton')

    # Explicit structural shape checks supplement the authenticated byte source.
    for entry in inputs:
        fields = tuple_fields(entry, 2)
        if any(re.fullmatch(r'[0-9]+', field) is None for field in fields):
            refuse('input allocation element')
    for entry in gates:
        fields = tuple_fields(entry, 5)
        if any(re.fullmatch(r'[0-9]+', field) is None for field in fields):
            refuse('encoded gate element')
    for entry in memo:
        fields = tuple_fields(entry, 2)
        if (re.fullmatch(r'\.(?:binary|ite) [0-9]+ [0-9]+ [0-9]+', fields[0]) is None or
                re.fullmatch(r'[0-9]+', fields[1]) is None):
            refuse('memo element')
    for entry in emitted:
        if not entry.startswith('[') or not entry.endswith(']'):
            refuse('signed clause delimiters')
        literals = split_top(entry[1:-1])
        if (not 1 <= len(literals) <= 3 or render_list(literals) != entry or
                any(re.fullmatch(r'-?[1-9][0-9]*', literal) is None for literal in literals)):
            refuse('signed clause shape')

    families = [
        ('InputData', 'typedInputBlock', 'Oak.CNFDenseAllocation.InputAllocation', inputs, 3, 1),
        ('GateData', 'typedGateBlock', 'Oak.CNFBuilderTrace.EncodedGate', gates, 20, 5),
        ('MemoData', 'typedMemoBlock', 'Oak.CNFDenseAllocation.MemoEntry', memo, 20, 5),
        ('ClauseData', 'typedClauseBlock', '(List Int)', clauses, 81, 21),
    ]
    header = ('import Oak.CNFTypedBridge\n\n' +
              ''.join(lines[3:allocation_index]))
    generated = []
    assemblies = {}
    block_records = []
    family_records = []
    for module_prefix, block_prefix, element_type, entries, block_count, module_count in families:
        chunks = [entries[offset:offset + BLOCK] for offset in range(0, len(entries), BLOCK)]
        if len(chunks) != block_count or (len(chunks) + PER_MODULE - 1) // PER_MODULE != module_count:
            refuse('fixed family partition')
        flat = [entry for chunk in chunks for entry in chunk]
        charge(len(flat))
        if flat != entries or render_list(flat) != render_list(entries):
            refuse('family reconstruction')
        block_names = [block_prefix + '%03d' % index for index in range(len(chunks))]
        assemblies[module_prefix] = balanced(block_names)
        for start in range(0, len(chunks), PER_MODULE):
            module = module_prefix + '%02d' % (start // PER_MODULE)
            source = [header]
            for index in range(start, min(start + PER_MODULE, len(chunks))):
                chunk = chunks[index]
                if not 1 <= len(chunk) <= BLOCK:
                    refuse('block entry bound')
                literal = render_list(chunk)
                # Parse the exact emitted payload again; it must retain every token.
                if literal_list(literal, len(chunk)) != chunk:
                    refuse('generated block reconstruction')
                source.append('def %s : List %s := %s\n' %
                              (block_names[index], element_type, literal))
                block_records.append({
                    'name': block_names[index], 'module': module,
                    'first_entry': BLOCK * index, 'entries': len(chunk),
                    'literal_sha256': digest(literal.encode('utf-8')),
                })
            source.append('\nend TypedCNFInstance\n')
            generated.append((module + '.lean', ''.join(source).encode('utf-8')))
        family_records.append({
            'family': module_prefix, 'entries': len(entries), 'blocks': block_count,
            'modules': module_count, 'original_list_sha256': digest(render_list(entries).encode('utf-8')),
        })
    if len(generated) != 32 or len(block_records) != 124:
        refuse('part module or block inventory')

    new_lines = list(lines)
    new_lines[allocation_index] = allocation_prefix + '⟨2890, false, %s, %s, %s⟩\n' % (
        assemblies['InputData'], assemblies['GateData'], assemblies['MemoData'])
    new_lines[trace_index] = (
        'def typedBuilderClauses : List (List Int) := ' + assemblies['ClauseData'] + '\n' +
        trace_prefix + '⟨allocation, typedBuilderClauses, [5781], ' +
        'typedBuilderClauses ++ [[-2890]]⟩\n')
    imports = ''.join('import TypedCNFInstance.' + name[:-5] + '\n' for name, _ in generated)
    new_data = ''.join(new_lines[:2]) + imports + ''.join(new_lines[2:])
    preserved_again = [line for line in new_data.splitlines(keepends=True)
                       if re.match(r'def [nr][0-9]+(?:[A-Za-z]+)? : ', line) or
                       line.startswith('def context : Context := ')]
    if preserved_again != preserved:
        refuse('word/root/context declaration preservation')
    generated.append(('Data.lean', new_data.encode('utf-8')))
    generated.extend((name, unchanged[name]) for name in UNCHANGED)
    expected_names = {prefix + '%02d.lean' % i for prefix, _, _, _, _, count in families
                      for i in range(count)} | {'Data.lean'} | set(UNCHANGED)
    if len(generated) != 50 or {name for name, _ in generated} != expected_names:
        refuse('complete output inventory')
    if sum(len(raw) for _, raw in generated) > MAX_BYTES:
        refuse('aggregate generated source cap before publication')

    # The unchanged inputs remain in the original immutable writer directory.
    for name, raw in generated:
        if name not in UNCHANGED:
            stage.save('TypedCNFInstance.' + name[:-5], raw)
    stage.finish(33, {'word_root_declarations': 760, 'context_declarations': 1,
                      'leaf_blocks': 124, 'builder_clauses': 10351,
                      'emitted_clauses': 10352})
