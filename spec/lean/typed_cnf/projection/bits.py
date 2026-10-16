"""Scalar replay facts for the exact Node031 and Node145 circuits."""
import json
import re
from common import require


def balanced(items, combine):
    require(bool(items), 'empty balanced expression')
    if len(items) == 1:
        return items[0]
    middle = len(items) // 2
    return combine(balanced(items[:middle], combine), balanced(items[middle:], combine))


def list_text(values):
    return '[' + ', '.join(str(value) for value in values) + ']'


def roots(data, numbers, width):
    result = {}
    for number in numbers:
        matches = re.findall(r'^def r' + str(number) + r' : List Nat := (\[[^\n]*\])$', data, re.M)
        require(len(matches) == 1, 'root declaration')
        values = json.loads(matches[0])
        require(len(values) == width and all(type(v) is int and 0 <= v <= 5781 for v in values),
                'root width/edge range')
        result[number] = values
    return result


def project(stage):
    if stage.name == 'bits031':
        number, width, left, right, op = 31, 64, 25, 30, 'shr'
        circuit = 'barrelBits 64 false (rootBits r25) (rootBits r30) 6'
    else:
        require(stage.name == 'bits145', 'scalar stage identity')
        number, width, left, right, op = 145, 32, 142, 144, 'add'
        circuit = 'sumTerm (rootBits r142) (rootBits r144) (.constant false)'
    name = 'TypedCNFInstance.Node%03d' % number
    original = stage.source('nodes', name).decode()
    data = stage.source('data', 'TypedCNFInstance.Data').decode()
    vectors = roots(data, (left, right, number), width)
    if number == 31:
        require(vectors[right][:6] == [3, 780, 786, 792, 798, 804], 'six symbolic count edges')
    original_line = ('theorem d%d : Derivation context n%d r%d := .binary .%s (%s) d%d d%d rfl (by decide)\n'
                     % (number, number, number, op, circuit, left, right))
    require(original.count(original_line) == 1 and original.count('theorem ') == 1,
            'exact original scalar declaration')
    predecessor = 'import TypedCNFInstance.Node%03d\n' % (number - 1)
    require(original.startswith(predecessor), 'exact scalar predecessor')
    header = original[:original.index(original_line)]
    suffix = original[original.index(original_line) + len(original_line):]
    require(suffix == '\nend TypedCNFInstance\n', 'exact scalar suffix')
    common_header = header[len(predecessor):]
    rows = []
    for bit in range(width):
        proposition = ('replayCircuit context.allocation context.maxInt ((' + circuit + ') ' + str(bit) +
                       ') = some (r' + str(number) + '.getD ' + str(bit) + ' 0)')
        rows.append({'theorem': 'd%d_replay_bit%02d' % (number, bit), 'proposition': proposition})
    lists, groups = [], []
    for part in range(width // 4):
        indices = list(range(4 * part, 4 * part + 4))
        owned = [rows[bit] for bit in indices]
        bit_list = list_text(indices)
        group_name = 'd%d_replay_group%02d' % (number, part)
        theorem_lines = ['theorem ' + row['theorem'] + ' :\n    ' + row['proposition'] + ' := by decide\n'
                         for row in owned]
        group_statement = ('∀ bit, bit ∈ ' + bit_list + ' →\n      replayCircuit context.allocation context.maxInt ((' +
                           circuit + ') bit) = some (r' + str(number) + '.getD bit 0)')
        joined = '(List.forall_mem_nil _)'
        for row in reversed(owned):
            joined = '(List.forall_mem_cons.mpr ⟨' + row['theorem'] + ', ' + joined + '⟩)'
        theorem_lines.append('theorem ' + group_name + ' :\n    ' + group_statement + ' :=\n  ' + joined + '\n')
        imports = ['TypedCNFInstance.Data', 'TypedCNFInstance.Checks', 'Oak.CNFVectorReplay']
        text = ''.join('import ' + module + '\n' for module in imports) + common_header + '\n'.join(theorem_lines) + suffix
        require(text.count(':= by decide') == 4 and text.count('theorem ') == 5, 'scalar/group proof inventory')
        stage.save(name + 'Bits%02d' % part, text)
        lists.append(bit_list)
        groups.append(group_name)
    bit_list = balanced(lists, lambda left, right: '(' + left + ' ++ ' + right + ')')
    joined = balanced(groups, lambda left, right: '(List.forall_mem_append.mpr ⟨' + left + ', ' + right + '⟩)')
    final_proof = '(checkVector_of_bitList (bits := ' + bit_list + ') (by decide) (by decide) ' + joined + ')'
    replacement_line = original_line.replace('(by decide)', final_proof)
    require(replacement_line[:replacement_line.index('rfl ') + 4] == original_line[:original_line.index('rfl ') + 4],
            'constructor or original premises changed')
    new_header = predecessor + ''.join('import ' + name + 'Bits%02d\n' % part for part in range(width // 4)) + common_header
    stage.save(name, new_header + replacement_line + suffix)
    stage.finish(width // 4 + 1, {'node': number, 'bits': width, 'groups': width // 4})
