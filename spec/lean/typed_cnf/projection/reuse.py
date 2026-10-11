"""Reuse only concrete checker proofs, retaining each semantic constructor."""
from common import require
from bits import roots


def project(stage):
    data = stage.source('data', 'TypedCNFInstance.Data').decode()
    cases = [(121, 113, 120, 31, 25, 30, 64, 'shr'),
             (242, 239, 241, 145, 142, 144, 32, 'add'),
             (294, 291, 293, 145, 142, 144, 32, 'add'),
             (340, 337, 339, 145, 142, 144, 32, 'add')]
    for number, left, right, checked, old_left, old_right, width, op in cases:
        vectors = roots(data, (number, left, right, checked, old_left, old_right), width)
        require(all(vectors[a] == vectors[b] for a, b in
                    ((number, checked), (left, old_left), (right, old_right))), 'reused concrete root equality')
        name = 'TypedCNFInstance.Node%03d' % number
        original = stage.source('nodes', name).decode()
        prior = stage.source('bits%03d' % checked, 'TypedCNFInstance.Node%03d' % checked).decode()
        lines = [line for line in prior.splitlines() if line.startswith('theorem d%d :' % checked)]
        require(len(lines) == 1 and lines[0].count(' rfl ') == 1, 'prior checker proof boundary')
        proof = lines[0].split(' rfl ', 1)[1]
        require(proof.startswith('(checkVector_of_bitList '), 'prior checker construction')
        circuit = ('barrelBits 64 false (rootBits r%d) (rootBits r%d) 6' % (left, right)
                   if op == 'shr' else 'sumTerm (rootBits r%d) (rootBits r%d) (.constant false)' % (left, right))
        checked_circuit = ('barrelBits 64 false (rootBits r25) (rootBits r30) 6'
                           if op == 'shr' else 'sumTerm (rootBits r142) (rootBits r144) (.constant false)')
        original_line = ('theorem d%d : Derivation context n%d r%d := .binary .%s (%s) d%d d%d rfl (by decide)\n'
                         % (number, number, number, op, circuit, left, right))
        require(original.count(original_line) == 1 and original.count('theorem ') == 1, 'own constructor identity')
        replacement = ('(by\n  change checkVector context.allocation context.maxInt %d\n    (%s) r%d = true\n  exact %s)'
                       % (width, checked_circuit, checked, proof))
        stage.save(name, original.replace(original_line, original_line.replace('(by decide)', replacement), 1))
    stage.finish(4, {'checker_reuse_nodes': [121, 242, 294, 340],
                     'semantic_constructor_and_child_proofs_preserved': True})
