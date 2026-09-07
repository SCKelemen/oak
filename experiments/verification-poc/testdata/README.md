# Python-to-Go migration fixtures

`parity/` was captured from the Python implementation before its removal.
Each case retains its checked-model document, three CNF formulas, three SMT
queries, TLA+/Lean projections, and a proof or counterexample certificate.

Go tests compare the native checked AST (excluding the source hash) and every
projection byte for byte, then explicitly rebind only the fixture certificate's
format and source identity before checking its unchanged CNF hashes and proof
or trace. The command-line verifier never performs that rebinding.

These are static regression data. No Python process or parser is used in tests.
The fixtures establish parity for five examples, not universal refinement of
the encoder or equivalence to Oak's runtime semantics.
