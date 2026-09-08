# Duplicate-aware clause classification

`ClauseClassifier.lean` computes a clause's classification from a partial
assignment. It first detects a satisfied literal, then removes false literals
and repeated occurrences. An empty residual is conflict, a singleton is unit,
and two or more distinct residual literals are unresolved.

Nine reported theorems establish duplicate-removal membership, residual
membership, the residual implied by each successful classification, and the
resulting semantic premises. A unit result names a literal present in the clause,
its variable is unassigned, and every different literal is false. A conflict
result establishes that every literal is false. The final two theorems compose
these computed facts with the previous milestone: conflict excludes satisfying
extensions and a justified unit write preserves compatible models.

The implementation does not take a semantic oracle or a proof premise to decide
its result. The soundness theorems derive those premises from successful
execution of the classifier. Literal indices must be positive for semantic
composition; the native corpus uses bounded encodings and valid three-valued
assignment bytes.

The Go harness copies the actual inner clause scan and `literal_value` definition
from `self_hosted_rup.oak` into a test wrapper. The scan body is preserved
byte-for-byte, including duplicate detection and early satisfaction. Extraction
requires unique, ordered source seams. The wrapper exposes the classification
and exact encoded unit literal; it does not change production Oak source.

The corpus covers all 85 ordered clauses of length 0..3 over two variables under
all nine partial assignments (765 cases). Another 384 cases cover both literal
polarities at every variable boundary, all assignment states, and four repeated
occurrences. The independent Go oracle uses sets; Lean uses its proved residual
classifier. Three corrupt expected outputs test the native observation path.
All cases run through the existing bounded native batches.

## Boundary

The functional duplicate-aware classifier and its semantic composition are
proved. Equivalence of Oak's imperative scan to that classifier is tested on
1,149 cases, not proved for every input. Its loop counters, byte-array accesses,
invalid-literal short-circuit behavior, and compiler remain outside these proofs.
The prior complete propagation trace and stream/certificate gates remain active.
This module does not yet replace the trace executor's existing classifier.

Next: connect the proved classifier to the executable propagation chain, carrying
assignment invariants and deriving RUP acceptance soundness through the chain.
