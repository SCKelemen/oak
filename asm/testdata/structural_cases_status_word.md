# Captured result obligation

`structural_cases_status_word.dag.gz` is a complete, losslessly compressed
symbolic result DAG from the native ARM64 `status_word` candidate. It contains
no executable source or runtime input values. The text format is the verifier's
term DAG format, with original pointer sharing represented by node IDs.

Provenance:

- Source tree: `f11cfe5c00eb2084ef56308643763a3158427ea6`.
- Candidate: `schedule+reallocate+trim-callee-saves`.
- Assembly SHA-256: `039fc1ac283129852c93748a72db429aa1d7096f3c61c368089b5b5405cd0bbd`.
- Materialization recipe SHA-256: `b7ff9eb79e056d30b8310e9b2839568986a509af59ee42017948660e257f5070`.
- Decompressed DAG SHA-256: `3b3ae62b07fd3fb305f6a286e4eae89c9d269744d7910d38da35f13351a2d3d0`.

The five roots are raw ASM result, raw Oak result, canonical ASM result,
canonical Oak result, and input domain (nil). Result and declared scalar
widths are 32. Capture occurred after normal canonicalization and before the
witness pass or BDD decision. The union contains 16,393 nodes.

The test replays this result obligation, including both case visitation
orders and the existing witness pass. It does not claim to replay the complete
function's memory effects, traps, callees, search, or native solver build.
