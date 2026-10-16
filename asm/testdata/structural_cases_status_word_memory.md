# Captured status_word final memory equality

This fixture is the complete arbitrary-index ew memory equality from the first native status_word candidate, preserving the DAG and all declared widths. The fresh ew[?] index remains symbolic at 32 bits. It includes the raw ASM and Oak memory roots, their canonical roots, and the nil domain. No branch, address, alias, or memory value has been selected.

The candidate assembly, source, reference, complete materialization recipe and machine contract were checked byte-for-byte against the immutable first validation capture. Candidate: schedule+reallocate+trim-callee-saves. Body SHA256: 039fc1ac283129852c93748a72db429aa1d7096f3c61c368089b5b5405cd0bbd. Recipe SHA256: b7ff9eb79e056d30b8310e9b2839568986a509af59ee42017948660e257f5070.

Capture used full source/default EmitNative preprocessing with only status_word selected; preceding native function metadata transitions were absent, so this is not an exact hosted-prefix replay. The ordinary unjoined check deferred memory because the logs had 73 versus 75 entries; its joined retry returned Witnessed on the scalar result. The original deferred memory check then reached this obligation. Its pointwise attempt rejected unequal log lengths without any implication calls. Capture stopped before this obligation's witnesses or BDD, with no proof verdict.

The frozen capture code was ecf1492feae428da25c1f00916a94e93c8b4f709 plus observation-only hooks. 18,140 unique nodes, zero argument references. Raw roots 2888/8853, canonical roots 11325/18139, domain -1. Declared parameters ew[?], kind, le.bytes_at, le.state_at, le.strs_at all have width32.

Uncompressed SHA256: 4c36ee5210db0887ba49611847bc04536531d92549e4434cc4c549c7545642e6. Tests validate the digest before reconstructing the graph and replay the actual equality checker, including witnesses. The fixture proves no broader function or solver property by itself.
