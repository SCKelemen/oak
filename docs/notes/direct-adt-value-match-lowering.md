# Direct ADT value-match lowering

Checked flat ADT matches can now be sequenced in supported value positions, including direct assertion operands. Lowering evaluates the subject once, keeps arm bindings scoped, preserves short-circuit and loop evaluation points, and handles the reviewed borrowed-span assignment destinations without copying owner storage. Unsupported metadata, carrier storage and nested payload constraints in the new value path produce compiler errors.

The scoped Linux/amd64 diagnostic gate passed 11 roots and 67 children, including 51 C/native pairs, static SIGILL calibration and both assignment-order traps. The diagnostic acceptance parser also passed 70 controls. Production compiler bytes and corrected Oak fixtures match the portable candidate; test instrumentation differs. Successful native artifacts were hashed during the run, while retained evidence contains their observations rather than raw successful C/products.

The exact portable whole-tree binary was not executed locally. Existing hosted CI selects the portable codegen tests in packages, direct-value/trap/evaluation-order/inline tests in e2e-a-r, and frontend refusals in compiler-rest-a-m. Require actual PASS records for all selected roots and children on the new commit, including both Linux/amd64 trap children, before claiming portable-helper acceptance. Job-green alone does not exclude skips. Diagnostic and portable helper failure handling, environment, output bounds and deadlines are not equivalent.

Two separate defects remain open. Explicit declaration semicolons work around parser paths that consume a next-line parenthesis despite the documented newline boundary rule. A distinctive trap-fixture function name avoids a backend namespace collision where user `store` becomes the runtime macro name `oak_store`. Neither workaround repairs its underlying defect.

This is a scoped compiler regression result, not full language completeness, a new proof/refinement result, target-platform acceptance or performance evidence. Earlier failure evidence is preserved. The code change excludes diagnostic helpers and the separate APDU work.

Local diagnostic validation used architecture base `12ac2f68`. The evaluation commit preserves the subsequently published `61e319ac` BDD table-growth change. The combined compiler and BDD source has not been executed locally; its exact hosted checks remain required. No earlier BDD performance attribution is transferred to this combination.
