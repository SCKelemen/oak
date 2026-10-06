# Compiler diagnostic corpus

Each `.oak` file is compiled through the public `Compilation.EmitC()` pipeline and must be rejected before C emission with the phase and stable code encoded in its filename.

Filename contract:

`<case>[.strict].error.<typecheck|borrowcheck|discipline>.<OAK-X0000>.oak`

Use `.strict` only when the diagnostic is intentionally warning-severity in the default profile and becomes rejecting under the strict zero-warning profile.

`TestDiagnosticCorpusCoversStableTypeDiagnostics` requires every exported stable typechecker diagnostic in the T010x/T020x/T030x families to have at least one source-level public-pipeline witness.
