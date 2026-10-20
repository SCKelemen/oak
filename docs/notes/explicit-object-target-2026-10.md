# Explicit native object targets

`asm.WriteObjectFor` takes a native architecture separately from the encoded
functions. It accepts `arm64` and `rv64`, requires every function to carry the
same explicit architecture, and rejects missing/unsupported targets before
layout. Empty and data-only RV64 objects now carry `EM_RISCV`; they no longer
inherit the legacy empty-layout ARM64 default. RV64 Mach-O is refused even
when there are no functions.

The compiler's companion-object, native-object, and assembly-object emission
paths use this boundary. Targets without an Oak native assembler lane cannot
emit an empty ARM64 object through these paths. Companion C emission still
omits the object when there are no assembly functions.

`WriteObject` and `WriteObjectWith` retain their inference and compatibility
behavior for existing clients. Valid explicit nonempty objects use the same
layout, relocation and container writers and remain byte-identical. This API
binds requested architecture to object metadata and function declarations; it
does not verify arbitrary machine-code bytes or establish translation proofs.
