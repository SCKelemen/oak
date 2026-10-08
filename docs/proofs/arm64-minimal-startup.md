# Minimal ARM64 ELF-to-syscall-request slice

This local, experimental slice pins the actual `EmitExecutable` output of
`main: (): i32 { 42 }` for Linux/ARM64. The complete ELF is 4648 bytes. Its
entry and text address are 0x10000, with one RX PT_LOAD at file offset 0x1000,
file/memory size 32, alignment 4096. The 20-byte text is:

- BL +12, which saves the startup continuation in X30
- MOVZ W8,#93
- SVC #0
- MOVZ W0,#42
- RET X30

Execution order differs from file order: BL, main MOVZ, RET, syscall-number
MOVZ, SVC. Five projected steps from arbitrary initial registers/SP/flags
produce the request `(syscall number 93, argument 42)`. Four steps do not.

The target-independent `Oak.MinimalELF` checker binds the raw little-endian
ELF64 header, AArch64 machine number, executable type, ABI flags, one RX
file-backed PT_LOAD, alignment, file/address bounds, no wrapping and exact
body bytes. ARM admission additionally requires entry 0x10000. Mere presence
of a correct body elsewhere in an ELF is insufficient to prove startup.

The compiler test reads the production ELF with Go's independent debug/elf
reader, pins its actual section/segment/entry layout, and feeds all 4648 actual
bytes to Lean. The kernel then checks ELF admission and transports the
successful startup request through that admitted file slice. This is finite
compiler correspondence for this one source, not a universal source parser,
optimizer or linker implementation theorem.

The CPU model is an explicit no-fault projection supporting only BL, MOVZ W
with zero shift, ordinary RET and SVC 0. It reads a supplied byte list. No
claim is made about actual OS loading, mappings, permissions, hardware fetch,
PostDecode, BranchTo, architectural SVC exception handling, Linux's service
implementation or process exit. In particular, request 93 with argument 42 is
not renamed to a proved process exit 42. Independent emulator execution is
not yet run because qemu-aarch64 is not installed in this environment.

A two-input bitwise helper plus constant main was also investigated. The
compiler folds the constant main to zero, leaving the helper uncalled. This
startup example therefore deliberately makes no dynamic-bitwise claim.

Validation: pinned Lean 4.33.1 build; complete production-image admission and
startup test with OAK_REQUIRE_ARM64_LEAN=1; public theorem axiom audit without
sorryAx/native-decide axioms. This work has not been published or connected
to production verification verdicts.
