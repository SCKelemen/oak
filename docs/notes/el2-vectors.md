# EL2 exception vector base

Oak exposes `arm64.read_vbar_el2() -> u64` and
`arm64.write_vbar_el2(value: u64) -> ()`. These are privileged AArch64
register operations, with no hidden allocation or barrier. The OS must supply
a valid 2 KiB-aligned executable vector table for its translation regime and
execute an explicit ISB after installation. The write intrinsic does not
validate mappings or establish a vector table.

The OS collection payload uses these operations to install a fatal exception
diagnostic path. ESR_EL2, ELR_EL2, SPSR_EL2 and FAR_EL2 reads were already
available. FAR is meaningful only for exception classes that define it.

Reference: [Arm VBAR_EL2](https://support.arm.com/documentation/ddi0601/2023-12/AArch64-Registers/VBAR-EL2--Vector-Base-Address-Register--EL2-?lang=en).

The instruction-refinement tests require exact MRS/MSR VBAR_EL2 operations and
verify that neither introduces a barrier. Runtime vector alignment, dispatch,
and exception diagnostics are exercised in the OS QEMU suite.
