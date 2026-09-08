# EL2 physical timer register surface

Oak now exposes read_cntpct_el0 and read_cntfrq_el0 as read-only u64
operations, plus read/write_cnthp_ctl_el2 and read/write_cnthp_cval_el2.
These use the existing system-register semantic authority and explicit
AArch64 MRS/MSR lowering. No portable timer emulation or hidden barriers
are added.

CNTPCT is the physical counter; CNTFRQ gives its frequency in Hz. Oak
exposes CNTFRQ as read-only deliberately, although privileged firmware
can architecturally write it. CNTHP_CTL and CNTHP_CVAL require EL2 and
control the non-secure hypervisor physical timer. Control bit 0 enables
the timer, bit 1 masks its output, and read-only bit 2 reports the timer
condition. The timer is a level interrupt source. Software must disable,
mask, or reprogram it before completing interrupt-controller service.

The caller owns privilege configuration, GIC routing, barriers, deadline
overflow policy, and interrupt entry/return. Reads/writes alone neither
enable IRQ delivery nor preserve an interrupted ABI frame. Tests verify
all six transfer instructions and exact register names with no added
barriers; catalog tests reject write access to the two counter inputs.

Consumer: SCKelemen/os's single-core QEMU EL2 timer interrupt pilot.
