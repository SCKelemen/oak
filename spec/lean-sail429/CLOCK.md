# Bounded clocked platform callback

`OakSailClockedSource.accepted_typed_clocked_prefix` checks the restricted
original source and all 36 production bytes against nine bounded iterations
of the generated platform callback. Each iteration uses actual try_step, with
actual tick_clock after iterations 2, 4, 6 and 8. The result retains the proven
bitwise value, frame restoration and return PC, while exposing four counter
increments and the final timer phase.

## Exactly what is connected to the generated loop

`OakSailPlatformCallback.generated_loop_callback` is a kernel-checked equality
identifying the callback passed by unchanged `LeanRV64D/Step.lean:492` to its
original `forIn Lean.Loop.mk`. It preserves the opaque iterator and exit-code
read in that equality; it does not replace the original full-loop definition.

The source of Lean 4.29's `Loop.forIn` is `Init/While.lean:25`. Its outer wrapper
has an equation, but its inner recursive partial definition does not provide
the ordinary unfolding equation needed here. `boundedPlatform` is therefore
an explicitly separate, terminating finite iterator of the identified callback.
There is **no theorem that the original full loop executes this prefix, returns,
or terminates**. With htif_done=false, RET merely returns to a caller; it does
not set a platform-exit flag. No exit-code mapping or program-exit result is
inferred.

## Additional clock state

The previous source/body/fetch/step, ABI, Machine/Bare, RAM-placement, executable
permission and stack-disjointness conditions remain. ClockProfile adds mapped:

- mcyclecfg=0, mcycle=c
- mtime=t, mtimecmp=d
- menvcfg=0 and htif_done=false

The unchanged StepProfile has mcountinhibit=4#32: retirement increments remain
inhibited, but cycle increments are enabled. The prefix requires t.toNat+4 <
d.toNat. This strict future deadline also excludes timer wrap during the four
ticks. It is not a no-wrap assumption for mcycle, which deliberately increments
modulo 2^64.

Actual `should_inc_mcycle` (Platform.lean:546) reads mcyclecfg even in Boolean
expressions with other known conditions. `tick_clock` (line554) reads privilege,
increments mcycle, increments mtime, then calls `clint_dispatch false` (line390).
The latter reads old mip, mtimecmp and the new mtime, and writes mip's MTIP bit.
The timer premise makes that bit zero; the actual same-value write is proved to
preserve the state, rather than being omitted from the model.

This pin enables Sstc (`PlatformConfig.lean:5584`), so menvcfg is read. Its STCE=0
skips the stimecmp access. The unchanged-mip path excludes the CSR callback in
the positive theorem. The threshold negative control reaches the alternate
path, proves actual MTIP=1, and executes `csr_name_write_callback "mip"`
(Callbacks.lean:616), including the eager read_mip inputs. The underlying full
CSR callback at Callbacks.lean:238 is pure Unit in this generated model.

## Observable result

`plat_insns_per_tick` is exactly2 (PlatformConfig.lean:11032). Starting phase0,
nine iterations end at phase1 with mcycle=c+4 modulo64 and mtime=t+4 without wrap.
The callback's local step number stays unchanged: unchanged try_step returns
false on the proven active-instruction path, and the generated callback invokes
`cycle_count` and increments its local step number only on true. We retain that
exact generated behavior, not an inferred hardware meaning of the flag.
`cycle_count` would update the sequential model's cycleCount field
(ConcurrencyInterfaceV1.lean:285); it is not invoked in this prefix.

Consequently cycleCount remains unchanged while the architectural mcycle CSR
changes. minstret and all other counters remain unchanged. Final PC/nextPC,
result and callee-save behavior match the preceding step theorem. Only mcycle
and mtime are added to its changed-register set. The only RAM changes remain
the 16 saved stack bytes; code, memory outside those slots, tags, choice state
and sailOutput are preserved. The fixed instruction/CLINT debug flags are false;
there are no hidden device-output or trace effects.

## Checks and trust boundary

The model/export sources and toolchain pins are unchanged. One Lean4.29 kernel
checks canonical source, typed meaning, physical memory, fetch, steps, clocks
and bounded callback composition. Actual clock helpers retain only standard
Lean axioms and sys_enable_experimental_extensions; the full callback/prefix
retains the existing77-name step closure, with no additional opaque parameter.
The kernel audit includes the generated callback equality and the complete
source-bound prefix, and rejects native-evaluation, sorry or unlisted axioms.

Constructive ClockProfile+StepProfile witnesses establish nonvacuity. Negative
controls cover an alternate initial phase, exact timer-threshold arrival with
actual MTIP update, and modular cycle-counter wrap. The source/full-byte compiler
pin and prior malformed-source/code/permission/stack tests remain required.
The independent exporter-faithfulness boundary remains explicit.

Run in this directory after restoring the provenance-verified original export:

```
lake build
python3 audit.py
python3 step-audit.py
python3 clock-audit.py
```

From the repository root:

```
OAK_REQUIRE_RV64_LEAN=1 go test ./compiler -run '^TestRV64(Fetched|Stepped|Clocked)BitwiseCompilerMatchesLean$' -count=1 -v
```

ELF loading, platform reset/reachability, external interrupt changes, real-time
scheduling and full-loop execution/termination remain open. No production
verified label or Linux-process claim is introduced.
