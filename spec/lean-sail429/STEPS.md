# Actual fetched nine-step RV64 execution

`OakSailSteppedFrame.accepted_typed_steps` connects the restricted original
source declaration and its existing typed-expression meaning to **nine calls
of the unchanged generated `try_step`** in one Lean 4.29 kernel. Each call
performs actual interrupt dispatch, RAM instruction fetch, external decoding,
generated instruction execution and `tick_pc`. All 36 checked compiler bytes
are placed in the concrete sequential RAM map. No fetch, instruction, interrupt
or step-success proposition appears among the public theorem's assumptions.

The supported source is one canonical two-parameter u32 AND/OR/XOR declaration.
The mandatory compiler pin compiles exactly that complete original input,
extracts the entire function symbol, rejects unresolved relocations in its
extent, and kernel-checks source acceptance and all emitted bytes. This is a
bounded checked instance, not a universal correctness theorem of the Go parser
or compiler.

## Explicit execution profile

All previous concrete Machine/Bare, stack and executable-code conditions remain:
MemoryConfig, ConfigOK, FrameAccess, full byte placement, four-byte code alignment,
a nonwrapping 36-byte interval, executable PMA containment, low non-MMIO addresses
and code disjointness from both eight-byte saved stack slots. The ABI maps x2,
x9, x18, x10, x11 and x1; x10/x11 contain sign-extended u32 inputs. The cleared
return address meets four-byte alignment. No following caller instruction is
fetched, so executability of the return destination is outside this theorem.

StepProfile additionally maps:

- cur_privilege = Machine, mstatus = 0, misa = the pinned RV64I configuration
- mip = 0, mie = 0, sig_meip = 0
- elp = 0 and hart_state = HART_ACTIVE
- mcountinhibit = 4#32 (IR inhibited), minstretcfg = 0

The source-bound theorem explicitly maps initial PC and nextPC to the code
address and initial minstret_increment to false. These are initial-state
premises, not a startup or loader implementation.

The proof accounts for eager reads even when a Boolean condition is already
false: interrupt dispatch still reads mip, mie, mstatus, sig_meip and misa;
should_inc_minstret still reads minstretcfg with IR set. RV64I disables S, so
mideleg/sig_seip are not read. Landing-pad checking reads elp even though the
separate instruction configuration disables landing-pad updates.

`stepProfileState_profile` constructs a nonempty step-profile witness from any
state while preserving memory. The checked examples also provide mutually
compatible executable/data permissions and disjoint ranges: code at 0x10000,
SP at 0x11000, and a read/write/execute PMA region covering 0x10000..0x13000.
These are permitted freestanding configurations, not assertions that a real
platform reset or Linux loader creates them.

## Exact transition and observations

The bounded driver `steps` calls actual `try_step` nine times and retains all
nine returned flags. The theorem proves the list is nine false values, meaning
none of these calls returns the waiting flag. Each instruction successfully
retires through the generated control path.

On every call, try_step writes minstret_increment=false. Active-hart execution
fetches the current word and writes nextPC=PC+4 before executing it. The first
eight bodies leave that sequential nextPC; RET replaces it with x1 with bit
zero cleared. Actual tick_pc reads nextPC, writes PC, and performs the model's
PC callback readback. The final state has both PC and nextPC equal to that
aligned return target, and minstret_increment=false.

The final x10 is the sign-extended u32 source result. Original SP, s1/s2, return
address and every register other than x10, PC, nextPC and minstret_increment are
preserved, including mapped values or absence. In particular minstret is
unchanged: IR inhibition makes its update branch unselected, without requiring
an initial minstret mapping. Only the two saved eight-byte words change in RAM;
all other memory lookups preserve their values or absence. Choice state, tags,
cycleCount and sailOutput remain unchanged. The observation lemmas state these
facts separately from the exact whole-state equality.

## Deliberate remaining boundaries

The proof does not run tick_clock or the generated outer platform loop. It does
not advance mcycle/mtime, run CLINT clock dispatch, model external interrupt
changes between calls, prove reset-state reachability, load an ELF or establish
Linux process behavior. Initial byte placement and all configuration/mapping
premises remain explicit. The source-to-Lean exporter is not verified; the
target is its exact provenance-pinned generated definitions. No generated
source, toolchain pin or production verified label changes.

## Kernel closure and checks

The complete step theorem has 77 reported dependencies: the existing 76-name
full-dispatch closure, plus `valid_reservation : Unit → Bool` from
LeanRV64D/RiscvExtras.lean:38. That opaque Boolean is referenced through
try_step's HART_WAITING path, excluded by the proved HART_ACTIVE profile. No
value is assumed. The existing terminal/reservation and floating-point opaque
primitives retain their documented types and unused-branch boundaries from
`../lean-sail433/FRAME.md` and its allowlist. These are model parameters, not
assumed correctness propositions. Step-specific helpers are audited separately;
there are no native-evaluation, sorry or unlisted axioms.

`step-audit.py` checks theorem closures and the new declaration's exact type.
Negative controls prove actual should_inc_minstret returns true when IR is
cleared, actual PMA fetch checking returns E_Fetch_Access_Fault for a matching
non-executable region, and source/body certificates reject changed input bytes.
The prior missing-memory, wrap and overlap checks remain required.

Run after restoring the original provenance-verified export:

```
cd spec/lean-sail429
lake build
python3 audit.py
python3 step-audit.py
```

From the repository root:

```
OAK_REQUIRE_RV64_LEAN=1 go test ./compiler -run '^TestRV64(Fetched|Stepped)BitwiseCompilerMatchesLean$' -count=1 -v
```

The existing required Sail CI job runs these checks with no-skip enforcement.
The isolated project compiles canonical Oak and shared bridge sources directly
through srcDir. It does not import proof objects from another Lean version.
The existing Lean 4.33 compatibility lane remains in place.
