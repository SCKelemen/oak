# Note: the OS pilot's consolidated requests — assessment and dispositions

**Status: round one landed, 2026-09-12.** Source: the OS (hypervisor) pilot's
consolidated list, synthesized from its `OAK-NEEDS.md` and its design logs
0102–0105, grouped by leverage. The pilot's numbering is kept.

| # | Request | Determination | Disposition |
| --- | --- | --- | --- |
| R1 | Multiple live instances of a stateful module, mutated in place, without by-value copies of large state (three stage2 regimes at once; a ~400 KiB pool) | **A port rewrite with existing features, plus one backend fix.** N instances are an owned array of the record and one span over it; a store through an element (`s[dom].pool[k] = v`) and a field write (`s[dom].count = ...`) are in place. The one copy the backend did make — a field **read** through a span element returned the whole record by value from the checked helper — is removed: `s[dom].count` now selects the element in place. | **Landed** (`50-borrowing.md` §8e, `90-backend.md` §8; `compiler/e2e_os_round1_test.go`). Bind the span in a block; read the owner after it. Whole-element binding `st: Stage2 = s[dom]` remains the explicit copy. |
| R2 | Module-level constants as C constants, not mutable statics (`static u64 page_size = 16384;` makes `/ page_size` a hardware division) | **A codegen gap, confirmed from the generated C.** | **Landed** (`90-backend.md` §8a): a scalar global with a constant initializer that no statement assigns, index-assigns, borrows, or addresses is `static const`; the C compiler folds it. A written global stays `static`. |
| R3 | Bounds-check elision for owned fixed arrays (`state: [4]u8` under `i < len(state)`) | **Half confirmed.** A local owned array and a record's array field already elide under the canonical loop; a **top-level** table did not, because extent facts admitted only local containers. | **Landed**: a top-level owned array is admitted in a fact's container position (its static extent is a fact of the program; the index stays local). `TABLE[i]` under `i < len(TABLE)` is direct. If a pinned port still shows checks, its loop is outside the canonical shape (the index must change only as the body's last statement) — send the loop. |
| R4 | `o + 3 < len(b)` should elide `b[o]..b[o+3]` | **Declined as spelled, and the chapter was wrong to promise it.** Fixed-width `o + 3` wraps (`20-types.md` §11.1), so the guard can hold for an `o` far past the end; the typechecker reports that shape as `OAK-T0701`. | **Documentation fixed** (`50-borrowing.md` "Offset bound"): the sound spelling is `len(b) >= u32(4) && o <= len(b) - u32(4)` (or `o < len(b) - 3` with `len(b) >= 3` known), which proves all four reads today (`guard_without_wrap`, `offset_under_bound`); the test pins both spellings. |
| R5 | Constant-fold `(a << k) \| b` in global initializers | **A codegen gap**: the shift routed through the checked helper, which is not a C constant expression. | **Landed** (`90-backend.md` §8a): in a constant context the shift is the plain operator at the checked width. |
| R6 | `mair_el1`, `sp_el0`, `elr_el1`, `spsr_el1` for the verified assembler | **Already present**: all four are in the generated table (`asm/sysregs_gen.go`, from Arm's SysReg XML, A-profile 2026-06), readable and writable. | **No change**; a test pins the four (`asm/sysreg_test.go`). The pilot's checkout predates the table's regeneration. |
| R7 | FFI `Buffer[T]` + arena, and borrowing runtime memory in `unsafe` | **Already present**: `Buffer[T]` with custody states and Buffer fields in records (`92-ffi.md` §2.8), the `arena` package (`stdlib/arena.oak`). | **No change**; pointer to the chapter. |
| R8 | Resource contracts on function types, borrow-by-provenance (`OAK-B0111`) | **Already present**: `50-borrowing.md` §9 (contracts across callable boundaries, provenance, `OAK-B0111`–`B0115`). | **No change**; the capability and process tables can adopt `consume`/`borrowed` modes as written. |
| R9 | A time library (instants, civil time, RFC 3339) | **Already present**: `stdlib/time.oak` (`Instant`, `Duration`, `Civil`, `Zoned`, RFC 3339 text), with `timesim` and `timenative` realizations. | **No change.** |
| R10 | Inlinable emission or the maturing native backend | **Direction**, sequenced after R1 by the pilot itself. | Open. Hot pure functions already carry `OAK_INLINE`; a header-emitting mode is the increment when perf is on the critical path. |

## What the round did not do

- It did not measure the stage2 walk. R2's effect is the C compiler's
  folding of a `static const`; the pilot's `stage2_bench.c` is the check.
- It did not change the wrapping contract of `+` (R4). The chapter now
  says what the checker does, and why.
