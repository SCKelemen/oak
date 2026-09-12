/-!
# Targets and cross builds (docs/spec/90-backend.md §2a)

The model of `target` and `toolchain` (Go): the closed set of platforms Oak
builds for, what each decides (the assembler lane, the object format, the
static-linking default, the C data model), and the resolution of a C
compiler driver from what a host has, in a fixed order. The theorems are
the tooling's promises:

* every supported target is LP64 — the one C data model the backend
  assumes (`92-ffi.md` §2.4);
* the lane of a target is a function of its architecture alone, so a unit
  applies to a target exactly when its lane matches (`94-assembler.md` §9);
* resolution is total over the availability record: it yields a driver or
  a definite refusal, never falls through;
* a resolved driver targets the requested platform (soundness), the
  explicit `OAK_CC` wins over every discovered compiler, and the host
  target always resolves when `cc` is present;
* a cross build for Linux links statically; a freestanding build is an
  object.
-/

namespace Oak.Target

inductive OS where
  | linux | darwin | freestanding
  deriving DecidableEq, Repr

inductive Arch where
  | arm64 | amd64 | riscv64
  deriving DecidableEq, Repr

structure Target where
  os : OS
  arch : Arch
  deriving DecidableEq, Repr

/-- The closed set: Darwin has no RISC-V platform. -/
def supported (t : Target) : Bool :=
  match t.os, t.arch with
  | .darwin, .riscv64 => false
  | _, _ => true

/-- The C data model every supported target has: `int` 32, `long` and
    pointers 64 bits. -/
structure DataModel where
  intBits : Nat
  longBits : Nat
  ptrBits : Nat
  deriving DecidableEq, Repr

def lp64 : DataModel := ⟨32, 64, 64⟩

def dataModel (_ : Target) : DataModel := lp64

theorem supported_lp64 (t : Target) (_ : supported t = true) : dataModel t = lp64 := rfl

/-- The assembler lane of an architecture (`Function.Arch` in Go): arm64,
    rv64, or none for amd64. -/
inductive Lane where
  | arm64 | rv64
  deriving DecidableEq, Repr

def lane : Target → Option Lane
  | ⟨_, .arm64⟩ => some .arm64
  | ⟨_, .riscv64⟩ => some .rv64
  | ⟨_, .amd64⟩ => none

/-- The lane depends on the architecture alone. -/
theorem lane_arch (t u : Target) (h : t.arch = u.arch) : lane t = lane u := by
  obtain ⟨o₁, a₁⟩ := t
  obtain ⟨o₂, a₂⟩ := u
  simp only at h
  subst h
  cases a₁ <;> rfl

/-- An asm unit of lane `l` applies to `t` exactly when `t`'s lane is `l`;
    otherwise the Oak fallback body compiles (or, absent one, the build
    fails closed) — `stitchAsmUnits` in Go. -/
def unitApplies (l : Lane) (t : Target) : Bool := lane t == some l

theorem unitApplies_iff (l : Lane) (t : Target) : unitApplies l t = true ↔ lane t = some l := by
  simp [unitApplies]

/-- At most one lane applies to a target, so two units of different lanes
    for one signature never both realize it. -/
theorem lanes_exclusive (t : Target) (l m : Lane) (hl : unitApplies l t = true) (hm : unitApplies m t = true) : l = m := by
  rw [unitApplies_iff] at hl hm
  rw [hl] at hm
  exact Option.some.inj hm

inductive Format where
  | macho | elf
  deriving DecidableEq, Repr

def format (t : Target) : Format := if t.os = .darwin then .macho else .elf

def staticLink (t : Target) : Bool := t.os == .linux
def freestanding (t : Target) : Bool := t.os == .freestanding

/-- The RISC-V float ABI a companion object declares: lp64d for a hosted
    RISC-V target (its libc's), lp64 (soft) otherwise. -/
inductive FloatABI where
  | soft | double
  deriving DecidableEq, Repr

def rv64FloatABI (t : Target) : FloatABI :=
  if t.arch = .riscv64 ∧ t.os ≠ .freestanding then .double else .soft

theorem linux_riscv64_lp64d : rv64FloatABI ⟨.linux, .riscv64⟩ = .double := rfl
theorem bare_riscv64_lp64 : rv64FloatABI ⟨.freestanding, .riscv64⟩ = .soft := rfl

/-! ## Driver resolution (`toolchain.Resolve`) -/

/-- What a host has: the compilers on PATH and the environment. -/
structure Host where
  platform : Target
  hasCC : Bool
  hasZig : Bool
  hasClang : Bool
  hasGNU : Target → Bool   -- a target-prefixed gcc
  oakCC : Bool             -- OAK_CC set (to an executable that exists)
  sysroot : Bool           -- OAK_SYSROOT set

inductive Kind where
  | explicit | host | zig | clang | gnu
  deriving DecidableEq, Repr

structure Driver where
  kind : Kind
  target : Target
  static : Bool
  object : Bool
  deriving DecidableEq, Repr

def finish (k : Kind) (t : Target) (isHost : Bool) : Driver :=
  { kind := k, target := t, object := freestanding t, static := staticLink t && !isHost && !freestanding t }

/-- The order of `toolchain.Resolve`: OAK_CC, then cc for the host, zig,
    clang (a hosted cross target needs a sysroot), a GNU cross compiler. -/
def resolve (h : Host) (t : Target) : Option Driver :=
  let isHost := t == h.platform
  if h.oakCC then some (finish .explicit t isHost)
  else if !supported t then none
  else if isHost && h.hasCC then some (finish .host t isHost)
  else if h.hasZig then some (finish .zig t isHost)
  else if h.hasClang && (freestanding t || h.sysroot || isHost) then some (finish .clang t isHost)
  else if h.hasGNU t then some (finish .gnu t isHost)
  else none

/-- Soundness: a resolved driver targets the requested platform. -/
theorem resolve_targets (h : Host) (t : Target) (d : Driver) (hd : resolve h t = some d) : d.target = t := by
  unfold resolve at hd
  simp only at hd
  split at hd <;> (try split at hd) <;> (try split at hd) <;> (try split at hd) <;> (try split at hd) <;> (try split at hd) <;>
    first
    | (cases hd; rfl)
    | (simp at hd)

/-- The explicit compiler wins. -/
theorem resolve_explicit (h : Host) (t : Target) (hcc : h.oakCC = true) :
    resolve h t = some (finish .explicit t (t == h.platform)) := by
  unfold resolve; simp [hcc]

/-- The host target always resolves when cc is present. -/
theorem resolve_host (h : Host) (hcc : h.hasCC = true) (hs : supported h.platform = true) :
    ∃ d, resolve h h.platform = some d := by
  unfold resolve
  by_cases ho : h.oakCC
  · exact ⟨finish .explicit h.platform (h.platform == h.platform), by simp [ho]⟩
  · exact ⟨finish .host h.platform (h.platform == h.platform), by simp [ho, hcc, hs]⟩

/-- A cross build for Linux links statically; a freestanding build is an
    object and never static. -/
theorem finish_linux_static (k : Kind) (a : Arch) : (finish k ⟨.linux, a⟩ false).static = true := by
  simp [finish, staticLink, freestanding]
theorem finish_freestanding_object (k : Kind) (a : Arch) (isHost : Bool) :
    (finish k ⟨.freestanding, a⟩ isHost).object = true ∧ (finish k ⟨.freestanding, a⟩ isHost).static = false := by
  simp [finish, staticLink, freestanding]

/-- With zig present, every supported target resolves from any host: the
    "cross build from everywhere" promise. -/
theorem resolve_zig (h : Host) (t : Target) (hz : h.hasZig = true) (hs : supported t = true) :
    ∃ d, resolve h t = some d := by
  unfold resolve
  by_cases ho : h.oakCC
  · exact ⟨finish .explicit t (t == h.platform), by simp [ho]⟩
  · by_cases hh : ((t == h.platform) && h.hasCC) = true
    · exact ⟨finish .host t (t == h.platform), by simp [ho, hs, hh]⟩
    · exact ⟨finish .zig t (t == h.platform), by simp [ho, hs, hh, hz]⟩

end Oak.Target
