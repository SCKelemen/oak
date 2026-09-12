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
  | arm | riscv32 -- the 32-bit microcontroller architectures (Cortex-M, RV32)
  deriving DecidableEq, Repr

structure Target where
  os : OS
  arch : Arch
  deriving DecidableEq, Repr

/-- The 32-bit microcontroller architectures. -/
def Arch.mcu : Arch → Bool
  | .arm | .riscv32 => true
  | _ => false

/-- The closed set: Darwin has no RISC-V platform; the microcontroller
    architectures exist freestanding only. -/
def supported (t : Target) : Bool :=
  match t.os, t.arch with
  | .darwin, .riscv64 => false
  | .linux, .arm | .linux, .riscv32 | .darwin, .arm | .darwin, .riscv32 => false
  | _, _ => true

/-- A C data model: the widths of `int`, `long`, and pointers. -/
structure DataModel where
  intBits : Nat
  longBits : Nat
  ptrBits : Nat
  deriving DecidableEq, Repr

def lp64 : DataModel := ⟨32, 64, 64⟩
def ilp32 : DataModel := ⟨32, 32, 32⟩

/-- `Target.DataModel` in Go: ILP32 for the microcontroller architectures,
    LP64 otherwise — the two models `92-ffi.md` §2.4 admits. -/
def dataModel (t : Target) : DataModel := if t.arch.mcu then ilp32 else lp64

theorem dataModel_lp64_or_ilp32 (t : Target) : dataModel t = lp64 ∨ dataModel t = ilp32 := by
  unfold dataModel; split <;> simp

/-- `int` is 32 bits on every target: the fixed-width rows of the FFI are
    unconditional and the `c.Int` row never moves. -/
theorem int_bits_32 (t : Target) : (dataModel t).intBits = 32 := by
  unfold dataModel; split <;> rfl

/-- Pointers are the machine word: 32 bits exactly on the microcontrollers. -/
theorem ptr_bits (t : Target) : (dataModel t).ptrBits = (if t.arch.mcu then 32 else 64) := by
  unfold dataModel; split <;> simp_all [lp64, ilp32]

theorem hosted_lp64 (t : Target) (h : supported t = true) (hos : t.os ≠ .freestanding) : dataModel t = lp64 := by
  obtain ⟨os, arch⟩ := t
  cases os <;> cases arch <;> simp_all [supported, dataModel, Arch.mcu]

/-- The assembler lane of an architecture (`Function.Arch` in Go): arm64,
    rv64, or none for amd64. -/
inductive Lane where
  | arm64 | rv64
  deriving DecidableEq, Repr

def lane : Target → Option Lane
  | ⟨_, .arm64⟩ => some .arm64
  | ⟨_, .riscv64⟩ => some .rv64
  | ⟨_, .amd64⟩ | ⟨_, .arm⟩ | ⟨_, .riscv32⟩ => none

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

/-- The processor a target compiles for when the build names none
    (`Target.DefaultCPU`): the toolchain's baseline for hosted targets, and
    for freestanding ones a processor whose defaults match the companion
    object — soft-float RISC-V, the Cortex-M4 for Arm. -/
def defaultCPU (t : Target) : Option String :=
  if t.os ≠ .freestanding then none
  else match t.arch with
    | .riscv64 => some "generic_rv64"
    | .riscv32 => some "generic_rv32"
    | .arm => some "cortex_m4"
    | _ => none

/-- The default processor of a freestanding RISC-V target is soft-float,
    which is what the companion object declares for it. -/
theorem defaultCPU_bare_rv64 : defaultCPU ⟨.freestanding, .riscv64⟩ = some "generic_rv64" ∧ rv64FloatABI ⟨.freestanding, .riscv64⟩ = .soft := ⟨rfl, rfl⟩

/-- Hosted targets take the toolchain's baseline. -/
theorem defaultCPU_hosted (t : Target) (h : t.os ≠ .freestanding) : defaultCPU t = none := by
  simp [defaultCPU, h]

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

/-! ## Running a cross build (`oak run -target`, `toolchain.ResolveEmulator`) -/

/-- What a host has for running foreign binaries: QEMU's user-mode
    emulator per architecture, or an explicit `OAK_EMULATOR`. -/
structure Runners where
  qemuUser : Arch → Bool
  explicit : Bool

/-- How `oak run` executes a program for `t` on host platform `p`:
    directly for the host target; through the explicit emulator when set;
    through user-mode QEMU for a foreign Linux target; never otherwise. -/
inductive Run where
  | direct | explicit | qemu
  deriving DecidableEq, Repr

def runWith (p : Target) (r : Runners) (t : Target) : Option Run :=
  if t = p then some .direct
  else if r.explicit then some .explicit
  else if t.os = .linux ∧ r.qemuUser t.arch then some .qemu
  else none

/-- The host target always runs, and directly. -/
theorem runWith_host (p : Target) (r : Runners) : runWith p r p = some .direct := by
  simp [runWith]

/-- Without an explicit emulator, a foreign target runs only when it is a
    Linux target with a user-mode emulator on the host: freestanding and
    Darwin cross builds are refused (fail closed). -/
theorem runWith_foreign (p : Target) (r : Runners) (t : Target) (ht : t ≠ p) (he : r.explicit = false) :
    (runWith p r t).isSome = true ↔ (t.os = .linux ∧ r.qemuUser t.arch = true) := by
  simp [runWith, ht, he]

theorem runWith_freestanding_none (p : Target) (r : Runners) (a : Arch)
    (ht : (⟨.freestanding, a⟩ : Target) ≠ p) (he : r.explicit = false) :
    runWith p r ⟨.freestanding, a⟩ = none := by
  simp [runWith, ht, he]

/-- An explicit emulator is the user's word: it runs any foreign target. -/
theorem runWith_explicit (p : Target) (r : Runners) (t : Target) (ht : t ≠ p) (he : r.explicit = true) :
    runWith p r t = some .explicit := by
  simp [runWith, ht, he]

end Oak.Target
