package semir

// CPUFeature is one processor feature a program may dispatch on
// (docs/spec/93-simd.md section 6; docs/notes/cpu-dispatch-design-2026-09.md).
// A feature is tied to an architecture: a `dispatch` slot for another
// architecture is inert on this target. The catalog is closed; adding a
// feature is a language change reviewed with its probe.
type CPUFeature struct {
	// Name is the slot spelling in a dispatch clause: `sve`, `sve2`, `rvv`.
	Name string
	// Arch is the target architecture the feature belongs to (target.Arch*).
	Arch string
	// BaselineMacro is the C preprocessor macro the C compiler defines when
	// the build's -cpu already guarantees the feature: the dispatched
	// function is then the realization outright (the static rule).
	BaselineMacro string
	// Attribute is the function attribute that enables the feature for one
	// function in a translation unit compiled at the baseline.
	Attribute string
	// Bit is the feature's position in the probed word oak_cpu_features.
	Bit uint
	// Mode names the lowering mode a realization is emitted in (the
	// scalable API's helper and type suffix); empty for features that
	// change no lowering.
	Mode string
}

// Macro is the C spelling of the feature's bit.
func (f CPUFeature) Macro() string { return "OAK_CPU_" + upper(f.Name) }

func upper(s string) string {
	b := []byte(s)
	for i, c := range b {
		if 'a' <= c && c <= 'z' {
			b[i] = c - 'a' + 'A'
		}
	}
	return string(b)
}

var cpuFeatures = [...]CPUFeature{
	{Name: "sve", Arch: "arm64", BaselineMacro: "__ARM_FEATURE_SVE", Attribute: `__attribute__((target("sve")))`, Bit: 0, Mode: "sve"},
	{Name: "sve2", Arch: "arm64", BaselineMacro: "__ARM_FEATURE_SVE2", Attribute: `__attribute__((target("sve2")))`, Bit: 1, Mode: "sve"},
	{Name: "rvv", Arch: "riscv64", BaselineMacro: "__riscv_vector", Attribute: `__attribute__((target("arch=+v")))`, Bit: 2, Mode: "rvv"},
}

// CPUFeatures returns the fixed catalog by value.
func CPUFeatures() [len(cpuFeatures)]CPUFeature { return cpuFeatures }

// LookupCPUFeature finds a feature by its slot spelling.
func LookupCPUFeature(name string) (CPUFeature, bool) {
	for i := range cpuFeatures {
		if cpuFeatures[i].Name == name {
			return cpuFeatures[i], true
		}
	}
	return CPUFeature{}, false
}
