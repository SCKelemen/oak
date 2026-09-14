package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

func TestZZProbeTrusted(t *testing.T) {
	programs := map[string]string{"native": nativeProgram, "spans": nativeSpanProgram, "floats": nativeFloatProgram, "simd": nativeSimdProgram, "floatsimd": nativeFloatSimdProgram, "arrays": nativeArrayProgram, "rv64simd": nativeRV64SimdProgram, "rv64floatsimd": nativeRV64FloatSimdProgram, "adt": nativeADTProgram, "compound": nativeCompoundProgram, "nested": nativeNestedProgram, "record": nativeRecordProgram, "recordarray": nativeRecordArrayProgram, "recordinplace": nativeRecordInPlaceProgram, "recordspan": nativeRecordSpanProgram, "spancall": nativeSpanCallProgram, "spaneffects": nativeSpanEffectsProgram, "stackargs": nativeStackArgsProgram, "stride": nativeStrideProgram, "subslice": nativeSubsliceProgram, "globals": nativeGlobalsProgram, "globalagg": nativeGlobalAggregatesProgram, "calleeeffects": nativeCalleeEffectsProgram, "callsummary": nativeCallSummaryProgram, "loopheader": nativeLoopHeaderLoadsProgram, "statements": nativeStatementShapesProgram, "tables": nativeTablesProgram, "generic": nativeGenericProgram, "leaf": nativeLeafProgram, "atomics": nativeAtomicsProgram}
	for name, src := range programs {
		for _, tgt := range []target.Target{{OS: target.OSDarwin, Arch: target.ArchArm64}, {OS: target.OSLinux, Arch: target.ArchRiscv64}} {
			var infos []string
			comp := New().WithSource("p.oak", src).WithNativeBodies().WithNativeAsm().WithTarget(tgt).WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
				if d.Source == "native" && strings.Contains(d.Message, "not verified") {
					infos = append(infos, d.Message)
				}
			})
			if _, err := comp.EmitNative(ObjectFormat(tgt)).Get(); err != nil {
				t.Logf("%s %s: %v", name, tgt.Arch, err)
				continue
			}
			for _, m := range infos {
				t.Logf("%s %s: %s", name, tgt.Arch, m)
			}
		}
	}
}
