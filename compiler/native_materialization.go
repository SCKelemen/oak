package compiler

import (
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"hash"
	"sort"
	"strconv"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/optir"
)

// MaterializationKey identifies every input the native Driver's Materialize
// method reads before a body exists. It is deliberately independent of the
// eventual assembly: the artifact graph needs this recipe key to schedule the
// lowering that produces that assembly.
func (d *nativeDriver) MaterializationKey(candidate *opt.Candidate) (string, error) {
	lane, ok := candidate.Config.(nativegen.Lane)
	if !ok {
		return "", fmt.Errorf("compiler: native materialization has configuration %T, expected nativegen.Lane", candidate.Config)
	}
	digest := sha256.New()
	// v25 adds verifier-gated narrow scalar-global mask elision to v24's
	// composed late-machine recipe. Preserve every recipe input to avoid
	// reusing another candidate's body.
	writeNativeMaterializationPart(digest, "oak.native.materialization.v25")
	writeNativeLane(digest, lane)
	if d.source == nil {
		writeNativeMaterializationPart(digest, "source:nil")
	} else {
		writeNativeMaterializationPart(digest, "source", d.source.String())
	}
	writeNativeFunctions(digest, d.functions)
	writeNativeRecords(digest, d.records)
	writeNativeADTs(digest, d.adts)
	writeNativeConstants(digest, d.constants)
	writeNativeMaterializationPart(digest, "declarations", d.declarations)
	fingerprint := d.tcFingerprint
	if fingerprint == "" {
		fingerprint = d.tc.NativeLoweringFingerprint()
	}
	writeNativeMaterializationPart(digest, "typechecker", fingerprint)
	return hex.EncodeToString(digest.Sum(nil)), nil
}

func writeNativeLane(digest hash.Hash, lane nativegen.Lane) {
	writeNativeMaterializationPart(digest, "lane", lane.Arch)
	flags := []struct {
		name    string
		enabled bool
	}{
		{"vector-reductions", lane.VectorReductions},
		{"vector-maps", lane.VectorMaps},
		{"unroll-vector-maps", lane.UnrollVectorMaps},
		{"unroll-fills", lane.UnrollFills},
		{"vector-folds", lane.VectorFolds},
		{"unroll-constant", lane.UnrollConstant},
		{"unroll-small", lane.UnrollSmall},
		{"use-optir", lane.UseOptIR},
		{"no-reductions", lane.NoReductions},
		{"hoist-invariants", lane.HoistInvariants},
		{"soft-float", lane.SoftFloat},
		{"elide-proven", lane.ElideProven},
		{"reuse-flags", lane.ReuseFlags},
		{"rotate-loops", lane.RotateLoops},
		{"carry-loop-indices", lane.CarryLoopIndices},
		{"elide-redundant-guards", lane.ElideRedundantGuards},
		{"strength", lane.Strength},
		{"vector-homes", lane.VectorHomes},
		{"loop-array-homes", lane.LoopArrayHomes},
		{"loop-result-homes", lane.LoopResultHomes},
		{"share-record-bases", lane.ShareRecordBases},
		{"share-global-addresses", lane.ShareGlobalAddresses},
		{"forward-global-loads", lane.ForwardGlobalLoads},
		{"elide-global-load-masks", lane.ElideGlobalLoadMasks},
		{"vector-blocks", lane.VectorBlocks},
		{"share-vector-addresses", lane.ShareVectorAddresses},
		{"multiply-add", lane.MultiplyAdd},
		{"value-select", lane.ValueSelect},
		{"fuse", lane.Fuse},
		{"fuse-exits", lane.FuseExits},
		{"cleanup", lane.Cleanup},
		{"vector", lane.Vector},
		{"reallocate", lane.Reallocate},
		{"schedule", lane.Schedule},
		{"fuse", lane.Fuse},
		{"fuse-exits", lane.FuseExits},
		{"packed-stack-args", lane.PackedStackArgs},
	}
	for _, flag := range flags {
		writeNativeMaterializationPart(digest, flag.name, strconv.FormatBool(flag.enabled))
	}
	writeNativeMaterializationPart(digest, "optir-fingerprint", lane.OptIRFingerprint, "optir-changes", strconv.Itoa(lane.OptIRChanges))
	writeNativeMaterializationPart(digest, "optir-memory", strconv.FormatBool(lane.OptIRMemory != nil))
	if lane.OptIRMemoryAuthority == nil {
		writeNativeMaterializationPart(digest, "optir-memory-authority:nil")
	} else {
		writeNativeMaterializationPart(digest, "optir-memory-authority", lane.OptIRMemoryAuthority.Fingerprint())
	}
	if lane.OptIRMemoryProjection == nil {
		writeNativeMaterializationPart(digest, "optir-memory-projection:nil")
	} else {
		writeNativeMaterializationPart(digest, "optir-memory-projection", lane.OptIRMemoryProjection.Fingerprint())
	}
	if lane.OptIRMemoryCallCertificate == nil {
		writeNativeMaterializationPart(digest, "optir-memory-call-certificate:nil")
	} else {
		writeNativeMaterializationPart(digest, "optir-memory-call-certificate", lane.OptIRMemoryCallCertificate.Fingerprint())
	}
	regionIDs := make([]string, 0, len(lane.OptIRRegionGlobals))
	for region := range lane.OptIRRegionGlobals {
		regionIDs = append(regionIDs, string(region))
	}
	sort.Strings(regionIDs)
	writeNativeMaterializationPart(digest, "optir-region-globals", strconv.Itoa(len(regionIDs)))
	for _, regionID := range regionIDs {
		binding := lane.OptIRRegionGlobals[optir.RegionID(regionID)]
		writeNativeMaterializationPart(digest, regionID, binding.Symbol, binding.Global.Type,
			strconv.Itoa(binding.Global.Bits), strconv.FormatBool(binding.Global.Aggregate), strconv.FormatInt(binding.Global.Size, 10))
	}

	lines := make([]int, 0, len(lane.GuardLines))
	for line := range lane.GuardLines {
		lines = append(lines, line)
	}
	sort.Ints(lines)
	writeNativeMaterializationPart(digest, "guard-lines", strconv.Itoa(len(lines)))
	for _, line := range lines {
		writeNativeMaterializationPart(digest, strconv.Itoa(line), strconv.FormatBool(lane.GuardLines[line]))
	}

	globalNames := nativeMaterializationNames(lane.Globals)
	writeNativeMaterializationPart(digest, "globals", strconv.Itoa(len(globalNames)))
	for _, name := range globalNames {
		global := lane.Globals[name]
		writeNativeMaterializationPart(digest, name, global.Type, strconv.Itoa(global.Bits), strconv.FormatBool(global.Aggregate), strconv.FormatInt(global.Size, 10))
	}
	aggregateNames := nativeMaterializationNames(lane.Aggregates)
	writeNativeMaterializationPart(digest, "aggregates", strconv.Itoa(len(aggregateNames)))
	for _, name := range aggregateNames {
		declaration := lane.Aggregates[name]
		value := "<nil>"
		if declaration != nil {
			value = declaration.String()
		}
		writeNativeMaterializationPart(digest, name, value)
	}
	tableNames := nativeMaterializationNames(lane.Tables)
	writeNativeMaterializationPart(digest, "tables", strconv.Itoa(len(tableNames)))
	for _, name := range tableNames {
		table := lane.Tables[name]
		writeNativeMaterializationPart(digest, name, table.Symbol, table.Elem, strconv.FormatInt(table.Length, 10))
	}
}

func writeNativeFunctions(digest hash.Hash, functions map[string]*ast.FunctionStatement) {
	names := nativeMaterializationNames(functions)
	writeNativeMaterializationPart(digest, "functions", strconv.Itoa(len(names)))
	for _, name := range names {
		function := functions[name]
		value := "<nil>"
		if function != nil {
			value = function.String()
		}
		writeNativeMaterializationPart(digest, name, value)
	}
}

func writeNativeRecords(digest hash.Hash, records map[string]*ast.RecordLiteral) {
	names := nativeMaterializationNames(records)
	writeNativeMaterializationPart(digest, "records", strconv.Itoa(len(names)))
	for _, name := range names {
		record := records[name]
		value := "<nil>"
		if record != nil {
			value = record.String()
		}
		writeNativeMaterializationPart(digest, name, value)
	}
}

func writeNativeADTs(digest hash.Hash, adts map[string]*ast.ADTType) {
	names := nativeMaterializationNames(adts)
	writeNativeMaterializationPart(digest, "adts", strconv.Itoa(len(names)))
	for _, name := range names {
		adt := adts[name]
		value := "<nil>"
		if adt != nil {
			value = adt.String()
		}
		writeNativeMaterializationPart(digest, name, value)
	}
}

func writeNativeConstants(digest hash.Hash, constants map[string]asm.Constant) {
	names := nativeMaterializationNames(constants)
	writeNativeMaterializationPart(digest, "constants", strconv.Itoa(len(names)))
	for _, name := range names {
		constant := constants[name]
		writeNativeMaterializationPart(digest, name, constant.Type, strconv.FormatUint(constant.Value, 10))
	}
}

func nativeMaterializationNames[T any](values map[string]T) []string {
	names := make([]string, 0, len(values))
	for name := range values {
		names = append(names, name)
	}
	sort.Strings(names)
	return names
}

func writeNativeMaterializationPart(digest hash.Hash, values ...string) {
	for _, value := range values {
		var length [8]byte
		binary.BigEndian.PutUint64(length[:], uint64(len(value)))
		_, _ = digest.Write(length[:])
		_, _ = digest.Write([]byte(value))
	}
}
