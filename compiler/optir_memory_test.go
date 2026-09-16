package compiler

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/optir"
)

func TestCheckedGlobalMemoryProjectsThroughDAGAndEliminatesOverwrittenStore(t *testing.T) {
	module, err := New().WithSource("optir_memory.oak", `
counter: u32 = u32(0)

replace: (x: u32): u32 {
  counter = x
  counter = x + u32(1)
  counter
}

main: (): i32 = 0
`).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	replace, ok := optIRFunction(module, "replace")
	if !ok {
		t.Fatalf("replace was not projected: %+v", module.Refusals)
	}
	if replace.CheckedMemoryHash == "" || replace.CheckedMemoryHash != replace.CheckedMemory.Fingerprint() {
		t.Fatalf("checked memory authority fingerprint = %q / %q", replace.CheckedMemoryHash, replace.CheckedMemory.Fingerprint())
	}
	regions := replace.MemoryProjection.Metadata.Regions
	if len(regions) != 1 || regions[0] == "" ||
		!reflect.DeepEqual(replace.MemoryProjection.Observability.LiveOut, []optir.RegionID{regions[0]}) {
		t.Fatalf("checked memory projection = %+v", replace.MemoryProjection)
	}
	if err := optir.VerifyCheckedMemoryProjection(replace.LoopInvariant, replace.CheckedMemory, replace.MemoryProjection); err != nil {
		t.Fatalf("checked memory projection verification: %v", err)
	}
	if len(replace.DeadStoreElimination.Removed) != 1 || replace.DeadStoreElimination.Removed[0].Region != regions[0] {
		t.Fatalf("dead-store report = %+v", replace.DeadStoreElimination)
	}
	if err := optir.VerifyDeadStoreElimination(
		replace.LoopInvariant,
		replace.MemoryProjection.Metadata,
		replace.MemorySSA,
		replace.MemoryProjection.Observability,
		replace.MemoryLiveness,
		replace.DeadStores,
		replace.DeadStoreMetadata,
		replace.DeadStoreElimination,
	); err != nil {
		t.Fatalf("dead-store verification: %v", err)
	}
	if stores, loads := countOptIRMemoryOperations(replace.LoopInvariant); stores != 2 || loads != 1 {
		t.Fatalf("pre-DSE memory operations = stores %d, loads %d", stores, loads)
	}
	if stores, loads := countOptIRMemoryOperations(replace.DeadStores); stores != 1 || loads != 1 {
		t.Fatalf("post-DSE memory operations = stores %d, loads %d", stores, loads)
	}
	projected, err := optir.ProjectCheckedMemory(replace.DeadStores, replace.CheckedMemory)
	if err != nil {
		t.Fatalf("post-DSE checked memory projection: %v", err)
	}
	if !reflect.DeepEqual(projected.Metadata, replace.DeadStoreMetadata) {
		t.Fatalf("post-DSE metadata = %+v, want %+v", projected.Metadata, replace.DeadStoreMetadata)
	}
	postDSESSA, err := optir.AnalyzeRegionMemorySSA(replace.DeadStores, projected.Metadata)
	if err != nil {
		t.Fatal(err)
	}
	if err := optir.VerifyRegionLoadForwarding(
		replace.DeadStores, projected.Metadata, postDSESSA,
		replace.ForwardedLoads, replace.ForwardedLoadMetadata, replace.RegionLoadForwarding,
	); err != nil {
		t.Fatalf("region-load forwarding verification: %v", err)
	}
	if replace.RegionLoadForwarding.Changes() != 1 || replace.RegionLoadForwarding.Replacements[0].Kind != optir.RegionLoadFromStore {
		t.Fatalf("region-load forwarding report = %+v", replace.RegionLoadForwarding)
	}
	if stores, loads := countOptIRMemoryOperations(replace.ForwardedLoads); stores != 1 || loads != 0 {
		t.Fatalf("post-forwarding memory operations = stores %d, loads %d", stores, loads)
	}
	if err := optir.VerifyCheckedMemoryProjection(replace.ForwardedLoads, replace.CheckedMemory, replace.FinalMemoryProjection); err != nil {
		t.Fatalf("final checked memory projection: %v", err)
	}
	if err := optir.VerifyRegionMemorySSA(replace.ForwardedLoads, replace.FinalMemoryProjection.Metadata, replace.FinalMemorySSA); err != nil {
		t.Fatalf("final region MemorySSA: %v", err)
	}
}

func TestCheckedGlobalMemoryKeepsBranchStoresAndAcceptsExactCallEffects(t *testing.T) {
	module, err := New().WithSource("optir_memory_branch.oak", `
flag: Bool = false
items: [2]u32

choose: (value: Bool): Bool {
  value ? {
    flag = true
  } | {
    flag = false
  }
  flag
}

read_item: (): u32 = items[u32(0)]

identity: (value: Bool): Bool = value
forward: (value: Bool): Bool = identity(value)
mixed: (value: Bool): Bool {
  flag = forward(value)
  flag
}
touch: (value: Bool): Bool {
  flag = value
  flag
}
stateful_wrapper: (value: Bool): Bool = touch(value)
stateful: (value: Bool): Bool {
  flag = stateful_wrapper(value)
  flag
}
set_flag: (value: Bool): Bool {
  flag = value
  value
}
set_wrapper: (value: Bool): Bool = set_flag(value)
set_forward: (value: Bool): Bool = set_wrapper(value)
main: (): i32 = 0
`).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	choose, ok := optIRFunction(module, "choose")
	if !ok {
		t.Fatalf("choose was not projected: %+v", module.Refusals)
	}
	if len(choose.MemoryProjection.Metadata.Operations) != 3 || len(choose.DeadStoreElimination.Removed) != 0 {
		t.Fatalf("branch memory analysis = projection %+v, DSE %+v", choose.MemoryProjection, choose.DeadStoreElimination)
	}
	if choose.RegionLoadForwarding.Changes() != 1 || choose.RegionLoadForwarding.Replacements[0].Kind != optir.RegionLoadFromPhi {
		t.Fatalf("branch memory-phi forwarding = %+v", choose.RegionLoadForwarding)
	}
	if stores, loads := countOptIRMemoryOperations(choose.ForwardedLoads); stores != 2 || loads != 0 {
		t.Fatalf("post-memory-phi operations = stores %d, loads %d", stores, loads)
	}
	if _, ok := optIRFunction(module, "read_item"); ok {
		t.Fatal("aggregate global unexpectedly entered the closed scalar memory vocabulary")
	}
	mixed, ok := optIRFunction(module, "mixed")
	if !ok {
		t.Fatalf("pure call mixed with global state was refused: %+v", module.Refusals)
	}
	calls := mixed.CheckedMemory.CallRecords()
	if len(calls) != 1 || calls[0].Callee != "forward" || calls[0].SummaryFingerprint == "" {
		t.Fatalf("mixed checked call authority = %+v", calls)
	}
	seenCall := false
	for _, block := range mixed.CFG.Blocks {
		for _, operation := range block.Operations {
			if operation.Code == optir.OpCall {
				seenCall = operation.MemoryCallID == calls[0].ID
			}
		}
	}
	if !seenCall {
		t.Fatalf("mixed CFG does not carry checked call ID %s: %#v", calls[0].ID, mixed.CFG)
	}
	seenNoModRef := false
	for _, operation := range mixed.MemoryProjection.Metadata.Operations {
		seenNoModRef = seenNoModRef || operation.CallEffect == optir.MemoryCallNoModRef
	}
	if !seenNoModRef {
		t.Fatalf("mixed memory projection has no checked no-ModRef call: %+v", mixed.MemoryProjection.Metadata)
	}
	if err := optir.VerifyCheckedMemoryProjection(mixed.LoopInvariant, mixed.CheckedMemory, mixed.MemoryProjection); err != nil {
		t.Fatalf("mixed checked memory projection: %v", err)
	}
	forward, ok := optIRFunction(module, "forward")
	if !ok || len(forward.CheckedMemory.CallRecords()) != 1 || forward.CheckedMemory.CallRecords()[0].Callee != "identity" {
		t.Fatalf("transitive pure summary was not projected: function=%+v refusals=%+v", forward, module.Refusals)
	}
	stateful, ok := optIRFunction(module, "stateful")
	if !ok {
		t.Fatalf("write-bearing call mixed with global state was refused: %+v", module.Refusals)
	}
	wrapper, ok := optIRFunction(module, "stateful_wrapper")
	if !ok {
		t.Fatalf("call-only stateful wrapper was refused: %+v", module.Refusals)
	}
	wrapperCalls := wrapper.CheckedMemory.CallRecords()
	if len(wrapper.CheckedMemory.Records()) != 0 || len(wrapperCalls) != 1 || wrapperCalls[0].Callee != "touch" || len(wrapperCalls[0].Accesses) != 1 {
		t.Fatalf("call-only stateful wrapper authority = %+v", wrapper.CheckedMemory)
	}
	stateEffect := wrapperCalls[0].Accesses[0]
	if stateEffect.Kind != optir.MemoryReadWrite || stateEffect.WholeRegion || stateEffect.Volatile {
		t.Fatalf("read/write callee effect = %+v", stateEffect)
	}
	seenModRef := false
	for _, operation := range wrapper.MemoryProjection.Metadata.Operations {
		seenModRef = seenModRef || operation.CallEffect == optir.MemoryCallModRef
	}
	if !seenModRef {
		t.Fatalf("stateful wrapper projection has no ModRef call: %+v", wrapper.MemoryProjection.Metadata)
	}
	statefulCalls := stateful.CheckedMemory.CallRecords()
	if len(statefulCalls) != 1 || !reflect.DeepEqual(statefulCalls[0].Accesses, wrapperCalls[0].Accesses) {
		t.Fatalf("transitive stateful effect = %+v, want %+v", statefulCalls, wrapperCalls[0].Accesses)
	}

	setWrapper, ok := optIRFunction(module, "set_wrapper")
	if !ok {
		t.Fatalf("write-only wrapper was refused: %+v", module.Refusals)
	}
	setCalls := setWrapper.CheckedMemory.CallRecords()
	if len(setCalls) != 1 || len(setCalls[0].Accesses) != 1 {
		t.Fatalf("write-only wrapper authority = %+v", setCalls)
	}
	write := setCalls[0].Accesses[0]
	if write.Kind != optir.MemoryWrite || write.WholeRegion || write.Volatile {
		t.Fatalf("write-only callee did not become conservative may-Mod: %+v", write)
	}
	seenMod := false
	for _, operation := range setWrapper.MemoryProjection.Metadata.Operations {
		seenMod = seenMod || operation.CallEffect == optir.MemoryCallMod
	}
	if !seenMod {
		t.Fatalf("write-only wrapper projection has no Mod call: %+v", setWrapper.MemoryProjection.Metadata)
	}
	setForward, ok := optIRFunction(module, "set_forward")
	if !ok {
		t.Fatalf("transitive write-only wrapper was refused: %+v", module.Refusals)
	}
	forwardWrites := setForward.CheckedMemory.CallRecords()
	if len(forwardWrites) != 1 || !reflect.DeepEqual(forwardWrites[0].Accesses, []optir.CheckedMemoryCallAccess{write}) {
		t.Fatalf("transitive write-only summary = %+v, want %+v", forwardWrites, write)
	}
	for _, refusal := range module.Refusals {
		if refusal.Function == "stateful" || refusal.Function == "stateful_wrapper" || refusal.Function == "set_wrapper" || refusal.Function == "set_forward" {
			t.Fatalf("representable writer was refused: %+v", refusal)
		}
	}
}

func TestCheckedGlobalMemoryAcceptsDirectAndTransitiveReaderSummaries(t *testing.T) {
	module, err := New().WithSource("optir_memory_reader.oak", `
observed: u32 = u32(7)
result: u32 = u32(0)

read_observed: (): u32 = observed
forward_read: (): u32 = read_observed()
mixed_read: (value: u32): u32 {
  result = value
  loaded: u32 = forward_read()
  result = loaded
  result
}
main: (): i32 = 0
`).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	forward, ok := optIRFunction(module, "forward_read")
	if !ok {
		t.Fatalf("call-only reader was refused: %+v", module.Refusals)
	}
	forwardCalls := forward.CheckedMemory.CallRecords()
	if len(forwardCalls) != 1 || forwardCalls[0].Callee != "read_observed" || len(forwardCalls[0].Accesses) != 1 {
		t.Fatalf("direct reader summary = %+v", forwardCalls)
	}
	read := forwardCalls[0].Accesses[0]
	if read.Region == "" || read.Kind != optir.MemoryRead || read.ValueType != "u32" || read.WholeRegion || read.Volatile {
		t.Fatalf("direct reader access = %+v", read)
	}
	if !forward.CheckedMemory.HasMemoryEffects() || len(forward.MemoryProjection.Metadata.Regions) != 1 {
		t.Fatalf("call-only Ref authority skipped memory artifacts: authority=%+v projection=%+v", forward.CheckedMemory, forward.MemoryProjection)
	}
	seenRef := false
	for _, operation := range forward.MemoryProjection.Metadata.Operations {
		seenRef = seenRef || operation.CallEffect == optir.MemoryCallRef
	}
	if !seenRef {
		t.Fatalf("call-only reader projection has no Ref operation: %+v", forward.MemoryProjection.Metadata)
	}

	mixed, ok := optIRFunction(module, "mixed_read")
	if !ok {
		t.Fatalf("transitive reader mixed with global memory was refused: %+v", module.Refusals)
	}
	mixedCalls := mixed.CheckedMemory.CallRecords()
	if len(mixedCalls) != 1 || mixedCalls[0].Callee != "forward_read" ||
		!reflect.DeepEqual(mixedCalls[0].Accesses, []optir.CheckedMemoryCallAccess{read}) {
		t.Fatalf("transitive reader summary = %+v, want access %+v", mixedCalls, read)
	}
	if mixedCalls[0].SummaryFingerprint == "" || mixedCalls[0].SummaryFingerprint == forwardCalls[0].SummaryFingerprint {
		t.Fatalf("transitive summary did not bind its own CFG and child: direct=%q transitive=%q", forwardCalls[0].SummaryFingerprint, mixedCalls[0].SummaryFingerprint)
	}
	derived, err := optir.DeriveCheckedMemoryCallSummary(forward.CFG, forward.CheckedMemory)
	if err != nil || derived.Fingerprint() != mixedCalls[0].SummaryFingerprint ||
		!reflect.DeepEqual(derived.Accesses(), []optir.CheckedMemoryCallAccess{read}) {
		t.Fatalf("transitive summary = fingerprint %q, accesses %+v, err=%v; want %q / %+v",
			derived.Fingerprint(), derived.Accesses(), err, mixedCalls[0].SummaryFingerprint, read)
	}
	if err := optir.VerifyCheckedMemoryProjection(mixed.LoopInvariant, mixed.CheckedMemory, mixed.MemoryProjection); err != nil {
		t.Fatalf("transitive reader checked projection: %v", err)
	}
}

func TestCheckedPureCallSummaryFingerprintBindsCalleeCFG(t *testing.T) {
	summary := func(body string) string {
		t.Helper()
		module, err := New().WithSource("optir_call_fingerprint.oak", `
flag: Bool = false
identity: (value: Bool): Bool = `+body+`
mixed: (value: Bool): Bool {
  flag = identity(value)
  flag
}
main: (): i32 = 0
`).OptIR().Get()
		if err != nil {
			t.Fatal(err)
		}
		mixed, ok := optIRFunction(module, "mixed")
		if !ok {
			t.Fatalf("mixed was refused: %+v", module.Refusals)
		}
		records := mixed.CheckedMemory.CallRecords()
		if len(records) != 1 {
			t.Fatalf("checked call records = %+v", records)
		}
		return records[0].SummaryFingerprint
	}
	first := summary("value")
	if again := summary("value"); first == "" || again != first {
		t.Fatalf("pure summary fingerprint is not deterministic: %q / %q", first, again)
	}
	if changed := summary("value == true"); changed == first {
		t.Fatalf("callee CFG change retained pure summary fingerprint %q", first)
	}
}

func TestCheckedMemoryCallCertificateExcludesUnrelatedCachedProjection(t *testing.T) {
	model, err := New().WithSource("optir_call_certificate.oak", `
observed: u32 = u32(7)
other: u32 = u32(9)
read_observed: (): u32 = observed
root: (): u32 = read_observed()
unrelated: (): u32 = other
main: (): i32 = 0
`).Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	globals := checkedOptIRGlobals(model.Tree.Root, model.TypeChecker)
	planner := newOptIRCallEffectPlanner(model.Tree.Root, model.TypeChecker, globals)
	if _, err := planner.lower(planner.functions["unrelated"]); err != nil {
		t.Fatalf("cache unrelated projection: %v", err)
	}
	root, err := planner.lower(planner.functions["root"])
	if err != nil {
		t.Fatalf("lower certificate root: %v", err)
	}
	certificate, err := planner.memoryCallCertificate("root", root.cfg, root.memory)
	if err != nil {
		t.Fatalf("reachable-only certificate: %v", err)
	}
	if certificate.Fingerprint() == "" {
		t.Fatal("reachable-only certificate has no fingerprint")
	}
	if err := optir.VerifyCheckedMemoryCallCertificate("root", root.cfg, root.memory, certificate); err != nil {
		t.Fatalf("verify reachable-only certificate: %v", err)
	}
}

func TestCheckedCallEffectSummaryRefusesRecursiveSCC(t *testing.T) {
	module, err := New().WithSource("optir_recursive_call.oak", `
flag: Bool = false
first: (value: Bool): Bool = second(value)
second: (value: Bool): Bool = first(value)
mixed: (value: Bool): Bool {
  flag = first(value)
  flag
}
main: (): i32 = 0
`).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	if _, ok := optIRFunction(module, "mixed"); ok {
		t.Fatal("recursive call SCC unexpectedly received a checked call-effect summary")
	}
	found := false
	for _, refusal := range module.Refusals {
		if refusal.Function == "mixed" && strings.Contains(refusal.Reason, "recursive call cycle") {
			found = true
		}
	}
	if !found {
		t.Fatalf("recursive SCC refusal = %+v", module.Refusals)
	}
}

func countOptIRMemoryOperations(cfg optir.CFG) (stores, loads int) {
	for _, block := range cfg.Blocks {
		for _, operation := range block.Operations {
			switch operation.Code {
			case optir.OpStoreRegion:
				stores++
			case optir.OpLoadRegion:
				loads++
			}
		}
	}
	return stores, loads
}
