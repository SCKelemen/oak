package nativegen

import (
	"reflect"
	"runtime"
	"sync"
	"testing"
	"time"
	"weak"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/machine"
	"github.com/SCKelemen/oak/optir"
)

// All public counter readers must keep the exact per-function values: these
// counts also decide whether candidate transforms fired and which passes run.
func TestLoweringMetadataReadersAndCopyBoundary(t *testing.T) {
	fn := &asm.Function{}
	metadata := editLoweringMetadata(fn)
	metadata.carriedLoopIndices = 1
	metadata.cleanedCopies = 2
	metadata.sharedGlobalAddresses = 3
	metadata.forwardedGlobalLoads = 4
	metadata.elidedGlobalLoadMasks = 5
	metadata.loopArrayHomesOf = 6
	metadata.loopResultHomesOf = 7
	metadata.fusedMultiplies = 8
	metadata.scheduledOf = 9
	metadata.fusedOf = 10
	metadata.fusedExitsOf = 11
	metadata.evictedLeafCalleeSaves = 12
	metadata.retainedCalleeSaveCarriers = 13
	metadata.trimmedCalleeSaves = 14
	metadata.elidedEmptyFrames = 15
	metadata.optIRLowered = 16
	metadata.reallocated = 17
	metadata.promotedSlots = 18
	metadata.elidedGuards = 19
	metadata.reusedCompares = 20
	metadata.hoistedLoops = 21
	metadata.rotatedLoops = 22
	metadata.reducedOps = 23
	metadata.vectorHomesOf = 24
	metadata.leafVectorHomesOf = 25
	metadata.rotatedOps = 26
	metadata.postScheduledCleanup = 27
	metadata.sharedRecordBases = 28
	metadata.reusedRecordBaseDestinations = 29
	metadata.reusedRemainingRecordBaseDestinations = 30
	metadata.rescheduledRecordBaseCarriers = 31
	metadata.redundantGuards = 32
	metadata.valueSelects = 33
	metadata.fusedVectorBlocks = 34
	metadata.sharedVectorAddressCount = 35
	metadata.pressured = true
	metadata.rewriteSitesOf = []RewriteSite{{Rewrite: "strength reduction", Decided: true, Line: 7}}
	recordFrameObjects(fn, []machine.FrameObject{{Offset: 8, Size: 32, Name: "local", Elem: 4}}, 16)
	readers := []struct {
		name string
		read func(*asm.Function) int
		want int
	}{
		{"CarriedLoopIndices", CarriedLoopIndices, 1},
		{"CleanedCopies", CleanedCopies, 2},
		{"SharedGlobalAddresses", SharedGlobalAddresses, 3},
		{"ForwardedGlobalLoads", ForwardedGlobalLoads, 4},
		{"ElidedGlobalLoadMasks", ElidedGlobalLoadMasks, 5},
		{"LoopArrayHomes", LoopArrayHomes, 6},
		{"LoopResultHomes", LoopResultHomes, 7},
		{"FusedMultiplies", FusedMultiplies, 8},
		{"Scheduled", Scheduled, 9},
		{"Fused", Fused, 10},
		{"FusedExits", FusedExits, 11},
		{"EvictedLeafCalleeSaves", EvictedLeafCalleeSaves, 12},
		{"RetainedCalleeSaveCarriers", RetainedCalleeSaveCarriers, 13},
		{"TrimmedCalleeSaves", TrimmedCalleeSaves, 14},
		{"ElidedEmptyFrames", ElidedEmptyFrames, 15},
		{"OptIRLowered", OptIRLowered, 16},
		{"Reallocated", Reallocated, 17},
		{"PromotedSlots", PromotedSlots, 18},
		{"ElidedGuards", ElidedGuards, 19},
		{"ReusedCompares", ReusedCompares, 20},
		{"Hoisted", Hoisted, 21},
		{"RotatedLoops", RotatedLoops, 22},
		{"Reduced", Reduced, 23},
		{"VectorHomes", VectorHomes, 24},
		{"LeafVectorHomes", LeafVectorHomes, 25},
		{"Rotated", Rotated, 26},
		{"PostScheduledCleanup", PostScheduledCleanup, 27},
		{"SharedRecordBases", SharedRecordBases, 28},
		{"ReusedRecordBaseDestinations", ReusedRecordBaseDestinations, 29},
		{"ReusedRemainingRecordBaseDestinations", ReusedRemainingRecordBaseDestinations, 30},
		{"RescheduledRecordBaseCarriers", RescheduledRecordBaseCarriers, 31},
		{"ElidedRedundantGuards", ElidedRedundantGuards, 32},
		{"ValueSelects", ValueSelects, 33},
		{"FusedVectorBlocks", FusedVectorBlocks, 34},
		{"SharedVectorAddresses", SharedVectorAddresses, 35},
	}
	copy := *fn
	unknown := &asm.Function{}
	for _, reader := range readers {
		if got := reader.read(fn); got != reader.want {
			t.Errorf("%s = %d, want %d", reader.name, got, reader.want)
		}
		for _, absent := range []*asm.Function{nil, unknown, &copy} {
			if got := reader.read(absent); got != 0 {
				t.Errorf("%s on absent/copied metadata = %d", reader.name, got)
			}
		}
	}
	if got := FrameObjects(fn); !reflect.DeepEqual(got, []machine.FrameObject{{Offset: 24, Size: 32, Name: "local", Elem: 4}}) || !reflect.DeepEqual(got, fn.FrameObjects) {
		t.Fatalf("live allocation/verifier frame objects changed: %+v", got)
	}
	if StrengthReduced(fn) != 1 || len(RewriteSites(fn)) != 1 || !readLoweringMetadata(fn).pressured {
		t.Fatal("live rewrite or pressure metadata was lost")
	}
	for _, absent := range []*asm.Function{nil, unknown, &copy} {
		if FrameObjects(absent) != nil || RewriteSites(absent) != nil || StrengthReduced(absent) != 0 || readLoweringMetadata(absent).pressured {
			t.Fatal("slice/rewrite/pressure metadata crossed a function identity boundary")
		}
	}
	if &FrameObjects(fn)[0] != &fn.FrameObjects[0] || &RewriteSites(fn)[0] != &metadata.rewriteSitesOf[0] {
		t.Fatal("live readers changed the existing slice-sharing contract")
	}
	if unknown.LoweringMetadata != nil || copy.LoweringMetadata != fn.LoweringMetadata {
		t.Fatal("reading absent/copied metadata mutated the function")
	}
	editLoweringMetadata(&copy).optIRLowered = 101
	if OptIRLowered(&copy) != 101 || OptIRLowered(fn) != metadata.optIRLowered || FrameObjects(&copy) != nil || RewriteSites(&copy) != nil {
		t.Fatal("writing a copied function inherited or changed its parent's metadata")
	}
}

func TestLoweringMetadataRewriteReaders(t *testing.T) {
	fn := &asm.Function{}
	readers := []struct {
		name string
		read func(*asm.Function) int
	}{
		{"reduction unrolling", Unrolled},
		{"fill unrolling", UnrolledFills},
		{"reduction vectorization", Vectorized},
		{"map vectorization", VectorizedMaps},
		{"map unrolling", UnrolledMaps},
		{"fold vectorization", VectorizedFolds},
		{"fold unrolling", UnrolledFolds},
		{"lane vectorization", VectorizedLanes},
		{"constant unrolling", UnrolledConstant},
		{"small constant unrolling", UnrolledSmall},
		{"strength reduction", StrengthReduced},
	}
	metadata := editLoweringMetadata(fn)
	for index, reader := range readers {
		for range index + 1 {
			metadata.rewriteSitesOf = append(metadata.rewriteSitesOf, RewriteSite{Rewrite: reader.name, Decided: true})
		}
	}
	metadata.rewriteSitesOf = append(metadata.rewriteSitesOf, RewriteSite{Rewrite: "strength reduction", Decided: false})
	copy := *fn
	for index, reader := range readers {
		if got := reader.read(fn); got != index+1 {
			t.Errorf("%s = %d, want %d", reader.name, got, index+1)
		}
		if reader.read(nil) != 0 || reader.read(&copy) != 0 {
			t.Errorf("%s crossed the function identity boundary", reader.name)
		}
	}
}

func TestLoweringMetadataMachineCopies(t *testing.T) {
	fn, functions, _, tc := checkedFillFunction(t, "calc: (x: u32): u32 = x + u32(1)", "calc")
	for _, arch := range []string{asm.ArchArm64, asm.ArchRV64} {
		t.Run(arch, func(t *testing.T) {
			original, err := CompileFor(Lane{Arch: arch, NoReductions: true}, fn, functions, nil, nil, nil, tc)
			if err != nil {
				t.Fatal(err)
			}
			editLoweringMetadata(original).scheduledOf = 17
			var cache machine.ReallocationCache
			for _, pass := range []struct {
				name string
				run  func() (*asm.Function, error)
			}{
				{"schedule", func() (*asm.Function, error) { out, _, err := machine.Schedule(original); return out, err }},
				{"fuse", func() (*asm.Function, error) { out, _, err := machine.Fuse(original); return out, err }},
				{"allocation-miss", func() (*asm.Function, error) {
					out, _, err := cache.Apply(original, FrameObjects(original))
					return out, err
				}},
				{"allocation-hit", func() (*asm.Function, error) {
					out, _, err := cache.Apply(original, FrameObjects(original))
					return out, err
				}},
			} {
				t.Run(pass.name, func(t *testing.T) {
					out, err := pass.run()
					if err != nil {
						t.Fatal(err)
					}
					if out == original || Scheduled(out) != 0 || FrameObjects(out) != nil || RewriteSites(out) != nil {
						t.Fatal("machine output inherited its input's nativegen metadata")
					}
					editLoweringMetadata(out).scheduledOf = 29
					if Scheduled(original) != 17 {
						t.Fatal("machine output changed input metadata")
					}
				})
			}
			if cache.Stats().Hits != 1 {
				t.Fatalf("cache hit path not exercised: %+v", cache.Stats())
			}
		})
	}
}

func TestLoweringMetadataOptIRFrameBoundary(t *testing.T) {
	fn, functions, _, tc := checkedFillFunction(t, "calc: (x: u32): u32 = x", "calc")
	cfg := optir.CFG{Name: "calc", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID: 0, Parameters: []optir.Value{{ID: 1, Type: "u32", Name: "x"}},
		Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}},
	}}}
	for _, arch := range []string{asm.ArchArm64, asm.ArchRV64} {
		t.Run(arch, func(t *testing.T) {
			template, err := CompileFor(Lane{Arch: arch, NoReductions: true}, fn, functions, nil, nil, nil, tc)
			if err != nil {
				t.Fatal(err)
			}
			// Deliberately outside the selector's new frame. The assembler field
			// is copied as before, but it must never become allocation authority.
			recordFrameObjects(template, []machine.FrameObject{{Offset: 4096, Size: 64, Name: "template", Elem: 4}}, 0)
			editLoweringMetadata(template).reallocated = 73
			var out *asm.Function
			if arch == asm.ArchArm64 {
				out, err = machine.LowerOptIRArm64(cfg, template)
			} else {
				out, err = machine.LowerOptIRRV64(cfg, template)
			}
			if err != nil {
				t.Fatal(err)
			}
			if !reflect.DeepEqual(out.FrameObjects, template.FrameObjects) || FrameObjects(out) != nil || Reallocated(out) != 0 {
				t.Fatal("OptIR selector changed the established template metadata boundary")
			}
			editLoweringMetadata(out).optIRLowered = 3
			if FrameObjects(out) != nil || OptIRLowered(out) != 3 || Reallocated(template) != 73 {
				t.Fatal("fresh OptIR metadata inherited stale template frame offsets")
			}
			want, summary, err := (*machine.ReallocationCache)(nil).Apply(out, nil)
			if err != nil {
				t.Fatal(err)
			}
			if err := (*CompileSession)(nil).reallocate(out, false); err != nil {
				t.Fatal(err)
			}
			if !reflect.DeepEqual(out.Items, want.Items) || !reflect.DeepEqual(out.Clobbers, want.Clobbers) || Reallocated(out) != summary.Sites || PromotedSlots(out) != summary.Promoted {
				t.Fatal("OptIR reallocation differs from the historical nil-object input")
			}
			if findings := asm.Check(out, fn, map[string]bool{"calc": true}); len(findings) != 0 {
				t.Fatal(findings)
			}
			if verdict := asm.Verify(out, fn, fn.Body); verdict.Kind != asm.VerdictProven {
				t.Fatalf("OptIR verdict: %s", verdict.Message)
			}
		})
	}
}

// A retained machine copy must not keep its template alive via opaque metadata.
func TestLoweringMetadataCopiedOwnerCollectible(t *testing.T) {
	finalized := make(chan struct{}, 1)
	copy := loweringMetadataFinalizedCopy(finalized)
	awaitLoweringMetadataFinalizers(t, finalized, 1)
	if Scheduled(copy) != 0 || FrameObjects(copy) != nil {
		t.Fatal("collected owner metadata became visible on a copy")
	}
	metadata := copy.LoweringMetadata.(*loweringMetadata)
	if metadata.owner.Value() != nil {
		t.Fatal("finalized owner retained a live weak identity")
	}
	// A retained opaque record cannot acquire a new owner after collection.
	// weak.Pointer identifies the allocation, even if its address is reused.
	for range 256 {
		fresh := &asm.Function{LoweringMetadata: metadata}
		if Scheduled(fresh) != 0 {
			t.Fatal("collected metadata rebound to a new function")
		}
		editLoweringMetadata(fresh).scheduledOf = 31
		if Scheduled(fresh) != 31 || metadata.owner.Value() != nil {
			t.Fatal("fresh metadata resurrected its old owner")
		}
	}
	runtime.KeepAlive(copy)
}

//go:noinline
func loweringMetadataFinalizedCopy(finalized chan<- struct{}) *asm.Function {
	fn := &asm.Function{}
	editLoweringMetadata(fn).scheduledOf = 23
	runtime.SetFinalizer(fn, func(*asm.Function) { finalized <- struct{}{} })
	copy := *fn
	return &copy
}

func TestLoweringMetadataDiscardedCompilationsCollectible(t *testing.T) {
	fn, functions, records, tc := checkedFillFunction(t, "calc: (x: u32, y: u32): u32 = x + y", "calc")
	var session CompileSession
	lane := Lane{Arch: asm.ArchArm64, NoReductions: true, Reallocate: true, Schedule: true, Cleanup: true}
	live, err := session.CompileFor(lane, fn, functions, records, nil, nil, tc)
	if err != nil {
		t.Fatal(err)
	}
	before := metadataComparable(*readLoweringMetadata(live))
	assembly := Describe(live)
	const count = 24
	finalized := make(chan struct{}, count)
	for range count {
		out, err := session.CompileFor(lane, fn, functions, records, nil, nil, tc)
		if err != nil {
			t.Fatal(err)
		}
		runtime.SetFinalizer(out, func(*asm.Function) { finalized <- struct{}{} })
	}
	awaitLoweringMetadataFinalizers(t, finalized, count)
	if !reflect.DeepEqual(before, metadataComparable(*readLoweringMetadata(live))) || Describe(live) != assembly {
		t.Fatal("collecting discarded candidates changed a live candidate")
	}
	if findings := asm.Check(live, fn, map[string]bool{"calc": true}); len(findings) != 0 {
		t.Fatal(findings)
	}
	if verdict := asm.Verify(live, fn, fn.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("live verdict after collection: %s", verdict.Message)
	}
	if stats := session.ReallocationStats(); stats.Requests != count+1 || stats.Hits != count {
		t.Fatalf("session did not remain live: %+v", stats)
	}
	runtime.KeepAlive(live)
}

func awaitLoweringMetadataFinalizers(t *testing.T, finalized <-chan struct{}, count int) {
	t.Helper()
	deadline := time.Now().Add(5 * time.Second)
	for remaining := count; remaining > 0; {
		runtime.GC()
		select {
		case <-finalized:
			remaining--
		case <-time.After(10 * time.Millisecond):
			if time.Now().After(deadline) {
				t.Fatalf("%d of %d discarded functions remained reachable", remaining, count)
			}
		}
	}
}

func TestLoweringMetadataConcurrentCandidates(t *testing.T) {
	fn, functions, records, tc := checkedFillFunction(t, "calc: (x: u32, y: u32): u32 = x + y", "calc")
	var group sync.WaitGroup
	for worker := range 8 {
		group.Go(func() {
			var session CompileSession
			for range 8 {
				lane := Lane{Arch: asm.ArchArm64, NoReductions: true, Reallocate: true, Cleanup: true, Schedule: worker%2 == 0}
				out, err := session.CompileFor(lane, fn, functions, records, nil, nil, tc)
				if err != nil {
					t.Error(err)
					return
				}
				before := metadataComparable(*readLoweringMetadata(out))
				copy := *out
				editLoweringMetadata(&copy).scheduledOf = worker + 100
				if !reflect.DeepEqual(before, metadataComparable(*readLoweringMetadata(out))) || Scheduled(&copy) != worker+100 {
					t.Error("independent candidate changed another candidate's metadata")
					return
				}
				// Concurrent readers of one completed function must not initialize
				// or mutate anything, including when metadata is absent.
				var readers sync.WaitGroup
				for range 2 {
					readers.Go(func() { _ = Scheduled(out); _ = FrameObjects(out); _ = RewriteSites(out); _ = Scheduled(nil) })
				}
				readers.Wait()
			}
		})
	}
	group.Wait()
}

func metadataComparable(metadata loweringMetadata) loweringMetadata {
	metadata.owner = weak.Pointer[asm.Function]{}
	return metadata
}

// Preserve the pre-metadata test's complete assembly comparison, and now also
// compare every owned metadata value while excluding only object identity.
func equalLoweredFunctions(left, right *asm.Function) bool {
	a, b := *left, *right
	a.LoweringMetadata, b.LoweringMetadata = nil, nil
	return reflect.DeepEqual(a, b) && reflect.DeepEqual(metadataComparable(*readLoweringMetadata(left)), metadataComparable(*readLoweringMetadata(right)))
}
