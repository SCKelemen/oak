package machine

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/optir"
)

type optIRMemoryCallTarget struct {
	name            string
	arch            string
	parameter       asm.Register
	callInstruction string
	addressText     string
	storeText       string
	lowerChecked    func(optir.CFG, *asm.Function, optir.CheckedMemoryAuthority, optir.CheckedMemoryProjection, optir.RegionMemorySSA, map[optir.RegionID]OptIRRegionGlobal) (*asm.Function, error)
	lowerUnchecked  func(optir.CFG, *asm.Function, optir.RegionMemoryMetadata, optir.RegionMemorySSA, map[optir.RegionID]OptIRRegionGlobal) (*asm.Function, error)
}

func optIRMemoryCallTargets() []optIRMemoryCallTarget {
	return []optIRMemoryCallTarget{
		{
			name: "aarch64", arch: asm.ArchArm64, parameter: w(0),
			callInstruction: "bl inc", addressText: "adrp x17, state", storeText: "str w0, [x17,#0]",
			lowerChecked: LowerOptIRArm64WithCheckedRegionMemory, lowerUnchecked: LowerOptIRArm64WithRegionMemory,
		},
		{
			name: "rv64", arch: asm.ArchRV64, parameter: optIRRV64Register(10),
			callInstruction: "call inc", addressText: "la t6, state", storeText: "sw t0, [t6,#0]",
			lowerChecked: LowerOptIRRV64WithCheckedRegionMemory, lowerUnchecked: LowerOptIRRV64WithRegionMemory,
		},
	}
}

func TestLowerOptIRCheckedRegionMemoryNoModRefCallVerifies(t *testing.T) {
	for _, target := range optIRMemoryCallTargets() {
		t.Run(target.name, func(t *testing.T) {
			fixture := newOptIRMemoryCallFixture(t, target)
			lowered, err := target.lowerChecked(fixture.cfg, fixture.template, fixture.authority, fixture.projection, fixture.memorySSA, fixture.bindings)
			if err != nil {
				t.Fatal(err)
			}
			body := text(lowered.Items)
			for _, instruction := range []string{target.callInstruction, target.addressText, target.storeText} {
				if !strings.Contains(body, instruction) {
					t.Fatalf("selected checked call/memory body lacks %q:\n%s", instruction, body)
				}
			}
			if lowered.Frame == 0 || lowered.Frame%16 != 0 {
				t.Fatalf("selected checked call/memory frame = %d, want nonzero 16-byte alignment", lowered.Frame)
			}
			if len(lowered.Globals) != 1 || lowered.Globals["state"] != fixture.global {
				t.Fatalf("selected checked call/memory globals = %#v, want only state", lowered.Globals)
			}
			if findings := asm.Check(lowered, fixture.declaration, map[string]bool{"inc": true}); len(findings) != 0 {
				t.Fatalf("selected checked call/memory body fails seam check: %v\n%s", findings, body)
			}
			verdict := asm.Verify(lowered, fixture.declaration, fixture.declaration.Body)
			if verdict.Kind != asm.VerdictProven {
				t.Fatalf("selected checked call/memory verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
			}
			if !strings.Contains(verdict.Message, "callees taken at their Oak bodies: inc") || !strings.Contains(verdict.Message, "package state it writes (state)") {
				t.Fatalf("proven verdict does not cover the callee and package state: %s", verdict.Message)
			}
		})
	}
}

func TestLowerOptIRRegionMemoryCallRequiresUntamperedCheckedAuthority(t *testing.T) {
	for _, target := range optIRMemoryCallTargets() {
		t.Run(target.name, func(t *testing.T) {
			fixture := newOptIRMemoryCallFixture(t, target)

			if _, err := target.lowerUnchecked(fixture.cfg, fixture.template, fixture.projection.Metadata, fixture.memorySSA, fixture.bindings); err == nil || !strings.Contains(err.Error(), "requires checked memory authority") {
				t.Fatalf("caller-owned no-ModRef metadata refusal = %v", err)
			}
			unknown := fixture.projection.Metadata
			unknown.Operations = append([]optir.MemoryOperationMetadata(nil), fixture.projection.Metadata.Operations...)
			for index := range unknown.Operations {
				if unknown.Operations[index].CallEffect != "" {
					unknown.Operations[index].CallEffect = ""
					unknown.Operations[index].Accesses = []optir.MemoryAccessSpec{{Kind: optir.MemoryUnknownClobber}}
				}
			}
			unknownSSA, err := optir.AnalyzeRegionMemorySSA(fixture.cfg, unknown)
			if err != nil {
				t.Fatalf("unknown-clobber fixture: %v", err)
			}
			if _, err := target.lowerUnchecked(fixture.cfg, fixture.template, unknown, unknownSSA, fixture.bindings); err == nil || !strings.Contains(err.Error(), "unsupported access kind unknown-clobber") {
				t.Fatalf("unknown call effect refusal = %v", err)
			}

			accessOnly, err := optir.NewCheckedMemoryAuthority(fixture.authority.Records())
			if err != nil {
				t.Fatal(err)
			}
			if _, err := target.lowerChecked(fixture.cfg, fixture.template, accessOnly, fixture.projection, fixture.memorySSA, fixture.bindings); err == nil || !strings.Contains(err.Error(), "different authority") {
				t.Fatalf("absent checked call authority refusal = %v", err)
			}

			missing := fixture.cfg
			missing.Blocks = append([]optir.Block(nil), fixture.cfg.Blocks...)
			missing.Blocks[0].Operations = append([]optir.Operation(nil), fixture.cfg.Blocks[0].Operations...)
			missing.Blocks[0].Operations[0].MemoryCallID = ""
			if _, err := target.lowerChecked(missing, fixture.template, fixture.authority, fixture.projection, fixture.memorySSA, fixture.bindings); err == nil || !strings.Contains(err.Error(), "different CFG") {
				t.Fatalf("missing checked call authorization refusal = %v", err)
			}

			tampered := fixture.projection
			tampered.Metadata.Operations = append([]optir.MemoryOperationMetadata(nil), fixture.projection.Metadata.Operations...)
			for index := range tampered.Metadata.Operations {
				if tampered.Metadata.Operations[index].CallEffect != "" {
					tampered.Metadata.Operations[index].CallEffect = optir.MemoryCallEffect("read-write")
				}
			}
			if _, err := target.lowerChecked(fixture.cfg, fixture.template, fixture.authority, tampered, fixture.memorySSA, fixture.bindings); err == nil || !strings.Contains(err.Error(), "mutated") {
				t.Fatalf("tampered checked call authorization refusal = %v", err)
			}
		})
	}
}

func TestLowerOptIRForgedNoModRefSummaryCannotReceiveProvenVerdict(t *testing.T) {
	for _, target := range optIRMemoryCallTargets() {
		t.Run(target.name, func(t *testing.T) {
			fixture := newOptIRMemoryCallFixture(t, target)
			declarations := optIRRV64Declarations(t, `
inc: (x: u32): u32 = state + x
call_store: (x: u32): u32 = {
  state = x
  value: u32 = inc(x)
  state = value
  value
}
`)
			fixture.declaration = declarations["call_store"]
			fixture.template.Signature = fixture.declaration
			fixture.template.Callees = map[string]*ast.FunctionStatement{"inc": declarations["inc"]}
			lowered, err := target.lowerChecked(fixture.cfg, fixture.template, fixture.authority, fixture.projection, fixture.memorySSA, fixture.bindings)
			if err != nil {
				t.Fatal(err)
			}
			verdict := asm.Verify(lowered, fixture.declaration, fixture.declaration.Body)
			if verdict.Kind == asm.VerdictProven {
				t.Fatalf("caller-minted no-ModRef summary received a proven verdict: %s\n%s", verdict.Message, text(lowered.Items))
			}
		})
	}
}

type optIRMemoryCallFixture struct {
	cfg         optir.CFG
	template    *asm.Function
	declaration *ast.FunctionStatement
	authority   optir.CheckedMemoryAuthority
	projection  optir.CheckedMemoryProjection
	memorySSA   optir.RegionMemorySSA
	bindings    map[optir.RegionID]OptIRRegionGlobal
	global      asm.Global
}

func newOptIRMemoryCallFixture(t *testing.T, target optIRMemoryCallTarget) optIRMemoryCallFixture {
	t.Helper()
	declarations := optIRRV64Declarations(t, `
inc: (x: u32): u32 = x + u32(1)
call_store: (x: u32): u32 = {
  value: u32 = inc(x)
  state = value
  value
}
`)
	declaration := declarations["call_store"]
	const region optir.RegionID = "opaque:checked-state"
	callSource := optir.Source{Context: "checked-call-memory.oak", Line: 3, Column: 16}
	storeSource := optir.Source{Context: "checked-call-memory.oak", Line: 4, Column: 3}
	callRecord, err := optir.NewCheckedMemoryCallRecord(callSource, "inc", "checked-transitive-no-mod-ref:inc")
	if err != nil {
		t.Fatal(err)
	}
	storeRecord, err := optir.NewCheckedMemoryAccessRecord(storeSource, region, optir.MemoryWrite, "u32", true, false)
	if err != nil {
		t.Fatal(err)
	}
	authority, err := optir.NewCheckedMemoryAuthorityWithCalls([]optir.CheckedMemoryAccessRecord{storeRecord}, []optir.CheckedMemoryCallRecord{callRecord})
	if err != nil {
		t.Fatal(err)
	}
	cfg := optir.CFG{
		Name: "call_store", Entry: 0, Results: []optir.Type{"u32"},
		Blocks: []optir.Block{{
			ID: 0, Parameters: []optir.Value{{ID: 1, Type: "u32", Name: "x"}},
			Operations: []optir.Operation{
				{
					Code: optir.OpCall, Results: []optir.Value{{ID: 2, Type: "u32"}}, Operands: []optir.ValueID{1},
					Effects: []optir.Effect{optir.EffectCall}, Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "inc"}},
					Source: callSource, MemoryCallID: callRecord.ID,
				},
				{Code: optir.OpStoreRegion, Operands: []optir.ValueID{2}, Effects: []optir.Effect{optir.EffectWriteMemory}, Source: storeSource, MemoryAccessID: storeRecord.ID},
			},
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{2}},
		}},
	}
	projection, err := optir.ProjectCheckedMemory(cfg, authority)
	if err != nil {
		t.Fatal(err)
	}
	if err := optir.VerifyCheckedMemoryProjection(cfg, authority, projection); err != nil {
		t.Fatal(err)
	}
	memorySSA, err := optir.AnalyzeRegionMemorySSA(cfg, projection.Metadata)
	if err != nil {
		t.Fatal(err)
	}
	if err := optir.VerifyRegionMemorySSA(cfg, projection.Metadata, memorySSA); err != nil {
		t.Fatal(err)
	}
	global := asm.Global{Type: "u32", Bits: 32}
	template := &asm.Function{
		Name: "call_store", Arch: target.arch, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: target.parameter, Param: "x"}},
		Globals:  map[string]asm.Global{"state": global},
		Callees:  map[string]*ast.FunctionStatement{"inc": declarations["inc"]},
	}
	return optIRMemoryCallFixture{
		cfg: cfg, template: template, declaration: declaration, authority: authority, projection: projection, memorySSA: memorySSA,
		bindings: map[optir.RegionID]OptIRRegionGlobal{region: {Symbol: "state", Global: global}}, global: global,
	}
}
