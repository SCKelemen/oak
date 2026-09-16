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
	lowerCertified  func(optir.CFG, *asm.Function, optir.CheckedMemoryAuthority, optir.CheckedMemoryProjection, optir.RegionMemorySSA, optir.CheckedMemoryCallCertificate, map[optir.RegionID]OptIRRegionGlobal) (*asm.Function, error)
	lowerUnchecked  func(optir.CFG, *asm.Function, optir.RegionMemoryMetadata, optir.RegionMemorySSA, map[optir.RegionID]OptIRRegionGlobal) (*asm.Function, error)
}

func optIRMemoryCallTargets() []optIRMemoryCallTarget {
	return []optIRMemoryCallTarget{
		{
			name: "aarch64", arch: asm.ArchArm64, parameter: w(0),
			callInstruction: "bl inc", addressText: "adrp x17, state", storeText: "str w0, [x17,#0]",
			lowerChecked: LowerOptIRArm64WithCheckedRegionMemory, lowerCertified: LowerOptIRArm64WithCertifiedRegionMemory, lowerUnchecked: LowerOptIRArm64WithRegionMemory,
		},
		{
			name: "rv64", arch: asm.ArchRV64, parameter: optIRRV64Register(10),
			callInstruction: "call inc", addressText: "la t6, state", storeText: "sw t0, [t6,#0]",
			lowerChecked: LowerOptIRRV64WithCheckedRegionMemory, lowerCertified: LowerOptIRRV64WithCertifiedRegionMemory, lowerUnchecked: LowerOptIRRV64WithRegionMemory,
		},
	}
}

func TestLowerOptIRCertifiedRegionMemoryRejectsMissingCertificate(t *testing.T) {
	for _, target := range optIRMemoryCallTargets() {
		t.Run(target.name, func(t *testing.T) {
			fixture := newOptIRMemoryCallFixture(t, target)
			var missing optir.CheckedMemoryCallCertificate
			if _, err := target.lowerCertified(fixture.cfg, fixture.template, fixture.authority, fixture.projection, fixture.memorySSA, missing, fixture.bindings); err == nil || !strings.Contains(err.Error(), "certificate") {
				t.Fatalf("missing checked call certificate refusal = %v", err)
			}
			wrongTemplate := *fixture.template
			wrongDeclaration := *fixture.declaration
			wrongName := *fixture.declaration.Name
			wrongName.Value = "different_root"
			wrongDeclaration.Name = &wrongName
			wrongTemplate.Signature = &wrongDeclaration
			if _, err := target.lowerCertified(fixture.cfg, &wrongTemplate, fixture.authority, fixture.projection, fixture.memorySSA, missing, fixture.bindings); err == nil || !strings.Contains(err.Error(), "does not match template") {
				t.Fatalf("certificate/template root mismatch refusal = %v", err)
			}
		})
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

func TestLowerOptIRCertifiedRegionMemoryNoModRefCallVerifies(t *testing.T) {
	for _, target := range optIRMemoryCallTargets() {
		t.Run(target.name, func(t *testing.T) {
			fixture := newOptIRMemoryCallFixture(t, target)
			lowered, err := target.lowerCertified(
				fixture.cfg, fixture.template, fixture.authority, fixture.projection,
				fixture.memorySSA, fixture.certificate, fixture.bindings,
			)
			if err != nil {
				t.Fatal(err)
			}
			if findings := asm.Check(lowered, fixture.declaration, map[string]bool{"inc": true}); len(findings) != 0 {
				t.Fatalf("certified call/memory body fails seam check: %v\n%s", findings, text(lowered.Items))
			}
			verdict := asm.Verify(lowered, fixture.declaration, fixture.declaration.Body)
			if verdict.Kind != asm.VerdictProven {
				t.Fatalf("certified call/memory verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
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

func TestLowerOptIRCheckedRegionMemoryRefCallOnlyVerifies(t *testing.T) {
	for _, target := range optIRMemoryCallTargets() {
		t.Run(target.name, func(t *testing.T) {
			fixture := newOptIRMemoryRefCallFixture(t, target, false)
			lowered, err := target.lowerChecked(fixture.cfg, fixture.template, fixture.authority, fixture.projection, fixture.memorySSA, fixture.bindings)
			if err != nil {
				t.Fatal(err)
			}
			body := text(lowered.Items)
			if !strings.Contains(body, target.callInstruction[:strings.IndexByte(target.callInstruction, ' ')+1]+"read_state") {
				t.Fatalf("selected checked Ref body lacks call to read_state:\n%s", body)
			}
			if strings.Contains(body, target.addressText) || strings.Contains(body, target.storeText) {
				t.Fatalf("call-only checked Ref body emits a caller memory access:\n%s", body)
			}
			if len(lowered.Globals) != 1 || lowered.Globals["state"] != fixture.global {
				t.Fatalf("selected checked Ref globals = %#v, want callee-only state", lowered.Globals)
			}
			if lowered.Frame == 0 || lowered.Frame%16 != 0 {
				t.Fatalf("selected checked Ref frame = %d, want nonzero 16-byte alignment", lowered.Frame)
			}
			if findings := asm.Check(lowered, fixture.declaration, map[string]bool{"read_state": true}); len(findings) != 0 {
				t.Fatalf("selected checked Ref body fails seam check: %v\n%s", findings, body)
			}
			verdict := asm.Verify(lowered, fixture.declaration, fixture.declaration.Body)
			if verdict.Kind != asm.VerdictProven {
				t.Fatalf("selected checked Ref verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
			}
			if !strings.Contains(verdict.Message, "callees taken at their Oak bodies: read_state") {
				t.Fatalf("proven Ref verdict does not name the admitted callee: %s", verdict.Message)
			}
		})
	}
}

func TestLowerOptIRRegionMemoryRefCallFailsClosed(t *testing.T) {
	for _, target := range optIRMemoryCallTargets() {
		t.Run(target.name, func(t *testing.T) {
			fixture := newOptIRMemoryRefCallFixture(t, target, false)

			if _, err := target.lowerUnchecked(fixture.cfg, fixture.template, fixture.projection.Metadata, fixture.memorySSA, fixture.bindings); err == nil || !strings.Contains(err.Error(), "requires checked memory authority") {
				t.Fatalf("caller-owned Ref metadata refusal = %v", err)
			}

			wrongBinding := map[optir.RegionID]OptIRRegionGlobal{}
			for region, binding := range fixture.bindings {
				wrongBinding[region] = OptIRRegionGlobal{Symbol: binding.Symbol, Global: asm.Global{Type: "i32", Bits: 32}}
			}
			if _, err := target.lowerChecked(fixture.cfg, fixture.template, fixture.authority, fixture.projection, fixture.memorySSA, wrongBinding); err == nil || !strings.Contains(err.Error(), "storage is i32/32") {
				t.Fatalf("Ref descriptor mismatch refusal = %v", err)
			}

			missingGlobal := *fixture.template
			missingGlobal.Globals = nil
			if _, err := target.lowerChecked(fixture.cfg, &missingGlobal, fixture.authority, fixture.projection, fixture.memorySSA, fixture.bindings); err == nil || !strings.Contains(err.Error(), "not authorized by the assembler template") {
				t.Fatalf("Ref missing-global refusal = %v", err)
			}

			tampered := fixture.projection
			tampered.Metadata.Operations = append([]optir.MemoryOperationMetadata(nil), fixture.projection.Metadata.Operations...)
			tampered.Metadata.Operations[0].Accesses = append([]optir.MemoryAccessSpec(nil), fixture.projection.Metadata.Operations[0].Accesses...)
			tampered.Metadata.Operations[0].Accesses[0].Kind = optir.MemoryWrite
			if _, err := target.lowerChecked(fixture.cfg, fixture.template, fixture.authority, tampered, fixture.memorySSA, fixture.bindings); err == nil || !strings.Contains(err.Error(), "mutated") {
				t.Fatalf("tampered Ref/write refusal = %v", err)
			}

			cyclic := newOptIRMemoryRefCallFixture(t, target, true)
			if _, err := target.lowerChecked(cyclic.cfg, cyclic.template, cyclic.authority, cyclic.projection, cyclic.memorySSA, cyclic.bindings); err == nil || !strings.Contains(err.Error(), "calls require acyclic control flow") {
				t.Fatalf("cyclic Ref-call refusal = %v", err)
			}
		})
	}
}

func TestLowerOptIRForgedRefSummaryCannotReceiveProvenVerdict(t *testing.T) {
	for _, target := range optIRMemoryCallTargets() {
		t.Run(target.name, func(t *testing.T) {
			fixture := newOptIRMemoryRefCallFixture(t, target, false)
			declarations := optIRRV64Declarations(t, `
read_state: (): u32 = other
call_read: (): u32 = read_state()
`)
			fixture.declaration = declarations["call_read"]
			fixture.template.Signature = fixture.declaration
			fixture.template.Callees = map[string]*ast.FunctionStatement{"read_state": declarations["read_state"]}
			fixture.template.Globals["other"] = fixture.global
			lowered, err := target.lowerChecked(fixture.cfg, fixture.template, fixture.authority, fixture.projection, fixture.memorySSA, fixture.bindings)
			if err != nil {
				t.Fatal(err)
			}
			verdict := asm.Verify(lowered, fixture.declaration, fixture.declaration.Body)
			if verdict.Kind == asm.VerdictProven {
				t.Fatalf("caller-minted Ref summary received a proven verdict: %s\n%s", verdict.Message, text(lowered.Items))
			}
		})
	}
}

func TestLowerOptIRCheckedRegionMemoryWriteCallsVerify(t *testing.T) {
	for _, target := range optIRMemoryCallTargets() {
		for _, effect := range []optir.MemoryCallEffect{optir.MemoryCallMod, optir.MemoryCallModRef} {
			t.Run(target.name+"/"+string(effect), func(t *testing.T) {
				fixture := newOptIRMemoryWriteCallFixture(t, target, effect)
				lowered, err := target.lowerChecked(fixture.cfg, fixture.template, fixture.authority, fixture.projection, fixture.memorySSA, fixture.bindings)
				if err != nil {
					t.Fatal(err)
				}
				callee := "write_state"
				if effect == optir.MemoryCallModRef {
					callee = "update_state"
				}
				body := text(lowered.Items)
				callPrefix := target.callInstruction[:strings.IndexByte(target.callInstruction, ' ')+1]
				if !strings.Contains(body, callPrefix+callee) {
					t.Fatalf("selected checked %s body lacks call to %s:\n%s", effect, callee, body)
				}
				if strings.Contains(body, target.addressText) {
					t.Fatalf("call-only checked %s body emits a synthetic caller memory access:\n%s", effect, body)
				}
				if len(lowered.Globals) != 1 || lowered.Globals["state"] != fixture.global {
					t.Fatalf("selected checked %s globals = %#v, want callee-only state", effect, lowered.Globals)
				}
				if lowered.Frame == 0 || lowered.Frame%16 != 0 {
					t.Fatalf("selected checked %s frame = %d, want nonzero 16-byte alignment", effect, lowered.Frame)
				}
				if findings := asm.Check(lowered, fixture.declaration, map[string]bool{callee: true}); len(findings) != 0 {
					t.Fatalf("selected checked %s body fails seam check: %v\n%s", effect, findings, body)
				}
				verdict := asm.Verify(lowered, fixture.declaration, fixture.declaration.Body)
				if verdict.Kind != asm.VerdictProven {
					t.Fatalf("selected checked %s verdict = %s (%s)\n%s", effect, verdict.Kind, verdict.Message, body)
				}
				if !strings.Contains(verdict.Message, "callees taken at their Oak bodies: "+callee) {
					t.Fatalf("proven %s verdict does not name the admitted callee: %s", effect, verdict.Message)
				}
			})
		}
	}
}

func TestLowerOptIRRegionMemoryWriteCallsFailClosed(t *testing.T) {
	for _, target := range optIRMemoryCallTargets() {
		for _, effect := range []optir.MemoryCallEffect{optir.MemoryCallMod, optir.MemoryCallModRef} {
			t.Run(target.name+"/"+string(effect), func(t *testing.T) {
				fixture := newOptIRMemoryWriteCallFixture(t, target, effect)
				if _, err := target.lowerUnchecked(fixture.cfg, fixture.template, fixture.projection.Metadata, fixture.memorySSA, fixture.bindings); err == nil || !strings.Contains(err.Error(), "requires checked memory authority") {
					t.Fatalf("caller-owned %s metadata refusal = %v", effect, err)
				}

				wrongEffect := fixture.projection
				wrongEffect.Metadata.Operations = append([]optir.MemoryOperationMetadata(nil), fixture.projection.Metadata.Operations...)
				wrongEffect.Metadata.Operations[0].CallEffect = optir.MemoryCallRef
				if _, err := target.lowerChecked(fixture.cfg, fixture.template, fixture.authority, wrongEffect, fixture.memorySSA, fixture.bindings); err == nil || !strings.Contains(err.Error(), "mutated") {
					t.Fatalf("tampered %s effect refusal = %v", effect, err)
				}

				wholeWrite := fixture.projection
				wholeWrite.Metadata.Operations = append([]optir.MemoryOperationMetadata(nil), fixture.projection.Metadata.Operations...)
				wholeWrite.Metadata.Operations[0].Accesses = append([]optir.MemoryAccessSpec(nil), fixture.projection.Metadata.Operations[0].Accesses...)
				wholeWrite.Metadata.Operations[0].Accesses[0].WholeRegion = true
				if _, err := target.lowerChecked(fixture.cfg, fixture.template, fixture.authority, wholeWrite, fixture.memorySSA, fixture.bindings); err == nil || !strings.Contains(err.Error(), "mutated") {
					t.Fatalf("tampered %s whole-write refusal = %v", effect, err)
				}
			})
		}
	}
}

func TestLowerOptIRForgedModSummaryCannotReceiveProvenVerdict(t *testing.T) {
	for _, target := range optIRMemoryCallTargets() {
		t.Run(target.name, func(t *testing.T) {
			fixture := newOptIRForgedModDSEFixture(t, target)
			lowered, err := target.lowerChecked(fixture.cfg, fixture.template, fixture.authority, fixture.projection, fixture.memorySSA, fixture.bindings)
			if err != nil {
				t.Fatal(err)
			}
			verdict := asm.Verify(lowered, fixture.declaration, fixture.declaration.Body)
			if verdict.Kind == asm.VerdictProven {
				t.Fatalf("caller-minted Mod summary received a proven verdict: %s\n%s", verdict.Message, text(lowered.Items))
			}
		})
	}
}

func TestLowerOptIRForgedRefWriteAcrossForwardedLoadCannotReceiveProvenVerdict(t *testing.T) {
	for _, target := range optIRMemoryCallTargets() {
		t.Run(target.name, func(t *testing.T) {
			fixture := newOptIRForgedForwardedRefFixture(t, target)
			lowered, err := target.lowerChecked(fixture.cfg, fixture.template, fixture.authority, fixture.projection, fixture.memorySSA, fixture.bindings)
			if err != nil {
				t.Fatal(err)
			}
			verdict := asm.Verify(lowered, fixture.declaration, fixture.declaration.Body)
			if verdict.Kind == asm.VerdictProven {
				t.Fatalf("forged Ref write across a forwarded load received a proven verdict: %s\n%s", verdict.Message, text(lowered.Items))
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
	certificate optir.CheckedMemoryCallCertificate
	bindings    map[optir.RegionID]OptIRRegionGlobal
	global      asm.Global
}

func newOptIRForgedModDSEFixture(t *testing.T, target optIRMemoryCallTarget) optIRMemoryCallFixture {
	t.Helper()
	declarations := optIRRV64Declarations(t, `
read_then_write: (value: u32): u32 = {
  old: u32 = state
  state = value
  old
}
call_write: (value: u32): u32 = {
  state = u32(7)
  old: u32 = read_then_write(value)
  state = u32(9)
  old
}
`)
	declaration := declarations["call_write"]
	const region optir.RegionID = "opaque:checked-state"
	callSource := optir.Source{Context: "forged-mod-dse.oak", Line: 8, Column: 14}
	storeSource := optir.Source{Context: "forged-mod-dse.oak", Line: 9, Column: 3}
	callRecord, err := optir.NewCheckedMemoryCallRecordWithAccesses(callSource, "read_then_write", "forged-mod:read_then_write", []optir.CheckedMemoryCallAccess{{
		Region: region, Kind: optir.MemoryWrite, ValueType: "u32",
	}})
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
	// A forged write-only summary makes the source's first store look dead once
	// the final whole store is considered. The candidate is that store-elided
	// form; the real callee read makes its returned value observably different.
	cfg := optir.CFG{
		Name: "call_write", Entry: 0, Results: []optir.Type{"u32"},
		Blocks: []optir.Block{{
			ID: 0, Parameters: []optir.Value{{ID: 1, Type: "u32", Name: "value"}},
			Operations: []optir.Operation{
				{
					Code: optir.OpCall, Results: []optir.Value{{ID: 2, Type: "u32"}}, Operands: []optir.ValueID{1},
					Effects: []optir.Effect{optir.EffectCall}, Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "read_then_write"}},
					Source: callSource, MemoryCallID: callRecord.ID,
				},
				{Code: optir.OpConstInt, Results: []optir.Value{{ID: 3, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "9"}}},
				{Code: optir.OpStoreRegion, Operands: []optir.ValueID{3}, Effects: []optir.Effect{optir.EffectWriteMemory}, Source: storeSource, MemoryAccessID: storeRecord.ID},
			},
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{2}},
		}},
	}
	projection, err := optir.ProjectCheckedMemory(cfg, authority)
	if err != nil {
		t.Fatal(err)
	}
	memorySSA, err := optir.AnalyzeRegionMemorySSA(cfg, projection.Metadata)
	if err != nil {
		t.Fatal(err)
	}
	global := asm.Global{Type: "u32", Bits: 32}
	template := &asm.Function{
		Name: "call_write", Arch: target.arch, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: target.parameter, Param: "value"}}, Globals: map[string]asm.Global{"state": global},
		Callees: map[string]*ast.FunctionStatement{"read_then_write": declarations["read_then_write"]},
	}
	return optIRMemoryCallFixture{
		cfg: cfg, template: template, declaration: declaration, authority: authority, projection: projection, memorySSA: memorySSA,
		bindings: map[optir.RegionID]OptIRRegionGlobal{region: {Symbol: "state", Global: global}}, global: global,
	}
}

func newOptIRForgedForwardedRefFixture(t *testing.T, target optIRMemoryCallTarget) optIRMemoryCallFixture {
	t.Helper()
	declarations := optIRRV64Declarations(t, `
clobber: (value: u32): u32 = {
  state = u32(41)
  value
}
store_call_load: (value: u32): u32 = {
  state = value
  passthrough: u32 = clobber(value)
  state
}
`)
	declaration := declarations["store_call_load"]
	const region optir.RegionID = "opaque:checked-state"
	storeSource := optir.Source{Context: "forged-forwarded-ref.oak", Line: 7, Column: 3}
	callSource := optir.Source{Context: "forged-forwarded-ref.oak", Line: 8, Column: 22}
	storeRecord, err := optir.NewCheckedMemoryAccessRecord(storeSource, region, optir.MemoryWrite, "u32", true, false)
	if err != nil {
		t.Fatal(err)
	}
	callRecord, err := optir.NewCheckedMemoryCallRecordWithAccesses(callSource, "clobber", "forged-ref:clobber", []optir.CheckedMemoryCallAccess{{
		Region: region, Kind: optir.MemoryRead, ValueType: "u32",
	}})
	if err != nil {
		t.Fatal(err)
	}
	authority, err := optir.NewCheckedMemoryAuthorityWithCalls([]optir.CheckedMemoryAccessRecord{storeRecord}, []optir.CheckedMemoryCallRecord{callRecord})
	if err != nil {
		t.Fatal(err)
	}
	// This candidate has the same observable result as forwarding the final
	// source load across a falsely summarized call. Returning the call's equal
	// passthrough result keeps the fixture inside the closed call selector, which
	// does not admit an unrelated value live across a call.
	cfg := optir.CFG{
		Name: "store_call_load", Entry: 0, Results: []optir.Type{"u32"},
		Blocks: []optir.Block{{
			ID: 0, Parameters: []optir.Value{{ID: 1, Type: "u32", Name: "value"}},
			Operations: []optir.Operation{
				{Code: optir.OpStoreRegion, Operands: []optir.ValueID{1}, Effects: []optir.Effect{optir.EffectWriteMemory}, Source: storeSource, MemoryAccessID: storeRecord.ID},
				{
					Code: optir.OpCall, Results: []optir.Value{{ID: 2, Type: "u32"}}, Operands: []optir.ValueID{1},
					Effects: []optir.Effect{optir.EffectCall}, Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "clobber"}},
					Source: callSource, MemoryCallID: callRecord.ID,
				},
			},
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{2}},
		}},
	}
	projection, err := optir.ProjectCheckedMemory(cfg, authority)
	if err != nil {
		t.Fatal(err)
	}
	memorySSA, err := optir.AnalyzeRegionMemorySSA(cfg, projection.Metadata)
	if err != nil {
		t.Fatal(err)
	}
	global := asm.Global{Type: "u32", Bits: 32}
	template := &asm.Function{
		Name: "store_call_load", Arch: target.arch, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: target.parameter, Param: "value"}},
		Globals:  map[string]asm.Global{"state": global},
		Callees:  map[string]*ast.FunctionStatement{"clobber": declarations["clobber"]},
	}
	return optIRMemoryCallFixture{
		cfg: cfg, template: template, declaration: declaration, authority: authority, projection: projection, memorySSA: memorySSA,
		bindings: map[optir.RegionID]OptIRRegionGlobal{region: {Symbol: "state", Global: global}}, global: global,
	}
}

func newOptIRMemoryRefCallFixture(t *testing.T, target optIRMemoryCallTarget, cyclic bool) optIRMemoryCallFixture {
	t.Helper()
	declarations := optIRRV64Declarations(t, `
read_state: (): u32 = state
call_read: (): u32 = read_state()
`)
	declaration := declarations["call_read"]
	const region optir.RegionID = "opaque:checked-state"
	callSource := optir.Source{Context: "checked-ref-call-memory.oak", Line: 2, Column: 24}
	callRecord, err := optir.NewCheckedMemoryCallRecordWithAccesses(callSource, "read_state", "checked-transitive-ref:read_state", []optir.CheckedMemoryCallAccess{{
		Region: region, Kind: optir.MemoryRead, ValueType: "u32",
	}})
	if err != nil {
		t.Fatal(err)
	}
	authority, err := optir.NewCheckedMemoryAuthorityWithCalls(nil, []optir.CheckedMemoryCallRecord{callRecord})
	if err != nil {
		t.Fatal(err)
	}
	cfg := optir.CFG{
		Name: "call_read", Entry: 0, Results: []optir.Type{"u32"},
		Blocks: []optir.Block{{
			ID: 0,
			Operations: []optir.Operation{{
				Code: optir.OpCall, Results: []optir.Value{{ID: 1, Type: "u32"}}, Effects: []optir.Effect{optir.EffectCall},
				Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "read_state"}}, Source: callSource, MemoryCallID: callRecord.ID,
			}},
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}},
		}},
	}
	if cyclic {
		cfg.Blocks = []optir.Block{
			{
				ID: 0,
				Operations: []optir.Operation{
					{Code: optir.OpConstBool, Results: []optir.Value{{ID: 1, Type: optir.TypeBool}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "false"}}},
					{Code: optir.OpConstInt, Results: []optir.Value{{ID: 2, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "0"}}},
				},
				Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 1}},
			},
			{ID: 1, Terminator: optir.Terminator{Kind: optir.TerminatorCondBranch, Condition: 1, True: optir.Edge{Target: 2}, False: optir.Edge{Target: 3}}},
			{
				ID: 2,
				Operations: []optir.Operation{{
					Code: optir.OpCall, Results: []optir.Value{{ID: 3, Type: "u32"}}, Effects: []optir.Effect{optir.EffectCall},
					Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "read_state"}}, Source: callSource, MemoryCallID: callRecord.ID,
				}},
				Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 1}},
			},
			{ID: 3, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{2}}},
		}
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
		Name: "call_read", Arch: target.arch, Signature: declaration, Fallback: true,
		Globals: map[string]asm.Global{"state": global}, Callees: map[string]*ast.FunctionStatement{"read_state": declarations["read_state"]},
	}
	return optIRMemoryCallFixture{
		cfg: cfg, template: template, declaration: declaration, authority: authority, projection: projection, memorySSA: memorySSA,
		bindings: map[optir.RegionID]OptIRRegionGlobal{region: {Symbol: "state", Global: global}}, global: global,
	}
}

func newOptIRMemoryWriteCallFixture(t *testing.T, target optIRMemoryCallTarget, effect optir.MemoryCallEffect) optIRMemoryCallFixture {
	t.Helper()
	callee, caller, kind := "write_state", "call_write", optir.MemoryWrite
	source := `
write_state: (value: u32): u32 = {
  state = value
  value
}
call_write: (value: u32): u32 = write_state(value)
`
	if effect == optir.MemoryCallModRef {
		callee, caller, kind = "update_state", "call_update", optir.MemoryReadWrite
		source = `
update_state: (value: u32): u32 = {
  state = state + value
  state
}
call_update: (value: u32): u32 = update_state(value)
`
	} else if effect != optir.MemoryCallMod {
		t.Fatalf("unsupported write-call fixture effect %q", effect)
	}
	declarations := optIRRV64Declarations(t, source)
	declaration := declarations[caller]
	const region optir.RegionID = "opaque:checked-state"
	callSource := optir.Source{Context: "checked-write-call-memory.oak", Line: 6, Column: 32}
	callRecord, err := optir.NewCheckedMemoryCallRecordWithAccesses(callSource, callee, "checked-transitive-"+string(effect)+":"+callee, []optir.CheckedMemoryCallAccess{{
		Region: region, Kind: kind, ValueType: "u32",
	}})
	if err != nil {
		t.Fatal(err)
	}
	authority, err := optir.NewCheckedMemoryAuthorityWithCalls(nil, []optir.CheckedMemoryCallRecord{callRecord})
	if err != nil {
		t.Fatal(err)
	}
	cfg := optir.CFG{
		Name: caller, Entry: 0, Results: []optir.Type{"u32"},
		Blocks: []optir.Block{{
			ID: 0, Parameters: []optir.Value{{ID: 1, Type: "u32", Name: "value"}},
			Operations: []optir.Operation{{
				Code: optir.OpCall, Results: []optir.Value{{ID: 2, Type: "u32"}}, Operands: []optir.ValueID{1}, Effects: []optir.Effect{optir.EffectCall},
				Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: callee}}, Source: callSource, MemoryCallID: callRecord.ID,
			}},
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
		Name: caller, Arch: target.arch, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: target.parameter, Param: "value"}}, Globals: map[string]asm.Global{"state": global},
		Callees: map[string]*ast.FunctionStatement{callee: declarations[callee]},
	}
	return optIRMemoryCallFixture{
		cfg: cfg, template: template, declaration: declaration, authority: authority, projection: projection, memorySSA: memorySSA,
		bindings: map[optir.RegionID]OptIRRegionGlobal{region: {Symbol: "state", Global: global}}, global: global,
	}
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
	leafCFG := optir.CFG{
		Name: "inc", Entry: 0, Results: []optir.Type{"u32"},
		Blocks: []optir.Block{{
			ID: 0, Parameters: []optir.Value{{ID: 1, Type: "u32", Name: "x"}},
			Operations: []optir.Operation{
				{Code: optir.OpConstInt, Results: []optir.Value{{ID: 2, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "1"}}},
				{Code: optir.OpIntAdd, Results: []optir.Value{{ID: 3, Type: "u32"}}, Operands: []optir.ValueID{1, 2}},
			},
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{3}},
		}},
	}
	leafAuthority, err := optir.NewCheckedMemoryAuthority(nil)
	if err != nil {
		t.Fatal(err)
	}
	leafSummary, err := optir.DeriveCheckedMemoryCallSummary(leafCFG, leafAuthority)
	if err != nil {
		t.Fatal(err)
	}
	callRecord, err := optir.NewCheckedMemoryCallRecordWithAccesses(callSource, "inc", leafSummary.Fingerprint(), leafSummary.Accesses())
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
	certificate, err := optir.NewCheckedMemoryCallCertificate("call_store", []optir.CheckedMemoryCallCertificateNode{
		{Name: "call_store", CFG: cfg, Authority: authority},
		{Name: "inc", CFG: leafCFG, Authority: leafAuthority},
	})
	if err != nil {
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
		certificate: certificate, bindings: map[optir.RegionID]OptIRRegionGlobal{region: {Symbol: "state", Global: global}}, global: global,
	}
}
