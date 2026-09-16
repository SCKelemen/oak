package machine

import (
	"fmt"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

// OptIRRegionGlobal binds one checked, target-independent memory region to
// the exact scalar package symbol emitted by a machine selector. Region
// identity is never inferred from the symbol spelling.
type OptIRRegionGlobal struct {
	Symbol string
	Global asm.Global
}

type optIRRegionMemorySelection struct {
	stores  map[optir.OperationSite]OptIRRegionGlobal
	loads   map[optir.OperationSite]OptIRRegionGlobal
	calls   map[optir.OperationSite]optir.MemoryCallEffect
	globals map[string]asm.Global
}

// validateCertifiedOptIRRegionMemory is the production call-summary seam. It
// independently checks the recursive summary certificate against the exact
// function, CFG, and source authority before the lower-level transport and
// MemorySSA checks may interpret any call effect.
func validateCertifiedOptIRRegionMemory(
	cfg optir.CFG,
	template *asm.Function,
	authority optir.CheckedMemoryAuthority,
	projection optir.CheckedMemoryProjection,
	memorySSA optir.RegionMemorySSA,
	certificate optir.CheckedMemoryCallCertificate,
	bindings map[optir.RegionID]OptIRRegionGlobal,
) (*optIRRegionMemorySelection, error) {
	if template == nil || template.Signature == nil || template.Signature.Name == nil {
		return nil, fmt.Errorf("machine: OptIR checked memory call certificate needs a named assembler template")
	}
	if template.Signature.Name.Value != cfg.Name {
		return nil, fmt.Errorf("machine: OptIR checked memory call certificate root %q does not match template %q", cfg.Name, template.Signature.Name.Value)
	}
	if err := optir.VerifyCheckedMemoryCallCertificate(cfg.Name, cfg, authority, certificate); err != nil {
		return nil, fmt.Errorf("machine: OptIR checked memory call certificate: %w", err)
	}
	return validateCheckedOptIRRegionMemory(cfg, template, authority, projection, memorySSA, bindings)
}

// validateCheckedOptIRRegionMemory is the low-level semantic-authority and
// transport-integrity seam. Production call-bearing lowering first uses
// validateCertifiedOptIRRegionMemory to establish the summaries themselves.
// RegionMemorySSA proves consistency with metadata; this additional check
// proves that the metadata itself was projected from checked source accesses
// on the exact final CFG.
func validateCheckedOptIRRegionMemory(
	cfg optir.CFG,
	template *asm.Function,
	authority optir.CheckedMemoryAuthority,
	projection optir.CheckedMemoryProjection,
	memorySSA optir.RegionMemorySSA,
	bindings map[optir.RegionID]OptIRRegionGlobal,
) (*optIRRegionMemorySelection, error) {
	if err := optir.VerifyCheckedMemoryProjection(cfg, authority, projection); err != nil {
		return nil, fmt.Errorf("machine: OptIR checked region memory authority: %w", err)
	}
	callRecords := make(map[string]optir.CheckedMemoryCallRecord)
	for _, record := range authority.CallRecords() {
		callRecords[record.ID] = record
	}
	return validateOptIRRegionMemoryWithCalls(cfg, template, projection.Metadata, memorySSA, bindings, true, callRecords)
}

// validateOptIRRegionMemory closes the first memory-emission subset before a
// target sees it. It deliberately admits only acyclic control flow or one
// canonical natural loop. Exact scalar package-cell reads, whole nonvolatile
// replacements, and (on acyclic CFGs) production-authenticated exact call
// summaries are the only memory vocabulary. The independent MemorySSA
// verifier binds operation sites and merge/loop versions to the exact CFG and
// checked region metadata.
func validateOptIRRegionMemory(
	cfg optir.CFG,
	template *asm.Function,
	metadata optir.RegionMemoryMetadata,
	memorySSA optir.RegionMemorySSA,
	bindings map[optir.RegionID]OptIRRegionGlobal,
) (*optIRRegionMemorySelection, error) {
	return validateOptIRRegionMemoryWithCalls(cfg, template, metadata, memorySSA, bindings, false, nil)
}

func validateOptIRRegionMemoryWithCalls(
	cfg optir.CFG,
	template *asm.Function,
	metadata optir.RegionMemoryMetadata,
	memorySSA optir.RegionMemorySSA,
	bindings map[optir.RegionID]OptIRRegionGlobal,
	checkedCalls bool,
	callRecords map[string]optir.CheckedMemoryCallRecord,
) (*optIRRegionMemorySelection, error) {
	if template == nil {
		return nil, fmt.Errorf("machine: OptIR region memory needs an assembler function template")
	}
	if err := optir.VerifyRegionMemorySSA(cfg, metadata, memorySSA); err != nil {
		return nil, fmt.Errorf("machine: OptIR region memory evidence: %w", err)
	}
	acyclic, err := optIRCFGAcyclic(cfg)
	if err != nil {
		return nil, fmt.Errorf("machine: OptIR region memory control flow: %w", err)
	}
	if !acyclic {
		if _, canonical := optIRCanonicalLoopCondition(cfg); !canonical {
			return nil, fmt.Errorf("machine: OptIR region memory requires acyclic control flow or one canonical natural loop")
		}
	}
	if len(metadata.Regions) == 0 {
		return nil, fmt.Errorf("machine: OptIR region memory requires at least one declared region")
	}
	if len(bindings) != len(metadata.Regions) {
		return nil, fmt.Errorf("machine: OptIR region memory has %d bindings for %d regions", len(bindings), len(metadata.Regions))
	}

	declared := make(map[optir.RegionID]bool, len(metadata.Regions))
	symbols := make(map[string]optir.RegionID, len(metadata.Regions))
	for _, region := range metadata.Regions {
		declared[region] = true
		binding, exists := bindings[region]
		if !exists {
			return nil, fmt.Errorf("machine: OptIR memory region %q has no global binding", region)
		}
		if binding.Symbol == "" {
			return nil, fmt.Errorf("machine: OptIR memory region %q has an empty global symbol", region)
		}
		if previous, duplicate := symbols[binding.Symbol]; duplicate {
			return nil, fmt.Errorf("machine: OptIR memory regions %q and %q share global symbol %q", previous, region, binding.Symbol)
		}
		symbols[binding.Symbol] = region
	}
	for region := range bindings {
		if !declared[region] {
			return nil, fmt.Errorf("machine: OptIR global binding names undeclared memory region %q", region)
		}
	}

	types := optIRTypes(cfg)
	stores := make(map[optir.OperationSite]OptIRRegionGlobal, len(metadata.Operations))
	loads := make(map[optir.OperationSite]OptIRRegionGlobal, len(metadata.Operations))
	calls := make(map[optir.OperationSite]optir.MemoryCallEffect)
	selectedGlobals := make(map[string]asm.Global, len(metadata.Regions))
	accessed := make(map[optir.RegionID]bool, len(metadata.Regions))
	summaryAccesses := 0
	for _, operationMetadata := range metadata.Operations {
		site := operationMetadata.Site
		block := optIRBlock(cfg, site.Block)
		if block == nil || site.Index < 0 || site.Index >= len(block.Operations) {
			return nil, fmt.Errorf("machine: OptIR region memory metadata names missing operation %d:%d", site.Block, site.Index)
		}
		operation := block.Operations[site.Index]
		if operationMetadata.CallEffect != "" {
			if !checkedCalls {
				return nil, fmt.Errorf("machine: OptIR call summary %d:%d requires checked memory authority", site.Block, site.Index)
			}
			if operation.Code != optir.OpCall || operation.MemoryCallID == "" {
				return nil, fmt.Errorf("machine: OptIR operation %d:%d is not an authenticated call summary", site.Block, site.Index)
			}
			record, authenticated := callRecords[operation.MemoryCallID]
			if !authenticated {
				return nil, fmt.Errorf("machine: OptIR call %d:%d has no authenticated call record", site.Block, site.Index)
			}
			if expected, valid := optIRCheckedCallEffect(record.Accesses); !valid || expected != operationMetadata.CallEffect {
				return nil, fmt.Errorf("machine: OptIR call %d:%d effect %q does not match its checked accesses", site.Block, site.Index, operationMetadata.CallEffect)
			}
			if len(record.Accesses) != len(operationMetadata.Accesses) {
				return nil, fmt.Errorf("machine: OptIR call %d:%d lacks its exact checked accesses", site.Block, site.Index)
			}
			checkedByRegion := make(map[optir.RegionID]optir.CheckedMemoryCallAccess, len(record.Accesses))
			for _, checked := range record.Accesses {
				if _, duplicate := checkedByRegion[checked.Region]; duplicate {
					return nil, fmt.Errorf("machine: OptIR call %d:%d repeats checked region %q", site.Block, site.Index, checked.Region)
				}
				checkedByRegion[checked.Region] = checked
			}
			for _, access := range operationMetadata.Accesses {
				checked, exact := checkedByRegion[access.Region]
				if !exact || access.Kind != checked.Kind || access.WholeRegion != checked.WholeRegion || access.Volatile != checked.Volatile || access.WholeRegion || access.Volatile {
					return nil, fmt.Errorf("machine: OptIR call %d:%d does not carry one exact nonvolatile partial access to region %q", site.Block, site.Index, access.Region)
				}
				binding, exists := bindings[access.Region]
				if !exists {
					return nil, fmt.Errorf("machine: OptIR call %d:%d names unbound region %q", site.Block, site.Index, access.Region)
				}
				if err := validateOptIRRegionGlobalBinding(template, access.Region, checked.ValueType, binding); err != nil {
					return nil, fmt.Errorf("machine: OptIR call %d:%d: %w", site.Block, site.Index, err)
				}
				accessed[access.Region] = true
				selectedGlobals[binding.Symbol] = binding.Global
				summaryAccesses++
			}
			calls[site] = operationMetadata.CallEffect
			continue
		}
		if len(operationMetadata.Accesses) != 1 {
			return nil, fmt.Errorf("machine: OptIR region memory operation %d:%d has %d accesses, want one", site.Block, site.Index, len(operationMetadata.Accesses))
		}
		access := operationMetadata.Accesses[0]
		if access.Kind != optir.MemoryRead && access.Kind != optir.MemoryWrite {
			return nil, fmt.Errorf("machine: OptIR region memory operation %d:%d has unsupported access kind %s", site.Block, site.Index, access.Kind)
		}
		binding, exists := bindings[access.Region]
		if !exists {
			return nil, fmt.Errorf("machine: OptIR region memory operation %d:%d names unbound region %q", site.Block, site.Index, access.Region)
		}
		var valueType optir.Type
		switch access.Kind {
		case optir.MemoryRead:
			if access.WholeRegion || access.Volatile || operation.Code != optir.OpLoadRegion || len(operation.Results) != 1 || len(operation.Operands) != 0 || len(operation.Attributes) != 0 ||
				len(operation.Effects) != 1 || operation.Effects[0] != optir.EffectReadMemory {
				return nil, fmt.Errorf("machine: OptIR operation %d:%d is not a canonical nonvolatile region load", site.Block, site.Index)
			}
			valueType = operation.Results[0].Type
			loads[site] = binding
		case optir.MemoryWrite:
			if !access.WholeRegion || access.Volatile || operation.Code != optir.OpStoreRegion || len(operation.Results) != 0 || len(operation.Operands) != 1 || len(operation.Attributes) != 0 ||
				len(operation.Effects) != 1 || operation.Effects[0] != optir.EffectWriteMemory {
				return nil, fmt.Errorf("machine: OptIR operation %d:%d is not a canonical region store (not one whole nonvolatile write)", site.Block, site.Index)
			}
			var typed bool
			valueType, typed = types[operation.Operands[0]]
			if !typed {
				return nil, fmt.Errorf("machine: OptIR region store %d:%d operand %d has no type", site.Block, site.Index, operation.Operands[0])
			}
			stores[site] = binding
		}
		if err := validateOptIRRegionGlobalBinding(template, access.Region, valueType, binding); err != nil {
			return nil, err
		}
		accessed[access.Region] = true
		selectedGlobals[binding.Symbol] = binding.Global
	}
	for _, block := range cfg.Blocks {
		for index, operation := range block.Operations {
			if operation.Code != optir.OpCall {
				continue
			}
			site := optir.OperationSite{Block: block.ID, Index: index}
			if _, admitted := calls[site]; !admitted {
				return nil, fmt.Errorf("machine: OptIR call %d:%d has no authenticated memory-effect summary", site.Block, site.Index)
			}
		}
	}
	if !acyclic && len(calls) != 0 {
		return nil, fmt.Errorf("machine: OptIR region memory calls require acyclic control flow")
	}
	if len(stores)+len(loads)+summaryAccesses == 0 {
		return nil, fmt.Errorf("machine: OptIR region memory has no accesses")
	}
	for _, region := range metadata.Regions {
		if !accessed[region] {
			return nil, fmt.Errorf("machine: OptIR memory region %q is declared but not accessed", region)
		}
	}
	return &optIRRegionMemorySelection{stores: stores, loads: loads, calls: calls, globals: selectedGlobals}, nil
}

func optIRCheckedCallEffect(accesses []optir.CheckedMemoryCallAccess) (optir.MemoryCallEffect, bool) {
	reads, writes := false, false
	for _, access := range accesses {
		if access.Region == "" || access.ValueType == "" || access.WholeRegion || access.Volatile {
			return "", false
		}
		switch access.Kind {
		case optir.MemoryRead:
			reads = true
		case optir.MemoryWrite:
			writes = true
		case optir.MemoryReadWrite:
			reads, writes = true, true
		default:
			return "", false
		}
	}
	switch {
	case reads && writes:
		return optir.MemoryCallModRef, true
	case writes:
		return optir.MemoryCallMod, true
	case reads:
		return optir.MemoryCallRef, true
	default:
		return optir.MemoryCallNoModRef, true
	}
}

func (selection *optIRRegionMemorySelection) admitsMemoryCalls(cfg optir.CFG) bool {
	if selection == nil {
		return false
	}
	calls := 0
	for _, block := range cfg.Blocks {
		for index, operation := range block.Operations {
			if operation.Code != optir.OpCall {
				continue
			}
			calls++
			if _, admitted := selection.calls[optir.OperationSite{Block: block.ID, Index: index}]; !admitted {
				return false
			}
		}
	}
	return calls == len(selection.calls)
}

func (selection *optIRRegionMemorySelection) selectedGlobals() map[string]asm.Global {
	if selection == nil {
		return map[string]asm.Global{}
	}
	return cloneOptIRSelectedGlobals(selection.globals)
}

func validateOptIRRegionGlobalBinding(template *asm.Function, region optir.RegionID, valueType optir.Type, binding OptIRRegionGlobal) error {
	if err := validateOptIRScalarGlobal(valueType, binding.Global); err != nil {
		return fmt.Errorf("machine: OptIR region %q global %q: %w", region, binding.Symbol, err)
	}
	authorized, exists := template.Globals[binding.Symbol]
	if !exists {
		return fmt.Errorf("machine: OptIR memory region %q global %q is not authorized by the assembler template", region, binding.Symbol)
	}
	if authorized != binding.Global {
		return fmt.Errorf("machine: OptIR memory region %q global %q does not match the assembler template", region, binding.Symbol)
	}
	return nil
}

func validateOptIRScalarGlobal(typ optir.Type, global asm.Global) error {
	bits, ok := optIRScalarGlobalBits(typ)
	if !ok {
		return fmt.Errorf("type %s is not an admitted scalar", typ)
	}
	if global.Aggregate || global.Size != 0 {
		return fmt.Errorf("aggregate or sized storage is outside the scalar region-memory subset")
	}
	if global.Type != string(typ) || global.Bits != bits {
		return fmt.Errorf("storage is %s/%d bits, want %s/%d bits", global.Type, global.Bits, typ, bits)
	}
	return nil
}

func optIRScalarGlobalBits(typ optir.Type) (int, bool) {
	if typ == optir.TypeBool {
		// Bool follows its native/C package-cell ABI, not its one-bit value
		// representation.
		return 32, true
	}
	switch typ {
	case "u8", "i8":
		return 8, true
	case "u16", "i16":
		return 16, true
	case "u32", "i32":
		return 32, true
	case "u64", "i64":
		return 64, true
	default:
		return 0, false
	}
}

func cloneOptIRSelectedGlobals(globals map[string]asm.Global) map[string]asm.Global {
	if len(globals) == 0 {
		return nil
	}
	out := make(map[string]asm.Global, len(globals))
	for symbol, global := range globals {
		out[symbol] = global
	}
	return out
}
