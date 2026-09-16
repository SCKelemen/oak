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
	stores map[optir.OperationSite]OptIRRegionGlobal
	loads  map[optir.OperationSite]OptIRRegionGlobal
}

// validateCheckedOptIRRegionMemory is the production semantic-authority seam.
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
	return validateOptIRRegionMemory(cfg, template, projection.Metadata, memorySSA, bindings)
}

// validateOptIRRegionMemory closes the first memory-emission subset before a
// target sees it. It deliberately admits only acyclic, call-free control flow
// over exact scalar package-cell reads and whole, nonvolatile replacements.
// The independent MemorySSA verifier binds operation sites and merge versions
// to the exact CFG revision and checked region metadata.
func validateOptIRRegionMemory(
	cfg optir.CFG,
	template *asm.Function,
	metadata optir.RegionMemoryMetadata,
	memorySSA optir.RegionMemorySSA,
	bindings map[optir.RegionID]OptIRRegionGlobal,
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
		return nil, fmt.Errorf("machine: OptIR region memory requires acyclic control flow")
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
	accessed := make(map[optir.RegionID]bool, len(metadata.Regions))
	for _, operationMetadata := range metadata.Operations {
		site := operationMetadata.Site
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
		block := optIRBlock(cfg, site.Block)
		if block == nil || site.Index < 0 || site.Index >= len(block.Operations) {
			return nil, fmt.Errorf("machine: OptIR region memory metadata names missing operation %d:%d", site.Block, site.Index)
		}
		operation := block.Operations[site.Index]
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
		if err := validateOptIRScalarGlobal(valueType, binding.Global); err != nil {
			return nil, fmt.Errorf("machine: OptIR region %q global %q: %w", access.Region, binding.Symbol, err)
		}
		authorized, exists := template.Globals[binding.Symbol]
		if !exists {
			return nil, fmt.Errorf("machine: OptIR memory region %q global %q is not authorized by the assembler template", access.Region, binding.Symbol)
		}
		if authorized != binding.Global {
			return nil, fmt.Errorf("machine: OptIR memory region %q global %q does not match the assembler template", access.Region, binding.Symbol)
		}
		accessed[access.Region] = true
	}
	if len(stores)+len(loads) == 0 {
		return nil, fmt.Errorf("machine: OptIR region memory has no accesses")
	}
	for _, region := range metadata.Regions {
		if !accessed[region] {
			return nil, fmt.Errorf("machine: OptIR memory region %q is declared but not accessed", region)
		}
	}
	return &optIRRegionMemorySelection{stores: stores, loads: loads}, nil
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
