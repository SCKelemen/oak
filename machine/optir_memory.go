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

type optIRRegionStoreSelection struct {
	stores map[optir.OperationSite]OptIRRegionGlobal
}

// validateOptIRRegionStores closes the first memory-emission subset before a
// target sees it. It deliberately admits only one straight-line block of
// whole, nonvolatile scalar package-cell replacements. The independent
// MemorySSA verifier binds the operation sites to the exact CFG revision and
// exact checked region metadata supplied by the frontend.
func validateOptIRRegionStores(
	cfg optir.CFG,
	template *asm.Function,
	metadata optir.RegionMemoryMetadata,
	memorySSA optir.RegionMemorySSA,
	bindings map[optir.RegionID]OptIRRegionGlobal,
) (*optIRRegionStoreSelection, error) {
	if template == nil {
		return nil, fmt.Errorf("machine: OptIR region stores need an assembler function template")
	}
	if err := optir.VerifyRegionMemorySSA(cfg, metadata, memorySSA); err != nil {
		return nil, fmt.Errorf("machine: OptIR region memory evidence: %w", err)
	}
	if len(cfg.Blocks) != 1 || cfg.Blocks[0].ID != cfg.Entry {
		return nil, fmt.Errorf("machine: OptIR region stores require one straight-line entry block")
	}
	if len(metadata.Regions) == 0 {
		return nil, fmt.Errorf("machine: OptIR region stores require at least one declared region")
	}
	if len(bindings) != len(metadata.Regions) {
		return nil, fmt.Errorf("machine: OptIR region stores have %d bindings for %d regions", len(bindings), len(metadata.Regions))
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
	written := make(map[optir.RegionID]bool, len(metadata.Regions))
	for _, operationMetadata := range metadata.Operations {
		site := operationMetadata.Site
		if len(operationMetadata.Accesses) != 1 {
			return nil, fmt.Errorf("machine: OptIR region store %d:%d has %d accesses, want one", site.Block, site.Index, len(operationMetadata.Accesses))
		}
		access := operationMetadata.Accesses[0]
		if access.Kind != optir.MemoryWrite || !access.WholeRegion || access.Volatile {
			return nil, fmt.Errorf("machine: OptIR region store %d:%d is not one whole nonvolatile write", site.Block, site.Index)
		}
		binding, exists := bindings[access.Region]
		if !exists {
			return nil, fmt.Errorf("machine: OptIR region store %d:%d names unbound region %q", site.Block, site.Index, access.Region)
		}
		block := optIRBlock(cfg, site.Block)
		if block == nil || site.Index < 0 || site.Index >= len(block.Operations) {
			return nil, fmt.Errorf("machine: OptIR region store metadata names missing operation %d:%d", site.Block, site.Index)
		}
		operation := block.Operations[site.Index]
		if operation.Code != optir.OpStoreRegion || len(operation.Results) != 0 || len(operation.Operands) != 1 || len(operation.Attributes) != 0 ||
			len(operation.Effects) != 1 || operation.Effects[0] != optir.EffectWriteMemory {
			return nil, fmt.Errorf("machine: OptIR operation %d:%d is not a canonical region store", site.Block, site.Index)
		}
		operandType, exists := types[operation.Operands[0]]
		if !exists {
			return nil, fmt.Errorf("machine: OptIR region store %d:%d operand %d has no type", site.Block, site.Index, operation.Operands[0])
		}
		if err := validateOptIRScalarGlobal(operandType, binding.Global); err != nil {
			return nil, fmt.Errorf("machine: OptIR region %q global %q: %w", access.Region, binding.Symbol, err)
		}
		authorized, exists := template.Globals[binding.Symbol]
		if !exists {
			return nil, fmt.Errorf("machine: OptIR memory region %q global %q is not authorized by the assembler template", access.Region, binding.Symbol)
		}
		if authorized != binding.Global {
			return nil, fmt.Errorf("machine: OptIR memory region %q global %q does not match the assembler template", access.Region, binding.Symbol)
		}
		stores[site] = binding
		written[access.Region] = true
	}
	if len(stores) == 0 {
		return nil, fmt.Errorf("machine: OptIR region memory has no stores")
	}
	for _, region := range metadata.Regions {
		if !written[region] {
			return nil, fmt.Errorf("machine: OptIR memory region %q is declared but not stored", region)
		}
	}
	return &optIRRegionStoreSelection{stores: stores}, nil
}

func validateOptIRScalarGlobal(typ optir.Type, global asm.Global) error {
	bits, ok := optIRScalarGlobalBits(typ)
	if !ok {
		return fmt.Errorf("type %s is not an admitted scalar", typ)
	}
	if global.Aggregate || global.Size != 0 {
		return fmt.Errorf("aggregate or sized storage is outside the scalar region-store subset")
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
