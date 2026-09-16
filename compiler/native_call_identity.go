package compiler

import (
	"fmt"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

type optIRCallOccurrence struct {
	site   uint32
	target string
}

type machineCallForm uint8

const (
	machineNonCall machineCallForm = iota
	machineDirectCall
	machineOpaqueCall
)

// checkOptIRMachineCallIdentity binds a fully materialized machine body back
// to the exact call occurrences in its fingerprinted OptIR CFG. Call-site
// identity is compiler metadata only: it is never emitted into the object.
// Comparing occurrences as a map deliberately permits physical block-order
// changes while preserving exact static multiplicity and target identity.
func checkOptIRMachineCallIdentity(cfg optir.CFG, function *asm.Function) error {
	if function == nil {
		return fmt.Errorf("compiler: OptIR machine-call identity has no machine function")
	}
	if function.Body != nil {
		return fmt.Errorf("compiler: OptIR machine-call identity requires the selector's body-free output")
	}
	if function.Arch != asm.ArchArm64 && function.Arch != asm.ArchRV64 {
		return fmt.Errorf("compiler: OptIR machine-call identity does not recognize architecture %q", function.Arch)
	}
	if function.Name != cfg.Name {
		return fmt.Errorf("compiler: OptIR function %q materialized as machine function %q", cfg.Name, function.Name)
	}
	expected, err := checkedOptIRCallOccurrences(cfg)
	if err != nil {
		return fmt.Errorf("compiler: OptIR machine-call authority: %w", err)
	}
	actual, err := checkedMachineCallOccurrences(function)
	if err != nil {
		return fmt.Errorf("compiler: OptIR machine-call materialization: %w", err)
	}
	if len(actual) != len(expected) {
		return fmt.Errorf("compiler: OptIR machine-call identity has %d materialized occurrence(s), want %d", len(actual), len(expected))
	}
	for site, target := range expected {
		materialized, exists := actual[site]
		if !exists {
			return fmt.Errorf("compiler: OptIR call site %d to %q is missing from the machine body", site, target)
		}
		if materialized != target {
			return fmt.Errorf("compiler: OptIR call site %d targets %q in the machine body, want %q", site, materialized, target)
		}
	}
	return nil
}

func checkedOptIRCallOccurrences(cfg optir.CFG) (map[uint32]string, error) {
	if err := optir.Verify(cfg); err != nil {
		return nil, err
	}
	layout, err := optir.AnalyzeBlockLayout(cfg)
	if err != nil {
		return nil, err
	}
	if err := optir.VerifyBlockLayout(cfg, layout); err != nil {
		return nil, err
	}
	blocks := make(map[optir.BlockID]optir.Block, len(cfg.Blocks))
	for _, block := range cfg.Blocks {
		blocks[block.ID] = block
	}
	out := map[uint32]string{}
	for _, blockID := range layout.Order {
		block, exists := blocks[blockID]
		if !exists {
			return nil, fmt.Errorf("verified block layout names missing block %d", blockID)
		}
		for _, operation := range block.Operations {
			if operation.Code != optir.OpCall {
				continue
			}
			if len(operation.Results) != 1 || operation.Results[0].ID == 0 {
				return nil, fmt.Errorf("block %d has a call without one nonzero result identity", blockID)
			}
			if len(operation.Attributes) != 1 || operation.Attributes[0].Name != optir.AttributeCallee || operation.Attributes[0].Value == "" {
				return nil, fmt.Errorf("block %d call site %d has no unique direct callee", blockID, operation.Results[0].ID)
			}
			site := uint32(operation.Results[0].ID)
			if _, duplicate := out[site]; duplicate {
				return nil, fmt.Errorf("block %d repeats call-site identity %d", blockID, site)
			}
			out[site] = operation.Attributes[0].Value
		}
	}
	return out, nil
}

func checkedMachineCallOccurrences(function *asm.Function) (map[uint32]string, error) {
	out := map[uint32]string{}
	for _, item := range function.Items {
		instruction, isInstruction := item.(asm.Instruction)
		if !isInstruction {
			continue
		}
		form := classifyMachineCall(function.Arch, instruction.Mnemonic)
		switch form {
		case machineOpaqueCall:
			return nil, fmt.Errorf("line %d uses unsupported indirect or linking call %q", instruction.Line, instruction.Mnemonic)
		case machineNonCall:
			if instruction.OptIRCallSite != 0 {
				return nil, fmt.Errorf("line %d tags non-call %q as OptIR call site %d", instruction.Line, instruction.Mnemonic, instruction.OptIRCallSite)
			}
			continue
		}
		if instruction.OptIRCallSite == 0 {
			return nil, fmt.Errorf("line %d has an untagged direct call", instruction.Line)
		}
		if len(instruction.Operands) != 1 {
			return nil, fmt.Errorf("line %d direct call has %d operands, want one symbol", instruction.Line, len(instruction.Operands))
		}
		symbol, ok := instruction.Operands[0].(asm.Symbol)
		if !ok || symbol.Name == "" || symbol.Lo12 {
			return nil, fmt.Errorf("line %d direct call does not have one plain nonempty symbol", instruction.Line)
		}
		if _, duplicate := out[instruction.OptIRCallSite]; duplicate {
			return nil, fmt.Errorf("line %d repeats OptIR call-site identity %d", instruction.Line, instruction.OptIRCallSite)
		}
		out[instruction.OptIRCallSite] = symbol.Name
	}
	return out, nil
}

func classifyMachineCall(arch, mnemonic string) machineCallForm {
	switch arch {
	case asm.ArchRV64:
		switch mnemonic {
		case "call":
			return machineDirectCall
		case "jal", "jalr", "tail":
			return machineOpaqueCall
		}
	case asm.ArchArm64:
		switch mnemonic {
		case "bl":
			return machineDirectCall
		case "blr", "blraa", "blrab", "blraaz", "blrabz":
			return machineOpaqueCall
		}
	}
	return machineNonCall
}
