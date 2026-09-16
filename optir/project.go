package optir

import "fmt"

// Project lowers structured OptIR to a canonical CFG/SSA view. It validates
// the structured input first and independently verifies the result before
// returning it to an analysis.
func Project(function Function) (CFG, error) {
	maximum, err := validateStructured(function)
	if err != nil {
		return CFG{}, err
	}
	p := projector{
		cfg: CFG{
			Name:    function.Name,
			Results: append([]Type(nil), function.Results...),
			Facts:   cloneFacts(function.Facts),
		},
		nextValue: maximum + 1,
	}
	entry := p.newBlock()
	p.cfg.Entry = entry
	p.block(entry).Parameters = cloneValues(function.Parameters)
	last, err := p.emitRegion(function.Body, entry, nil)
	if err != nil {
		return CFG{}, err
	}
	p.block(last).Terminator = Terminator{
		Kind:   TerminatorReturn,
		Values: remapValues(function.Body.Yield, nil),
	}
	if err := Verify(p.cfg); err != nil {
		return CFG{}, fmt.Errorf("optir: projected CFG is invalid: %w", err)
	}
	return p.cfg, nil
}

type projector struct {
	cfg       CFG
	nextBlock BlockID
	nextValue ValueID
}

func (p *projector) newBlock() BlockID {
	id := p.nextBlock
	p.nextBlock++
	p.cfg.Blocks = append(p.cfg.Blocks, Block{ID: id})
	return id
}

func (p *projector) block(id BlockID) *Block {
	return &p.cfg.Blocks[int(id)]
}

func (p *projector) freshValue(template Value) Value {
	template.ID = p.nextValue
	p.nextValue++
	return template
}

func (p *projector) emitRegion(region Region, current BlockID, bindings map[ValueID]ValueID) (BlockID, error) {
	for _, node := range region.Nodes {
		switch {
		case node.Operation != nil:
			op := cloneOperation(*node.Operation)
			op.Operands = remapValues(op.Operands, bindings)
			for i := range op.Facts {
				op.Facts[i].Values = remapValues(op.Facts[i].Values, bindings)
			}
			p.block(current).Operations = append(p.block(current).Operations, op)
		case node.If != nil:
			branch := node.If
			thenBlock := p.newBlock()
			elseBlock := p.newBlock()
			mergeBlock := p.newBlock()
			p.block(current).Terminator = Terminator{
				Kind:      TerminatorCondBranch,
				Condition: remapValue(branch.Condition, bindings),
				True:      Edge{Target: thenBlock},
				False:     Edge{Target: elseBlock},
			}
			thenEnd, err := p.emitRegion(branch.Then, thenBlock, cloneBindings(bindings))
			if err != nil {
				return 0, err
			}
			p.block(thenEnd).Terminator = Terminator{
				Kind: TerminatorBranch,
				True: Edge{Target: mergeBlock, Arguments: remapValues(branch.Then.Yield, bindings)},
			}
			elseEnd, err := p.emitRegion(branch.Else, elseBlock, cloneBindings(bindings))
			if err != nil {
				return 0, err
			}
			p.block(elseEnd).Terminator = Terminator{
				Kind: TerminatorBranch,
				True: Edge{Target: mergeBlock, Arguments: remapValues(branch.Else.Yield, bindings)},
			}
			p.block(mergeBlock).Parameters = cloneValues(branch.Results)
			current = mergeBlock
		case node.While != nil:
			loop := node.While
			header := p.newBlock()
			body := p.newBlock()
			exit := p.newBlock()
			headerParameters := make([]Value, len(loop.Results))
			bodyParameters := make([]Value, len(loop.Results))
			for i, result := range loop.Results {
				headerParameters[i] = p.freshValue(Value{Type: result.Type, Name: result.Name, Source: result.Source})
				bodyParameters[i] = p.freshValue(Value{Type: result.Type, Name: result.Name, Source: result.Source})
			}
			p.block(header).Parameters = headerParameters
			p.block(body).Parameters = bodyParameters
			p.block(exit).Parameters = cloneValues(loop.Results)
			p.block(current).Terminator = Terminator{
				Kind: TerminatorBranch,
				True: Edge{Target: header, Arguments: remapValues(loop.Initial, bindings)},
			}

			conditionBindings := cloneBindings(bindings)
			for i, argument := range loop.Condition.Arguments {
				conditionBindings[argument.ID] = headerParameters[i].ID
			}
			conditionEnd, err := p.emitRegion(loop.Condition, header, conditionBindings)
			if err != nil {
				return 0, err
			}
			headerValues := valueIDs(headerParameters)
			p.block(conditionEnd).Terminator = Terminator{
				Kind:      TerminatorCondBranch,
				Condition: remapValue(loop.Condition.Yield[0], conditionBindings),
				True:      Edge{Target: body, Arguments: headerValues},
				False:     Edge{Target: exit, Arguments: headerValues},
			}

			bodyBindings := cloneBindings(bindings)
			for i, argument := range loop.Body.Arguments {
				bodyBindings[argument.ID] = bodyParameters[i].ID
			}
			bodyEnd, err := p.emitRegion(loop.Body, body, bodyBindings)
			if err != nil {
				return 0, err
			}
			p.block(bodyEnd).Terminator = Terminator{
				Kind: TerminatorBranch,
				True: Edge{Target: header, Arguments: remapValues(loop.Body.Yield, bodyBindings)},
			}
			current = exit
		default:
			return 0, fmt.Errorf("optir: empty structured node")
		}
	}
	return current, nil
}

func remapValue(value ValueID, bindings map[ValueID]ValueID) ValueID {
	if replacement, ok := bindings[value]; ok {
		return replacement
	}
	return value
}

func remapValues(values []ValueID, bindings map[ValueID]ValueID) []ValueID {
	out := make([]ValueID, len(values))
	for i, value := range values {
		out[i] = remapValue(value, bindings)
	}
	return out
}

func cloneBindings(bindings map[ValueID]ValueID) map[ValueID]ValueID {
	out := make(map[ValueID]ValueID, len(bindings))
	for from, to := range bindings {
		out[from] = to
	}
	return out
}

func valueIDs(values []Value) []ValueID {
	out := make([]ValueID, len(values))
	for i, value := range values {
		out[i] = value.ID
	}
	return out
}

func cloneValues(values []Value) []Value {
	return append([]Value(nil), values...)
}

func cloneFacts(facts []Fact) []Fact {
	out := make([]Fact, len(facts))
	for i, fact := range facts {
		out[i] = fact
		out[i].Values = append([]ValueID(nil), fact.Values...)
		out[i].Dependencies = append([]string(nil), fact.Dependencies...)
	}
	return out
}

func cloneOperation(operation Operation) Operation {
	operation.Results = cloneValues(operation.Results)
	operation.Operands = append([]ValueID(nil), operation.Operands...)
	operation.Effects = append([]Effect(nil), operation.Effects...)
	operation.Attributes = append([]Attribute(nil), operation.Attributes...)
	operation.Facts = cloneFacts(operation.Facts)
	return operation
}
