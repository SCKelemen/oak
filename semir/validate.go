package semir

import "fmt"

func (m Module) Validate() error {
	definitions := make(map[string]struct{}, len(m.Definitions))
	for _, definition := range m.Definitions {
		if definition.Name == "" {
			return fmt.Errorf("semantic definition has empty name")
		}
		if _, exists := definitions[definition.Name]; exists {
			return fmt.Errorf("duplicate semantic definition %q", definition.Name)
		}
		definitions[definition.Name] = struct{}{}
		if err := definition.Validate(); err != nil {
			return fmt.Errorf("definition %q: %w", definition.Name, err)
		}
	}

	protocols := make(map[string]struct{}, len(m.Protocols))
	for _, protocol := range m.Protocols {
		if protocol.Name == "" {
			return fmt.Errorf("protocol has empty name")
		}
		if _, exists := protocols[protocol.Name]; exists {
			return fmt.Errorf("duplicate protocol %q", protocol.Name)
		}
		protocols[protocol.Name] = struct{}{}
		if err := protocol.Validate(); err != nil {
			return fmt.Errorf("protocol %q: %w", protocol.Name, err)
		}
	}

	for _, definition := range m.Definitions {
		if definition.Protocol == "" {
			continue
		}
		if _, exists := protocols[definition.Protocol]; !exists {
			return fmt.Errorf("definition %q references unknown protocol %q", definition.Name, definition.Protocol)
		}
	}
	return nil
}

func (d Definition) Validate() error {
	if d.Type.Kind == TypeInvalid {
		return fmt.Errorf("type axis is unspecified")
	}
	if err := validateUniqueNames("type parameter", typeParameterNames(d.Type.Parameters)); err != nil {
		return err
	}
	if err := validateUniqueNames("field", fieldNames(d.Type.Fields)); err != nil {
		return err
	}
	if err := validateUniqueNames("variant", variantNames(d.Type.Variants)); err != nil {
		return err
	}
	if d.Representation.Alignment != 0 && !isPowerOfTwo(d.Representation.Alignment) {
		return fmt.Errorf("representation alignment %d is not a power of two", d.Representation.Alignment)
	}
	if err := d.Authority.Validate(); err != nil {
		return err
	}
	if err := validatePropositions(d.Propositions); err != nil {
		return err
	}
	return nil
}

func (a Authority) Validate() error {
	required := make(map[string]struct{}, len(a.RequiredEffects))
	for _, effect := range a.RequiredEffects {
		key, err := effectKey(effect)
		if err != nil {
			return err
		}
		if _, exists := required[key]; exists {
			return fmt.Errorf("duplicate required effect %q", key)
		}
		required[key] = struct{}{}
	}

	forbidden := make(map[string]struct{}, len(a.ForbiddenEffects))
	for _, effect := range a.ForbiddenEffects {
		key, err := effectKey(effect)
		if err != nil {
			return err
		}
		if _, exists := forbidden[key]; exists {
			return fmt.Errorf("duplicate forbidden effect %q", key)
		}
		if _, exists := required[key]; exists {
			return fmt.Errorf("effect %q is both required and forbidden", key)
		}
		forbidden[key] = struct{}{}
	}

	capabilities := make(map[string]struct{}, len(a.Capabilities))
	for _, capability := range a.Capabilities {
		if capability.Name == "" {
			return fmt.Errorf("capability has empty name")
		}
		key := qualified(capability.Namespace, capability.Name)
		if _, exists := capabilities[key]; exists {
			return fmt.Errorf("duplicate capability %q", key)
		}
		capabilities[key] = struct{}{}
	}
	return nil
}

func (p Protocol) Validate() error {
	if p.Name == "" {
		return fmt.Errorf("empty name")
	}
	states := make(map[string]struct{}, len(p.States))
	for _, state := range p.States {
		if state.Name == "" {
			return fmt.Errorf("state has empty name")
		}
		if _, exists := states[state.Name]; exists {
			return fmt.Errorf("duplicate state %q", state.Name)
		}
		states[state.Name] = struct{}{}
	}
	if len(states) == 0 {
		return fmt.Errorf("has no states")
	}
	if _, exists := states[p.Initial]; !exists {
		return fmt.Errorf("initial state %q does not exist", p.Initial)
	}

	transitions := make(map[string]struct{}, len(p.Transitions))
	for _, transition := range p.Transitions {
		if transition.Name == "" {
			return fmt.Errorf("transition has empty name")
		}
		if _, exists := transitions[transition.Name]; exists {
			return fmt.Errorf("duplicate transition %q", transition.Name)
		}
		transitions[transition.Name] = struct{}{}
		if _, exists := states[transition.From]; !exists {
			return fmt.Errorf("transition %q references unknown source state %q", transition.Name, transition.From)
		}
		if _, exists := states[transition.To]; !exists {
			return fmt.Errorf("transition %q references unknown target state %q", transition.Name, transition.To)
		}
		if err := validatePropositions(transition.Requires); err != nil {
			return fmt.Errorf("transition %q: %w", transition.Name, err)
		}
		for _, effect := range transition.Effects {
			if _, err := effectKey(effect); err != nil {
				return fmt.Errorf("transition %q: %w", transition.Name, err)
			}
		}
	}
	if err := validatePropositions(p.Invariants); err != nil {
		return fmt.Errorf("invariant: %w", err)
	}
	for _, property := range append(append([]TemporalProperty{}, p.Assumptions...), p.Guarantees...) {
		if property.Name == "" {
			return fmt.Errorf("temporal property has empty name")
		}
		if err := property.Formula.Validate(); err != nil {
			return fmt.Errorf("temporal property %q: %w", property.Name, err)
		}
	}
	return nil
}

func (e Expr) Validate() error {
	switch e.Kind {
	case ExprRef:
		if e.Ref == "" {
			return fmt.Errorf("reference expression has empty name")
		}
		return nil
	case ExprInt, ExprBool:
		return nil
	case ExprApply:
		arity, ok := operatorArity(e.Op)
		if !ok {
			return fmt.Errorf("unknown operator %q", e.Op)
		}
		if len(e.Args) != arity {
			return fmt.Errorf("operator %q expects %d arguments, got %d", e.Op, arity, len(e.Args))
		}
		for i, arg := range e.Args {
			if err := arg.Validate(); err != nil {
				return fmt.Errorf("argument %d: %w", i, err)
			}
		}
		return nil
	default:
		return fmt.Errorf("invalid expression kind %q", e.Kind)
	}
}

func (t TemporalExpr) Validate() error {
	switch t.Kind {
	case TemporalAtom:
		if t.Atom == "" {
			return fmt.Errorf("temporal atom has empty name")
		}
		if len(t.Args) != 0 {
			return fmt.Errorf("temporal atom cannot have arguments")
		}
		return nil
	case TemporalNot, TemporalAlways, TemporalEventually, TemporalNext:
		return t.validateArity(1)
	case TemporalAnd, TemporalOr, TemporalUntil, TemporalImplies:
		return t.validateArity(2)
	default:
		return fmt.Errorf("invalid temporal expression kind %q", t.Kind)
	}
}

func (t TemporalExpr) validateArity(arity int) error {
	if len(t.Args) != arity {
		return fmt.Errorf("temporal operator %q expects %d arguments, got %d", t.Kind, arity, len(t.Args))
	}
	for i, arg := range t.Args {
		if err := arg.Validate(); err != nil {
			return fmt.Errorf("argument %d: %w", i, err)
		}
	}
	return nil
}

func validatePropositions(propositions []Proposition) error {
	names := make(map[string]struct{}, len(propositions))
	for _, proposition := range propositions {
		if proposition.Name == "" {
			return fmt.Errorf("proposition has empty name")
		}
		if _, exists := names[proposition.Name]; exists {
			return fmt.Errorf("duplicate proposition %q", proposition.Name)
		}
		names[proposition.Name] = struct{}{}
		if proposition.Status == "" {
			return fmt.Errorf("proposition %q has no proof status", proposition.Name)
		}
		if err := proposition.Expr.Validate(); err != nil {
			return fmt.Errorf("proposition %q: %w", proposition.Name, err)
		}
	}
	return nil
}

func operatorArity(op Operator) (int, bool) {
	switch op {
	case OpNot:
		return 1, true
	case OpAnd, OpOr, OpEq, OpNe, OpLt, OpLe, OpGt, OpGe, OpAdd, OpSub, OpMul, OpDiv, OpMod:
		return 2, true
	default:
		return 0, false
	}
}

func effectKey(effect Effect) (string, error) {
	if effect.Name == "" {
		return "", fmt.Errorf("effect has empty name")
	}
	return qualified(effect.Namespace, effect.Name), nil
}

func qualified(namespace, name string) string {
	if namespace == "" {
		return name
	}
	return namespace + "." + name
}

func isPowerOfTwo(value uint32) bool {
	return value != 0 && value&(value-1) == 0
}

func validateUniqueNames(kind string, names []string) error {
	seen := make(map[string]struct{}, len(names))
	for _, name := range names {
		if name == "" {
			return fmt.Errorf("%s has empty name", kind)
		}
		if _, exists := seen[name]; exists {
			return fmt.Errorf("duplicate %s %q", kind, name)
		}
		seen[name] = struct{}{}
	}
	return nil
}

func typeParameterNames(parameters []TypeParameter) []string {
	names := make([]string, len(parameters))
	for i, parameter := range parameters {
		names[i] = parameter.Name
	}
	return names
}

func fieldNames(fields []Field) []string {
	names := make([]string, len(fields))
	for i, field := range fields {
		names[i] = field.Name
	}
	return names
}

func variantNames(variants []Variant) []string {
	names := make([]string, len(variants))
	for i, variant := range variants {
		names[i] = variant.Name
	}
	return names
}
