package main

import "fmt"

// BooleanProgram is a postorder DAG over the proved Lean Boolean vocabulary.
// Initial/invariant inputs use field indices; step uses 2*i for s and 2*i+1 for t.
type BooleanInstruction struct {
	Op string `json:"op"`
	Value bool `json:"value"`
	Index int `json:"index"`
	Left int `json:"left"`
	Right int `json:"right"`
}
type BooleanBundle struct {
	Format string `json:"format"`
	SourceHash string `json:"source_sha256"`
	SemanticDigest string `json:"semantic_digest"`
	Fields []string `json:"fields"`
	Initial []BooleanInstruction `json:"initial"`
	Step []BooleanInstruction `json:"step"`
	Invariant []BooleanInstruction `json:"invariant"`
}

func exportBoolean(m *Model) (*BooleanBundle, error) {
	b := &BooleanBundle{Format: "oak-boolean-model-1", SourceHash: m.Document.SourceHash, SemanticDigest: m.Digest}
	indices := map[string]int{}
	for i, f := range m.Fields {
		if f.Type != "Bool" { return nil, fmt.Errorf("Boolean proof export requires Bool fields: %s is %s", f.Name, f.Type) }
		indices[f.Name] = i
		b.Fields = append(b.Fields, f.Name)
	}
	compile := func(root *Node, paired bool) ([]BooleanInstruction, error) {
		program := []BooleanInstruction{}
		appendNode := func(n BooleanInstruction) (int, error) {
			if len(program) >= 4096 { return 0, fmt.Errorf("Boolean proof program exceeds 4096 nodes") }
			program = append(program, n)
			return len(program)-1, nil
		}
		var walk func(*Node) (int, error)
		walk = func(n *Node) (int, error) {
			if n == nil || n.Type != "Bool" { return 0, fmt.Errorf("Boolean proof export requires Boolean expressions") }
			if n.Op == "bool" { return appendNode(BooleanInstruction{Op:"bool", Value:n.B}) }
			if n.Op == "var" {
				i, ok := indices[n.Field]
				if !ok || (n.State != "s" && n.State != "t") || (!paired && n.State != "s") { return 0, fmt.Errorf("invalid Boolean state input") }
				if paired { i *= 2; if n.State == "t" { i++ } }
				return appendNode(BooleanInstruction{Op:"var", Index:i})
			}
			arity := map[string]int{"!":1,"&&":2,"||":2,"==":2,"!=":2,"ite":3}[n.Op]
			if arity == 0 || len(n.Args) != arity { return 0, fmt.Errorf("unsupported Boolean proof operator %s", n.Op) }
			// Desugar typed Boolean equality and conditionals before exporting.
			if n.Op == "==" || n.Op == "!=" {
				a, c := n.Args[0], n.Args[1]
				eq := expression("||", "Bool", expression("&&", "Bool", a, c), expression("&&", "Bool", expression("!", "Bool", a), expression("!", "Bool", c)))
				if n.Op == "!=" { eq = expression("!", "Bool", eq) }
				return walk(eq)
			}
			if n.Op == "ite" {
				a, c, d := n.Args[0], n.Args[1], n.Args[2]
				return walk(expression("||", "Bool", expression("&&", "Bool", a, c), expression("&&", "Bool", expression("!", "Bool", a), d)))
			}
			left, err := walk(n.Args[0]); if err != nil { return 0, err }
			right := 0
			if arity == 2 { right, err = walk(n.Args[1]); if err != nil { return 0, err } }
			return appendNode(BooleanInstruction{Op:n.Op, Left:left, Right:right})
		}
		_, err := walk(root)
		return program, err
	}
	var err error
	b.Initial, err = compile(m.Terms["initial"], false); if err != nil { return nil, err }
	b.Step, err = compile(m.Terms["step"], true); if err != nil { return nil, err }
	b.Invariant, err = compile(m.Terms["invariant"], false); if err != nil { return nil, err }
	return b, nil
}
