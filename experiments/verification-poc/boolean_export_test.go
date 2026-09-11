package main

import (
	"testing"
)

func evalBooleanProgram(p []BooleanInstruction, inputs []bool) bool {
	values := make([]bool, len(p))
	for i, n := range p {
		switch n.Op {
		case "bool":
			values[i] = n.Value
		case "var":
			values[i] = inputs[n.Index]
		case "!":
			values[i] = !values[n.Left]
		case "&&":
			values[i] = values[n.Left] && values[n.Right]
		case "||":
			values[i] = values[n.Left] || values[n.Right]
		default:
			panic("unexpected export operator")
		}
	}
	return values[len(values)-1]
}

func TestBooleanModelExport(t *testing.T) {
	for _, name := range []string{"publication", "publication-relaxed"} {
		t.Run(name, func(t *testing.T) {
			m, err := loadModel("examples/native/" + name + ".json")
			if err != nil {
				t.Fatal(err)
			}
			b, err := exportBoolean(m)
			if err != nil {
				t.Fatal(err)
			}
			if b.SourceHash != m.Document.SourceHash || b.SemanticDigest != m.Digest {
				t.Fatal("source identity lost")
			}
			states, err := m.states()
			if err != nil {
				t.Fatal(err)
			}
			for _, s := range states {
				input := make([]bool, len(m.Fields))
				for i, f := range m.Fields {
					input[i] = s[f.Name].(bool)
				}
				for role, p := range map[string][]BooleanInstruction{"initial": b.Initial, "invariant": b.Invariant} {
					if evalBooleanProgram(p, input) != truth(m.Terms[role], s, nil) {
						t.Fatalf("%s differs for %v", role, s)
					}
				}
				for _, next := range states {
					paired := make([]bool, 2*len(m.Fields))
					for i, f := range m.Fields {
						paired[2*i] = s[f.Name].(bool)
						paired[2*i+1] = next[f.Name].(bool)
					}
					if evalBooleanProgram(b.Step, paired) != truth(m.Terms["step"], s, next) {
						t.Fatalf("step differs for %v -> %v", s, next)
					}
				}
			}
		})
	}
}

func TestBooleanExportRejectsNumericModel(t *testing.T) {
	m, err := loadModel("examples/native/counter.json")
	if err != nil {
		t.Fatal(err)
	}
	if _, err := exportBoolean(m); err == nil {
		t.Fatal("numeric model exported as Boolean")
	}
}

func TestBooleanExportConditional(t *testing.T) {
	m, err := loadModel("examples/native/publication.json")
	if err != nil {
		t.Fatal(err)
	}
	a := &Node{Op: "var", Type: "Bool", State: "s", Field: "written"}
	b := &Node{Op: "var", Type: "Bool", State: "s", Field: "published"}
	m.Terms["invariant"] = expression("ite", "Bool", a, expression("!=", "Bool", a, b), b)
	bundle, err := exportBoolean(m)
	if err != nil {
		t.Fatal(err)
	}
	states, _ := m.states()
	for _, s := range states {
		inputs := make([]bool, len(m.Fields))
		for i, f := range m.Fields {
			inputs[i] = s[f.Name].(bool)
		}
		if evalBooleanProgram(bundle.Invariant, inputs) != truth(m.Terms["invariant"], s, nil) {
			t.Fatal("conditional translation differs")
		}
	}
}
