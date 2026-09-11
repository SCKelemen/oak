package compiler

import (
	"strings"
	"testing"
)

// Conformance of a hand-written TLA+ module against a projection
// (docs/spec/112-protocols.md section 4a): the generated module agrees with
// itself, hand-edited copies are reported with the action and line that
// differ, spellings that differ only in whitespace or parentheses agree,
// and a module outside the normal form is unsupported, not judged.
func projectionOf(t *testing.T, source string) (string, TLAConformance) {
	t.Helper()
	tree, err := New().WithSource("p.oak", source).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	decl := Protocols(tree)[0]
	module, err := ProtocolTLAWithRecords(decl, "p.oak", RecordDeclarations(tree.Root))
	if err != nil {
		t.Fatal(err)
	}
	report, err := ProtocolConformance(decl, module, RecordDeclarations(tree.Root))
	if err != nil {
		t.Fatal(err)
	}
	return module, report
}

func conformanceOf(t *testing.T, source, module string) TLAConformance {
	t.Helper()
	tree, err := New().WithSource("p.oak", source).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	report, err := ProtocolConformance(Protocols(tree)[0], module, RecordDeclarations(tree.Root))
	if err != nil {
		t.Fatal(err)
	}
	return report
}

func TestTLAConformanceSelf(t *testing.T) {
	for name, source := range map[string]string{"slots": slotsProtocolSource, "replication": replicationProtocolSource} {
		t.Run(name, func(t *testing.T) {
			_, report := projectionOf(t, source)
			if !report.Conforms {
				t.Fatalf("the projection must agree with itself:\n%s", FormatTLAConformance(report))
			}
		})
	}
}

func TestTLAConformanceSpellingsAgree(t *testing.T) {
	module, _ := projectionOf(t, slotsProtocolSource)
	// Extra parentheses, spacing, reordered conjuncts and disjuncts, and a
	// comment are not differences.
	edited := strings.Replace(module, "state = \"Running\" /\\ ((who < 2) /\\ ~(parked[who]))", "(((who < 2)) /\\ ~(parked[who]))   /\\   state = \"Running\"", 1)
	edited = strings.Replace(edited, "Halt ==\n", "\\* the halt action\nHalt ==\n", 1)
	report := conformanceOf(t, slotsProtocolSource, edited)
	if !report.Conforms {
		t.Fatalf("spelling differences must not be reported:\n%s", FormatTLAConformance(report))
	}
}

func TestTLAConformanceReportsDifferences(t *testing.T) {
	module, _ := projectionOf(t, slotsProtocolSource)
	for name, tc := range map[string]struct {
		edit     func(string) string
		kind     string
		action   string
		contains string
	}{
		"changed guard constant": {
			edit: func(m string) string { return strings.Replace(m, "(woken[who] < 2)", "(woken[who] < 3)", 1) },
			kind: "missing-line", action: "Wake", contains: "woken[who]<2",
		},
		"swapped target": {
			edit: func(m string) string { return strings.Replace(m, "state' = \"Halted\"", "state' = \"Running\"", 1) },
			kind: "missing-line", action: "Halt",
		},
		"dropped line": {
			edit: func(m string) string {
				lines := strings.Split(m, "\n")
				var out []string
				dropped := false
				for _, l := range lines {
					if !dropped && strings.HasPrefix(strings.TrimSpace(l), "state = \"Running\" /\\ ((who < 2) /\\ ~(parked[who]))") {
						dropped = true
						continue
					}
					out = append(out, l)
				}
				return strings.Join(out, "\n")
			},
			kind: "missing-line", action: "Park",
		},
		"renamed action": {
			edit: func(m string) string { return strings.Replace(m, "Halt ==", "Stop ==", 1) },
			kind: "missing-action", action: "Halt",
		},
		"extra unchanged variable": {
			edit: func(m string) string {
				return strings.Replace(m, "UNCHANGED <<parked, woken, last>>", "UNCHANGED <<parked, woken>>", 1)
			},
			kind: "missing-line", action: "Halt",
		},
	} {
		t.Run(name, func(t *testing.T) {
			report := conformanceOf(t, slotsProtocolSource, tc.edit(module))
			if report.Conforms {
				t.Fatalf("the edit must be reported")
			}
			found := false
			for _, d := range report.Differences {
				if d.Kind == tc.kind && d.Action == tc.action && (tc.contains == "" || strings.Contains(d.Left+d.Right, tc.contains)) {
					found = true
				}
			}
			if !found {
				t.Fatalf("expected a %s difference on %s, got:\n%s", tc.kind, tc.action, FormatTLAConformance(report))
			}
		})
	}
}

func TestTLAConformanceUnsupportedForm(t *testing.T) {
	module, _ := projectionOf(t, slotsProtocolSource)
	// A disjunct without the state conjuncts is outside the normal form.
	edited := strings.Replace(module, "Halt ==\n    state = \"Running\"", "Halt ==\n    \\E k \\in 0..1 : parked[k] /\\ state' = \"Halted\"\n    \\/ state = \"Running\"", 1)
	report := conformanceOf(t, slotsProtocolSource, edited)
	if report.Conforms || len(report.Unsupported) == 0 {
		t.Fatalf("a form outside the normal form must be unsupported, not judged:\n%s", FormatTLAConformance(report))
	}
	if !strings.Contains(strings.Join(report.Unsupported, "\n"), "Halt") {
		t.Fatalf("the unsupported note must name the action: %v", report.Unsupported)
	}
}
