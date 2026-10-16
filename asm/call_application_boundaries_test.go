package asm

import "testing"

func TestMachineCallApplicationsVisitAllProofRoots(t *testing.T) {
	want := map[string]bool{}
	application := func(name string) *term {
		name = callApplicationName(name, "")
		want[name] = true
		return applyTerm(name, 32, paramTerm("input", 32))
	}
	writes := func(name string) map[string][]*spanWrite {
		return map[string][]*spanWrite{"memory": {{
			index: application(name + "_index"),
			value: application(name + "_value"),
			guard: application(name + "_guard"),
		}}}
	}
	result := application("result")
	// Both nested application arguments and ordinary DAG edges are relevant.
	shared := application("nested")
	result.args = append(result.args, shared, shared)
	conditionName := callApplicationName("selector", "")
	want[conditionName] = true
	condition := applyTerm(conditionName, 1, paramTerm("condition", 1))
	result = iteTerm(condition, result, application("other_branch"))
	execution := &pathExecutor{
		moreResults: []*term{application("more_result")},
		trap:        application("root_trap"),
		cells:       map[string]*term{"global": application("cell")},
		writes:      writes("root_write"),
		loops: []*loopEvent{{
			cond:       application("condition"),
			headerTrap: application("header_trap"),
			bodyTrap:   application("body_trap"),
			reached:    application("reached"),
			oakPath:    application("oak_path"),
			header:     map[string]*term{"value": application("header")},
			fresh:      map[string]*term{"value": application("fresh")},
			next:       map[string]*term{"value": application("next")},
			entry:      writes("entry"),
			writes:     writes("loop_write"),
		}},
	}
	got := machineCallApplications(result, execution)
	if len(got) != len(want) {
		t.Fatalf("application count = %d, want %d", len(got), len(want))
	}
	for name := range want {
		if !got[name] {
			t.Errorf("missing application %s", name)
		}
	}
	// A non-nil empty set is intentional: no machine call remains, so all
	// source calls must be expanded rather than retaining an opaque boundary.
	if empty := machineCallApplications(nil, nil); empty == nil || len(empty) != 0 {
		t.Fatalf("empty machine execution must yield an explicit empty set: %v", empty)
	}
}

func TestRetainCallApplicationMatchesExactCallee(t *testing.T) {
	for _, test := range []struct {
		name         string
		applications map[string]bool
		want         bool
	}{
		{"unrestricted", nil, true},
		{"no machine calls", map[string]bool{}, false},
		{"scalar result", map[string]bool{"call:callee:result": true}, true},
		{"array leaf", map[string]bool{"call:callee:result[3]": true}, true},
		{"record leaf", map[string]bool{"call:callee:result.field": true}, true},
		{"nested leaf", map[string]bool{"call:callee:result.field[3]": true}, true},
		{"different callee", map[string]bool{"call:callee_extra:result": true}, false},
		{"longer result name", map[string]bool{"call:callee:result_extra": true}, false},
	} {
		t.Run(test.name, func(t *testing.T) {
			lo := &oakLowering{machineApplications: test.applications}
			if got := lo.retainCallApplication("callee"); got != test.want {
				t.Fatalf("retain = %v, want %v", got, test.want)
			}
		})
	}
}
