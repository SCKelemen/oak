package compiler

import (
	"context"
	"errors"
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/target"
)

func TestEmissionGraphIdentityAndAdmission(t *testing.T) {
	description, _ := (target.Target{OS: target.OSCore, Arch: target.ArchWasm32}).Describe()
	input := opt.ArtifactKey{Kind: opt.ArtifactChecked, Name: "test.input", Version: "input-v1"}
	var calls []string
	backend := emissionBackend[string, string]{
		name: "test", materializeRevision: "encode-v1", admissionRevision: "check-v1",
		materialize: func(_ context.Context, d target.Description, value string) (string, error) {
			calls = append(calls, "materialize")
			return d.Target.String() + ":" + value, nil
		},
		admit: func(_ context.Context, d target.Description, value string) (string, error) {
			calls = append(calls, "admit")
			if !strings.HasPrefix(value, d.Target.String()+":") {
				return "", errors.New("materialized output names the wrong target")
			}
			return value, nil
		},
	}
	run := func(d target.Description, key opt.ArtifactKey, b emissionBackend[string, string]) EmissionReport {
		t.Helper()
		out, report, err := runEmissionGraph(context.Background(), d, key, "input", b)
		if err != nil || out == "" || len(report.Steps) != 4 {
			t.Fatalf("emission: %q, %+v, %v", out, report, err)
		}
		seen := map[opt.ArtifactKey]bool{}
		for _, step := range report.Steps {
			for _, dependency := range step.Dependencies {
				if !seen[dependency] {
					t.Fatal("dependency was not executed first", step)
				}
			}
			seen[step.Artifact] = true
		}
		last := report.Steps[3]
		if last.Artifact.Kind != opt.ArtifactAdmission || len(last.Dependencies) != 2 || last.Dependencies[0].Name != "target.description.v1" || last.Dependencies[1] != report.Steps[2].Artifact {
			t.Fatal("output bypassed materialization/admission", report)
		}
		return report
	}
	first := run(description, input, backend)
	if !reflect.DeepEqual(calls, []string{"materialize", "admit"}) {
		t.Fatal("incorrect stage order", calls)
	}
	if again := run(description, input, backend); !reflect.DeepEqual(first, again) {
		t.Fatal("unstable recipe identity")
	}
	for _, variant := range []string{"input", "target", "encoder", "validator"} {
		d, key, b := description, input, backend
		switch variant {
		case "input":
			key.Version = "input-v2"
		case "target":
			d, _ = (target.Target{OS: target.OSLinux, Arch: target.ArchArm64}).Describe()
		case "encoder":
			b.materializeRevision = "encode-v2"
		case "validator":
			b.admissionRevision = "check-v2"
		}
		if next := run(d, key, b); next.Steps[3].Artifact == first.Steps[3].Artifact {
			t.Fatal("changed input retained admission identity", variant)
		}
	}
	for _, failAt := range []string{"materialize", "admit", "cancel", "cancel after materialize", "description", "missing adapter"} {
		ctx, cancel := context.WithCancel(context.Background())
		d, b := description, backend
		sentinel := errors.New("refused")
		switch failAt {
		case "materialize":
			b.materialize = func(context.Context, target.Description, string) (string, error) { return "partial", sentinel }
		case "admit":
			b.admit = func(context.Context, target.Description, string) (string, error) { return "partial", sentinel }
		case "cancel":
			cancel()
		case "cancel after materialize":
			b.materialize = func(context.Context, target.Description, string) (string, error) {
				cancel()
				return "partial", nil
			}
		case "description":
			d.PointerBits = 64
		case "missing adapter":
			b.admit = nil
		}
		calls = nil
		out, report, err := runEmissionGraph(ctx, d, input, "input", b)
		cancel()
		if err == nil || out != "" || len(report.Steps) != 0 {
			t.Fatal("failure leaked output/evidence", failAt, out, report, err)
		}
		if failAt == "cancel" && (!errors.Is(err, context.Canceled) || len(calls) != 0) {
			t.Fatal("cancelled graph computed output", calls, err)
		}
	}
}

func TestEmissionUnknownTargetRefusesBeforeChecking(t *testing.T) {
	comp := New().WithTarget(target.Target{OS: "unknown", Arch: "unknown"}).WithSource("bad.oak", "not valid Oak")
	if _, err := comp.EmitC().Get(); err == nil || !strings.Contains(err.Error(), "target unknown/unknown") {
		t.Fatal("unknown target emitted C")
	}
	if _, err := comp.EmitNative(HostObjectFormat()).Get(); err == nil || !strings.Contains(err.Error(), "target unknown/unknown") {
		t.Fatal("unknown target emitted native output")
	}
}
