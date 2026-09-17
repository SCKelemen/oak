package compiler

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"

	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/target"
)

// EmissionReport is diagnostic provenance, not a semantic certificate. Recipes
// identify producer revisions and inputs; a byte hash must come from the
// actual output validator. No report field can authorize a verified verdict.
type EmissionReport struct {
	Target target.Description `json:"target"`
	Steps  []EmissionStep     `json:"steps"`
}

type EmissionStep struct {
	Artifact     opt.ArtifactKey   `json:"artifact"`
	Dependencies []opt.ArtifactKey `json:"dependencies"`
}

// emissionBackend is a small typed adapter, not a universal ISA interface.
// Materialization is untrusted; admission determines the output profile's
// policy. A byte/type-only admission must never be described as translation
// verification. Callbacks consume owned inputs and must not mutate them.
type emissionBackend[I, O any] struct {
	name, materializeRevision, admissionRevision string
	materialize                                  func(context.Context, target.Description, I) (O, error)
	admit                                        func(context.Context, target.Description, O) (O, error)
}

func runEmissionGraph[I, O any](ctx context.Context, description target.Description,
	inputKey opt.ArtifactKey, input I, backend emissionBackend[I, O],
) (O, EmissionReport, error) {
	var zero O
	if err := description.Validate(); err != nil {
		return zero, EmissionReport{}, err
	}
	if backend.name == "" || backend.materializeRevision == "" || backend.admissionRevision == "" || backend.materialize == nil || backend.admit == nil {
		return zero, EmissionReport{}, fmt.Errorf("compiler: incomplete emission adapter")
	}
	encoded, err := json.Marshal(description) // a fixed, value-only schema
	if err != nil {
		return zero, EmissionReport{}, err
	}
	hash := sha256.Sum256(encoded)
	config, configTask := opt.RootArtifact(opt.ArtifactKey{
		Kind: opt.ArtifactSource, Name: "target.description.v1", Version: hex.EncodeToString(hash[:]),
	}, description)
	checked, checkedTask := opt.RootArtifact(inputKey, input)
	candidate, candidateTask := opt.DerivedArtifact2(opt.ArtifactCandidate, backend.name+".materialize",
		backend.materializeRevision, config, checked, backend.materialize)
	admitted, admittedTask := opt.DerivedArtifact2(opt.ArtifactAdmission, backend.name+".admit",
		backend.admissionRevision, config, candidate, backend.admit)
	tasks := []opt.ArtifactTask{configTask, checkedTask, candidateTask, admittedTask}
	graph, err := opt.NewArtifactGraph(tasks...)
	if err != nil {
		return zero, EmissionReport{}, err
	}
	byKey := make(map[opt.ArtifactKey]opt.ArtifactTask, len(tasks))
	for _, task := range tasks {
		byKey[task.Key] = task
	}
	// No cache: generic Go payloads do not imply a serialization/freeze contract.
	run, err := graph.Run(ctx, nil, admitted.Key())
	if err != nil {
		return zero, EmissionReport{}, err
	}
	output, err := admitted.Value(run)
	if err != nil {
		return zero, EmissionReport{}, err
	}
	report := EmissionReport{Target: description}
	for _, key := range run.Executed {
		report.Steps = append(report.Steps, EmissionStep{
			Artifact: key, Dependencies: append([]opt.ArtifactKey{}, byKey[key].Dependencies...),
		})
	}
	return output, report, nil
}

func (comp Compilation) requireBackend(backend target.Backend, entry string) (target.Description, error) {
	description, err := comp.options.Target.Describe()
	if err != nil {
		return target.Description{}, err
	}
	if description.Backend != backend {
		return target.Description{}, fmt.Errorf("target %s uses %s output, not %s", description.Target, description.Backend, entry)
	}
	return description, nil
}
