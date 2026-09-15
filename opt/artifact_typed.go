package opt

import (
	"context"
	"fmt"
	"reflect"
)

// ArtifactRef is a typed reference to one exact artifact recipe. It removes
// payload casts from compiler pass wiring without changing the graph's opaque
// storage or treating a Go type as evidence that an artifact is admissible.
type ArtifactRef[T any] struct {
	key ArtifactKey
}

// Key returns the exact untyped identity used by ArtifactGraph.
func (reference ArtifactRef[T]) Key() ArtifactKey { return reference.key }

// Value reads this reference from a completed run and fails closed when the
// artifact is absent or its opaque payload has the wrong Go type.
func (reference ArtifactRef[T]) Value(run ArtifactRun) (T, error) {
	var zero T
	artifact, exists := run.Artifact(reference.key)
	if !exists {
		return zero, fmt.Errorf("opt: artifact %s was not produced", reference.key)
	}
	return artifactRefValue(reference, artifact)
}

// RootArtifact publishes a typed root value under a caller-supplied content
// identity. Roots do not derive their version because their owner defines the
// canonical input fingerprint.
func RootArtifact[T any](key ArtifactKey, value T) (ArtifactRef[T], ArtifactTask) {
	reference := ArtifactRef[T]{key: key}
	return reference, ArtifactTask{
		Key: key,
		Compute: func(context.Context, []Artifact) (any, error) {
			return value, nil
		},
	}
}

// DerivedArtifact1 builds a typed unary artifact task and derives its exact
// key from the producer revision and input identity.
func DerivedArtifact1[A, R any](kind ArtifactKind, name, revision string, input ArtifactRef[A], compute func(context.Context, A) (R, error)) (ArtifactRef[R], ArtifactTask) {
	key := ArtifactKey{Kind: kind, Name: name, Version: DeriveArtifactVersion(revision, input.key)}
	reference := ArtifactRef[R]{key: key}
	task := ArtifactTask{
		Key:          key,
		Dependencies: []ArtifactKey{input.key},
	}
	if compute != nil {
		task.Compute = func(ctx context.Context, dependencies []Artifact) (any, error) {
			value, err := artifactDependencyValue(input, dependencies, 0)
			if err != nil {
				return nil, err
			}
			return compute(ctx, value)
		}
	}
	return reference, task
}

// DerivedArtifact2 builds a typed binary artifact task. Dependency order is
// part of both the derived identity and the typed compute signature.
func DerivedArtifact2[A, B, R any](kind ArtifactKind, name, revision string, first ArtifactRef[A], second ArtifactRef[B], compute func(context.Context, A, B) (R, error)) (ArtifactRef[R], ArtifactTask) {
	key := ArtifactKey{Kind: kind, Name: name, Version: DeriveArtifactVersion(revision, first.key, second.key)}
	reference := ArtifactRef[R]{key: key}
	task := ArtifactTask{
		Key:          key,
		Dependencies: []ArtifactKey{first.key, second.key},
	}
	if compute != nil {
		task.Compute = func(ctx context.Context, dependencies []Artifact) (any, error) {
			firstValue, err := artifactDependencyValue(first, dependencies, 0)
			if err != nil {
				return nil, err
			}
			secondValue, err := artifactDependencyValue(second, dependencies, 1)
			if err != nil {
				return nil, err
			}
			return compute(ctx, firstValue, secondValue)
		}
	}
	return reference, task
}

// DerivedArtifact3 builds a typed ternary artifact task.
func DerivedArtifact3[A, B, C, R any](kind ArtifactKind, name, revision string, first ArtifactRef[A], second ArtifactRef[B], third ArtifactRef[C], compute func(context.Context, A, B, C) (R, error)) (ArtifactRef[R], ArtifactTask) {
	key := ArtifactKey{Kind: kind, Name: name, Version: DeriveArtifactVersion(revision, first.key, second.key, third.key)}
	reference := ArtifactRef[R]{key: key}
	task := ArtifactTask{
		Key:          key,
		Dependencies: []ArtifactKey{first.key, second.key, third.key},
	}
	if compute != nil {
		task.Compute = func(ctx context.Context, dependencies []Artifact) (any, error) {
			firstValue, err := artifactDependencyValue(first, dependencies, 0)
			if err != nil {
				return nil, err
			}
			secondValue, err := artifactDependencyValue(second, dependencies, 1)
			if err != nil {
				return nil, err
			}
			thirdValue, err := artifactDependencyValue(third, dependencies, 2)
			if err != nil {
				return nil, err
			}
			return compute(ctx, firstValue, secondValue, thirdValue)
		}
	}
	return reference, task
}

func artifactDependencyValue[T any](reference ArtifactRef[T], dependencies []Artifact, index int) (T, error) {
	var zero T
	if index < 0 || index >= len(dependencies) {
		return zero, fmt.Errorf("opt: artifact dependency %d for %s is missing", index, reference.key)
	}
	return artifactRefValue(reference, dependencies[index])
}

func artifactRefValue[T any](reference ArtifactRef[T], artifact Artifact) (T, error) {
	var zero T
	if artifact.Key != reference.key {
		return zero, fmt.Errorf("opt: artifact dependency is %s, expected %s", artifact.Key, reference.key)
	}
	value, ok := artifact.Value.(T)
	if !ok {
		return zero, fmt.Errorf("opt: artifact %s has payload %T, expected %s", artifact.Key, artifact.Value, reflect.TypeFor[T]())
	}
	return value, nil
}
