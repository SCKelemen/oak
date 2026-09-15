package opt

import (
	"container/heap"
	"context"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"fmt"
	"hash"
	"sort"
	"strings"
	"sync"
)

// ArtifactKind names the role of one immutable compiler artifact. The kind is
// descriptive; admissibility still comes from explicit proof and verdict
// artifacts rather than from this label.
type ArtifactKind string

const (
	ArtifactSource    ArtifactKind = "source"
	ArtifactChecked   ArtifactKind = "checked"
	ArtifactIR        ArtifactKind = "ir"
	ArtifactAnalysis  ArtifactKind = "analysis"
	ArtifactCandidate ArtifactKind = "candidate"
	ArtifactAdmission ArtifactKind = "admission"
	ArtifactMetrics   ArtifactKind = "metrics"
	ArtifactCost      ArtifactKind = "cost"
	ArtifactVerdict   ArtifactKind = "verdict"
	ArtifactSelection ArtifactKind = "selection"
)

// ArtifactKey identifies one exact artifact recipe. Version must include the
// producer revision and exact input identities when the artifact is cacheable.
type ArtifactKey struct {
	Kind    ArtifactKind
	Name    string
	Version string
}

func (key ArtifactKey) String() string {
	return fmt.Sprintf("%s:%s@%s", key.Kind, key.Name, key.Version)
}

func (key ArtifactKey) validate() error {
	if !validArtifactKind(key.Kind) {
		return fmt.Errorf("opt: artifact %q has invalid kind %q", key.Name, key.Kind)
	}
	if key.Name == "" {
		return fmt.Errorf("opt: artifact %s has an empty name", key.Kind)
	}
	if key.Version == "" {
		return fmt.Errorf("opt: artifact %s:%s has an empty version", key.Kind, key.Name)
	}
	return nil
}

func validArtifactKind(kind ArtifactKind) bool {
	switch kind {
	case ArtifactSource, ArtifactChecked, ArtifactIR, ArtifactAnalysis,
		ArtifactCandidate, ArtifactAdmission, ArtifactMetrics, ArtifactCost,
		ArtifactVerdict, ArtifactSelection:
		return true
	default:
		return false
	}
}

// DeriveArtifactVersion returns an unambiguous recipe digest over a producer
// revision and the ordered identities of all dependencies.
func DeriveArtifactVersion(revision string, dependencies ...ArtifactKey) string {
	digest := sha256.New()
	writeArtifactDigestPart(digest, "oak.optimizer.artifact.v1")
	writeArtifactDigestPart(digest, revision)
	for _, dependency := range dependencies {
		writeArtifactDigestPart(digest, string(dependency.Kind))
		writeArtifactDigestPart(digest, dependency.Name)
		writeArtifactDigestPart(digest, dependency.Version)
	}
	return hex.EncodeToString(digest.Sum(nil))
}

func writeArtifactDigestPart(digest hash.Hash, value string) {
	var length [8]byte
	binary.BigEndian.PutUint64(length[:], uint64(len(value)))
	_, _ = digest.Write(length[:])
	_, _ = digest.Write([]byte(value))
}

// Artifact is one immutable payload published under Key. Payloads are opaque
// to the scheduler and must not be mutated after publication.
type Artifact struct {
	Key   ArtifactKey
	Value any
}

// ArtifactCompute builds one artifact from dependencies supplied in the exact
// order declared by ArtifactTask.Dependencies.
type ArtifactCompute func(context.Context, []Artifact) (any, error)

// ArtifactTask is one node in an ArtifactGraph.
type ArtifactTask struct {
	Key          ArtifactKey
	Dependencies []ArtifactKey
	Compute      ArtifactCompute
}

// ArtifactGraph is an acyclic dependency graph of immutable artifacts.
type ArtifactGraph struct {
	tasks map[ArtifactKey]ArtifactTask
}

// NewArtifactGraph constructs and validates a graph. Tasks may be supplied in
// any order.
func NewArtifactGraph(tasks ...ArtifactTask) (*ArtifactGraph, error) {
	graph := &ArtifactGraph{}
	for _, task := range tasks {
		if err := graph.Add(task); err != nil {
			return nil, err
		}
	}
	if err := graph.Validate(); err != nil {
		return nil, err
	}
	return graph, nil
}

// Add records a task and defensively copies its dependency list. Missing
// dependencies and cycles are checked by Validate after graph construction.
func (graph *ArtifactGraph) Add(task ArtifactTask) error {
	if graph == nil {
		return errors.New("opt: add artifact task to nil graph")
	}
	if err := task.Key.validate(); err != nil {
		return err
	}
	if task.Compute == nil {
		return fmt.Errorf("opt: artifact %s has no computation", task.Key)
	}
	if graph.tasks == nil {
		graph.tasks = map[ArtifactKey]ArtifactTask{}
	}
	if _, exists := graph.tasks[task.Key]; exists {
		return fmt.Errorf("opt: duplicate artifact task %s", task.Key)
	}
	seen := make(map[ArtifactKey]bool, len(task.Dependencies))
	dependencies := make([]ArtifactKey, len(task.Dependencies))
	for index, dependency := range task.Dependencies {
		if err := dependency.validate(); err != nil {
			return fmt.Errorf("opt: artifact %s dependency %d: %w", task.Key, index, err)
		}
		if seen[dependency] {
			return fmt.Errorf("opt: artifact %s repeats dependency %s", task.Key, dependency)
		}
		seen[dependency] = true
		dependencies[index] = dependency
	}
	task.Dependencies = dependencies
	graph.tasks[task.Key] = task
	return nil
}

// Validate rejects missing dependencies and cycles.
func (graph *ArtifactGraph) Validate() error {
	_, err := graph.topologicalOrder()
	return err
}

// TopologicalOrder returns every graph key in deterministic dependency order.
func (graph *ArtifactGraph) TopologicalOrder() ([]ArtifactKey, error) {
	return graph.topologicalOrder()
}

func (graph *ArtifactGraph) topologicalOrder() ([]ArtifactKey, error) {
	if graph == nil {
		return nil, errors.New("opt: validate nil artifact graph")
	}
	indegree := make(map[ArtifactKey]int, len(graph.tasks))
	dependents := make(map[ArtifactKey][]ArtifactKey, len(graph.tasks))
	for key, task := range graph.tasks {
		indegree[key] = len(task.Dependencies)
		for _, dependency := range task.Dependencies {
			if _, exists := graph.tasks[dependency]; !exists {
				return nil, fmt.Errorf("opt: artifact %s depends on missing artifact %s", key, dependency)
			}
			dependents[dependency] = append(dependents[dependency], key)
		}
	}
	for key := range dependents {
		sortArtifactKeys(dependents[key])
	}
	ready := &artifactKeyHeap{}
	heap.Init(ready)
	for key, degree := range indegree {
		if degree == 0 {
			heap.Push(ready, key)
		}
	}
	order := make([]ArtifactKey, 0, len(graph.tasks))
	for ready.Len() > 0 {
		key := heap.Pop(ready).(ArtifactKey)
		order = append(order, key)
		for _, dependent := range dependents[key] {
			indegree[dependent]--
			if indegree[dependent] == 0 {
				heap.Push(ready, dependent)
			}
		}
	}
	if len(order) != len(graph.tasks) {
		cyclic := make([]ArtifactKey, 0, len(graph.tasks)-len(order))
		for key, degree := range indegree {
			if degree > 0 {
				cyclic = append(cyclic, key)
			}
		}
		sortArtifactKeys(cyclic)
		return nil, fmt.Errorf("opt: artifact graph contains a cycle involving %s", joinArtifactKeys(cyclic))
	}
	return order, nil
}

func sortArtifactKeys(keys []ArtifactKey) {
	sort.Slice(keys, func(i, j int) bool {
		return lessArtifactKey(keys[i], keys[j])
	})
}

func lessArtifactKey(left, right ArtifactKey) bool {
	if left.Kind != right.Kind {
		return left.Kind < right.Kind
	}
	if left.Name != right.Name {
		return left.Name < right.Name
	}
	return left.Version < right.Version
}

type artifactKeyHeap []ArtifactKey

func (keys artifactKeyHeap) Len() int           { return len(keys) }
func (keys artifactKeyHeap) Less(i, j int) bool { return lessArtifactKey(keys[i], keys[j]) }
func (keys artifactKeyHeap) Swap(i, j int)      { keys[i], keys[j] = keys[j], keys[i] }
func (keys *artifactKeyHeap) Push(value any)    { *keys = append(*keys, value.(ArtifactKey)) }
func (keys *artifactKeyHeap) Pop() any {
	old := *keys
	last := len(old) - 1
	value := old[last]
	old[last] = ArtifactKey{}
	*keys = old[:last]
	return value
}

func joinArtifactKeys(keys []ArtifactKey) string {
	if len(keys) == 0 {
		return "<none>"
	}
	var result strings.Builder
	for index, key := range keys {
		if index != 0 {
			result.WriteString(", ")
		}
		result.WriteString(key.String())
	}
	return result.String()
}

// ArtifactCache stores immutable payloads by their exact artifact key.
type ArtifactCache interface {
	Get(ArtifactKey) (any, bool)
	Put(ArtifactKey, any)
}

// MemoryArtifactCache is a process-local, concurrency-safe artifact cache.
type MemoryArtifactCache struct {
	mu     sync.RWMutex
	values map[ArtifactKey]any
}

func NewMemoryArtifactCache() *MemoryArtifactCache {
	return &MemoryArtifactCache{values: map[ArtifactKey]any{}}
}

func (cache *MemoryArtifactCache) Get(key ArtifactKey) (any, bool) {
	if cache == nil {
		return nil, false
	}
	cache.mu.RLock()
	defer cache.mu.RUnlock()
	value, exists := cache.values[key]
	return value, exists
}

func (cache *MemoryArtifactCache) Put(key ArtifactKey, value any) {
	if cache == nil {
		return
	}
	cache.mu.Lock()
	defer cache.mu.Unlock()
	if cache.values == nil {
		cache.values = map[ArtifactKey]any{}
	}
	cache.values[key] = value
}

func (cache *MemoryArtifactCache) Len() int {
	if cache == nil {
		return 0
	}
	cache.mu.RLock()
	defer cache.mu.RUnlock()
	return len(cache.values)
}

// ArtifactRun is deterministic execution evidence. Executed and CacheHits are
// in graph order; Targets are sorted by key independently of request order.
type ArtifactRun struct {
	Targets   []Artifact
	Executed  []ArtifactKey
	CacheHits []ArtifactKey
	artifacts map[ArtifactKey]Artifact
}

// Artifact returns a computed or cached artifact, including intermediates.
func (run ArtifactRun) Artifact(key ArtifactKey) (Artifact, bool) {
	artifact, exists := run.artifacts[key]
	return artifact, exists
}

// ArtifactTaskError attributes a computation or cancellation failure to the
// exact artifact that could not be produced.
type ArtifactTaskError struct {
	Key ArtifactKey
	Err error
}

func (failure *ArtifactTaskError) Error() string {
	return fmt.Sprintf("opt: artifact %s failed: %v", failure.Key, failure.Err)
}

func (failure *ArtifactTaskError) Unwrap() error { return failure.Err }

// Run computes the transitive closure of targets in deterministic topological
// order. A shared dependency executes at most once.
func (graph *ArtifactGraph) Run(ctx context.Context, cache ArtifactCache, targets ...ArtifactKey) (ArtifactRun, error) {
	order, err := graph.topologicalOrder()
	if err != nil {
		return ArtifactRun{}, err
	}
	if ctx == nil {
		return ArtifactRun{}, errors.New("opt: artifact graph run has nil context")
	}
	needed := map[ArtifactKey]bool{}
	preloaded := map[ArtifactKey]any{}
	work := append([]ArtifactKey(nil), targets...)
	for len(work) > 0 {
		last := len(work) - 1
		key := work[last]
		work = work[:last]
		if needed[key] {
			continue
		}
		task, exists := graph.tasks[key]
		if !exists {
			return ArtifactRun{}, fmt.Errorf("opt: requested missing artifact %s", key)
		}
		needed[key] = true
		if value, exists := cacheGet(cache, key); exists {
			preloaded[key] = value
			continue
		}
		work = append(work, task.Dependencies...)
	}

	run := ArtifactRun{artifacts: map[ArtifactKey]Artifact{}}
	for _, key := range order {
		if !needed[key] {
			continue
		}
		if err := ctx.Err(); err != nil {
			return run, &ArtifactTaskError{Key: key, Err: err}
		}
		if value, exists := preloaded[key]; exists {
			run.artifacts[key] = Artifact{Key: key, Value: value}
			run.CacheHits = append(run.CacheHits, key)
			continue
		}
		task := graph.tasks[key]
		dependencies := make([]Artifact, len(task.Dependencies))
		for index, dependency := range task.Dependencies {
			artifact, exists := run.artifacts[dependency]
			if !exists {
				return run, &ArtifactTaskError{Key: key, Err: fmt.Errorf("dependency %s produced no artifact", dependency)}
			}
			dependencies[index] = artifact
		}
		value, err := task.Compute(ctx, dependencies)
		if err != nil {
			return run, &ArtifactTaskError{Key: key, Err: err}
		}
		if err := ctx.Err(); err != nil {
			return run, &ArtifactTaskError{Key: key, Err: err}
		}
		artifact := Artifact{Key: key, Value: value}
		run.artifacts[key] = artifact
		run.Executed = append(run.Executed, key)
		if cache != nil {
			cache.Put(key, value)
		}
	}

	uniqueTargets := map[ArtifactKey]bool{}
	for _, key := range targets {
		uniqueTargets[key] = true
	}
	orderedTargets := make([]ArtifactKey, 0, len(uniqueTargets))
	for key := range uniqueTargets {
		orderedTargets = append(orderedTargets, key)
	}
	sortArtifactKeys(orderedTargets)
	for _, key := range orderedTargets {
		run.Targets = append(run.Targets, run.artifacts[key])
	}
	return run, nil
}

func cacheGet(cache ArtifactCache, key ArtifactKey) (any, bool) {
	if cache == nil {
		return nil, false
	}
	return cache.Get(key)
}
