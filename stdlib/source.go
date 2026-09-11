// Package stdlib embeds Oak source, not host-language implementations.
package stdlib

import (
	_ "embed"
	"regexp"
)

// baseSource is the opt-in bootstrap module loaded by import(std).
//
//go:embed std.oak
var baseSource string

// The host compiler composes bounded frontier helpers into import(std).
// Generated target code keeps no runtime module descriptor.
//
//go:embed causal_frontier.oak
var causalFrontierSource string

//go:embed strings.oak
var stringsSource string

//go:embed unicode.oak
var unicodeSource string

//go:embed json.oak
var jsonSource string

//go:embed filters.oak
var filtersSource string

//go:embed hash_table.oak
var hashTableSource string

//go:embed bitset_algebra.oak
var bitsetAlgebraSource string

// sort, varint and random are spliced into the flat prelude like the
// collections: sorting and searching over spans, LEB128/ZigZag integers,
// and a deterministic xoshiro256** stream.
//
//go:embed sort.oak
var sortSource string

//go:embed varint.oak
var varintSource string

//go:embed random.oak
var randomSource string

// math is a library package only (import("math")), never spliced into the
// flat prelude: its names (exp, log, ...) are too common to land
// unqualified in every program (docs/spec/20-types.md section 11.3.6).
//
//go:embed math.oak
var mathSource string

// hash is a library package only (import("hash")): SHA-256 and CRC-32C in
// Oak (stdlib/README.md), bit-identical across the interpreter and backends.
//
//go:embed hash.oak
var hashSource string

// mx is a library package only (import("mx")): the OCP Microscaling MXFP4
// block format — E2M1 elements under an E8M0 block scale — in Oak
// (docs/spec/20-types.md section 11.3.1a).
//
//go:embed mx.oak
var mxSource string

// Prelude is the core library (std.oak): Option, Result, Overflow, byte and
// ring helpers. Every standard library package builds on it unqualified, and
// the loader splices it into any program that imports a library package.
var Prelude = baseSource

// Source is the legacy flat prelude of `import(std)`: the core plus every
// library package flattened — package clauses and imports dropped, qualified
// cross-references de-qualified — in dependency order. Library sources are
// written once as real packages (docs/spec/83-modules.md section 9); the
// flat spelling is derived here so the two views cannot drift.
var Source = baseSource + "\n" + flatten(causalFrontierSource) + "\n" + flatten(unicodeSource) + "\n" +
	flatten(stringsSource) + "\n" + flatten(jsonSource) + "\n" + flatten(filtersSource) + "\n" +
	flatten(hashTableSource) + "\n" + flatten(bitsetAlgebraSource) + "\n" +
	flatten(sortSource) + "\n" + flatten(varintSource) + "\n" + flatten(randomSource)

var (
	clauseLine    = regexp.MustCompile(`(?m)^package [a-z_]+\n`)
	importLine    = regexp.MustCompile(`(?m)^import\("[a-z_]+"\)\n`)
	qualification = regexp.MustCompile(`\b(unicode|strings|json|filters|hash_table|bitset_algebra|causal_frontier|sort|varint|random)\.`)
)

// flatten derives the prelude spelling of a library package: no clause, no
// imports, unqualified references. Library identifiers are unique across
// files (they were one namespace), so de-qualification is unambiguous.
func flatten(text string) string {
	text = clauseLine.ReplaceAllString(text, "")
	text = importLine.ReplaceAllString(text, "")
	return qualification.ReplaceAllString(text, "")
}

//go:embed testing.oak
var testingSource string

// Simulated block storage with tape-driven faults (110-testing.md,
// "Simulated storage"): pure Oak over caller-owned storage, part of the
// testing module so simulation packages get it without a native adapter.
//
//go:embed sim_storage.oak
var simStorageSource string

// Process crash/restart as scheduled events and fair scheduling adapters
// (110-testing.md, "Crashes and scheduling").
//
//go:embed sim_sched.oak
var simSchedSource string

// TestingSource is the opt-in import(testing) module. Its reporting boundary
// is supplied by oak test; generated target helpers use caller-owned storage.
var TestingSource = testingSource + "\n" + simStorageSource + "\n" + simSchedSource

// Packages are the standard library files importable as qualified package
// views (docs/spec/83-modules.md section 9): `import("strings")` exposes the
// declarations of strings.oak as `strings.member`. The views share the flat
// bootstrap prelude, which the loader splices in alongside them.
var Packages = map[string]string{
	"strings":         stringsSource,
	"unicode":         unicodeSource,
	"json":            jsonSource,
	"filters":         filtersSource,
	"hash_table":      hashTableSource,
	"bitset_algebra":  bitsetAlgebraSource,
	"sort":            sortSource,
	"varint":          varintSource,
	"random":          randomSource,
	"causal_frontier": causalFrontierSource,
	"math":            mathSource,
	"hash":            hashSource,
	"mx":              mxSource,
}
