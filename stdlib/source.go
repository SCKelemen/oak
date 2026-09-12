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

// uuid: RFC 9562 version 4 and 7 values over the random and encoding
// packages (stdlib/README.md); a library package and part of the flat prelude.
//
// AsmUnit is an AArch64 `.oakasm` translation unit beside a library
// package (docs/spec/94-assembler.md section 7): the loader attaches it when
// the package is imported, with its function names rewritten to the
// package's internal names, so the units pair with the package's
// declarations exactly as a root package's units do.
type AsmUnit struct {
	Path string
	Text string
}

// The hash package's AArch64 kernels: CRC-32C through crc32cx and SHA-256
// through the SHA-2 extension. Each pairs with an Oak declaration that keeps
// its portable body, so the extraction, the interpreter, and non-AArch64
// builds see the same definition the unit is checked against.
//
//go:embed hash.arm64.oakasm
var hashAsmSource string

// AsmUnits lists the asm units of each library package by package path.
var AsmUnits = map[string][]AsmUnit{
	"hash": {{Path: "<stdlib>/hash.arm64.oakasm", Text: hashAsmSource}},
}

//go:embed uuid.oak
var uuidSource string

// path: slash-separated paths and glob patterns with Go's path semantics
// (stdlib/README.md); a library package and part of the flat prelude.
//
//go:embed path.oak
var pathSource string

// reduce: reductions whose grouping is a language fact — the balanced
// binary-counter tree and the sequential left fold (docs/spec/55-parallelism.md
// section 4); a library package and part of the flat prelude.
//
//go:embed reduce.oak
var reduceSource string

//go:embed tensor.oak
var tensorSource string

// grapheme: UAX #29 extended grapheme cluster segmentation over UTF-8 views
// (stdlib/README.md); a library package and part of the flat prelude.
//
//go:embed grapheme.oak
var graphemeSource string

// normalize: UAX #15 normalization forms over UTF-8 views
// (stdlib/README.md); a library package and part of the flat prelude.
//
//go:embed normalize.oak
var normalizeSource string

// float: shortest and correctly rounded decimal text for f64 and f32
// (stdlib/README.md); a library package and part of the flat prelude.
//
//go:embed float.oak
var floatSource string

// encoding: hex, base64, base32 and percent codecs over borrowed bytes
// (stdlib/README.md); a library package and part of the flat prelude.
//
//go:embed encoding.oak
var encodingSource string

// url is spliced into the flat prelude like the collections: RFC 3986
// reference parsing and resolution over caller storage (stdlib/README.md).
//
//go:embed url.oak
var urlSource string

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

// time is a library package only (import("time")): instants, durations,
// the proleptic Gregorian calendar and RFC 3339 text in Oak, with no clock
// (stdlib/README.md); its names (instant_add, weekday, ...) stay qualified.
//
//go:embed time.oak
var timeSource string

// timesim is a library package only (import("timesim")): drives a simulated
// TimeSource from the event queue, injects tape-drawn clock faults, and
// generates the instants, durations and text that break time code
// (110-testing.md, "Simulated time").
//
//go:embed timesim.oak
var timesimSource string

// timenative is a library package only (import("timenative")): the native
// TimeSource realization in pure Oak — clock_gettime as an extern, the
// clock ids as target constants (docs/spec/92-ffi.md section 2.11).
//
//go:embed timenative.oak
var timenativeSource string

// objc is a library package only (import("objc")), Darwin-only: the
// Objective-C runtime's class and selector lookups; messages are sent with
// the language form c.msg_send (docs/spec/92-ffi.md section 2.12).
//
//go:embed objc.oak
var objcSource string

// arena is a library package only (import("arena")): bump reservations of
// element ranges over an owner such as a Buffer[T]
// (docs/spec/60-effects-allocation.md section 6).
//
//go:embed arena.oak
var arenaSource string

// iosim and ionative are the two realizations of the IO port
// (docs/spec/120-io.md): completion rings over SimDisk for simulation,
// and over host bindings (stdlib/native/oak_io_host.c) for the operating
// system. A program imports the port as `io` and selects a realization
// with `replace io => iosim` or `replace io => ionative`.
//
//go:embed iosim.oak
var iosimSource string

//go:embed ionative.oak
var ionativeSource string

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
	flatten(hashTableSource) + "\n" + flatten(bitsetAlgebraSource) + "\n" + flatten(encodingSource) + "\n" +
	flatten(sortSource) + "\n" + flatten(varintSource) + "\n" + flatten(randomSource) + "\n" + flatten(urlSource) + "\n" + flatten(uuidSource) + "\n" + flatten(pathSource) + "\n" + flatten(graphemeSource) + "\n" + flatten(floatSource) + "\n" + flatten(normalizeSource)

var (
	clauseLine = regexp.MustCompile(`(?m)^package [a-z_]+\n`)
	importLine = regexp.MustCompile(`(?m)^import\("[a-z_]+"\)\n`)
	// A package qualifier is only a qualifier when nothing precedes it: after
	// a `.` it is a field named like a package (the `Url` record's `path`), so
	// the leading context is kept and only the qualifier is dropped.
	qualification = regexp.MustCompile(`(^|[^.\w])(unicode|strings|json|filters|hash_table|bitset_algebra|causal_frontier|encoding|sort|varint|random|url|uuid|path|grapheme|float|normalize)\.`)
)

// flatten derives the prelude spelling of a library package: no clause, no
// imports, unqualified references. Library identifiers are unique across
// files (they were one namespace), so de-qualification is unambiguous.
func flatten(text string) string {
	text = clauseLine.ReplaceAllString(text, "")
	text = importLine.ReplaceAllString(text, "")
	return qualification.ReplaceAllString(text, "$1")
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
	"iosim":           iosimSource,
	"ionative":        ionativeSource,
	"strings":         stringsSource,
	"unicode":         unicodeSource,
	"json":            jsonSource,
	"filters":         filtersSource,
	"hash_table":      hashTableSource,
	"bitset_algebra":  bitsetAlgebraSource,
	"sort":            sortSource,
	"varint":          varintSource,
	"random":          randomSource,
	"uuid":            uuidSource,
	"path":            pathSource,
	"reduce":          reduceSource,
	"tensor":          tensorSource,
	"grapheme":        graphemeSource,
	"normalize":       normalizeSource,
	"float":           floatSource,
	"causal_frontier": causalFrontierSource,
	"encoding":        encodingSource,
	"url":             urlSource,
	"math":            mathSource,
	"hash":            hashSource,
	"mx":              mxSource,
	"time":            timeSource,
	"timesim":         timesimSource,
	"timenative":      timenativeSource,
	"arena":           arenaSource,
	"objc":            objcSource,
}

// Flatten derives the prelude spelling of one library package's text: no
// package clause, no imports, qualified cross-references de-qualified. The
// Lean extraction of the standard library builds a package's program from
// the core prelude plus the flattened texts of the package and its
// dependencies (compiler/lean_stdlib_extract_test.go).
func Flatten(text string) string { return flatten(text) }
