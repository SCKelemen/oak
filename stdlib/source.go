// Package stdlib embeds Oak source, not host-language implementations.
package stdlib

import (
	_ "embed"
	"regexp"
	"strings"
)

// baseSource is the opt-in bootstrap module loaded by import(std).
//
//go:embed std.oak
var baseSource string

// bytes is the first freestanding foundation package cut out of the flat
// bootstrap prelude. The compatibility flat import is derived below.
//
//go:embed bytes.oak
var bytesSource string

// bitset is the second freestanding foundation package cut out of the flat
// bootstrap prelude. Its compatibility spelling is derived below.
//
//go:embed bitset.oak
var bitsetSource string

// endian is the fixed-width integer codec over caller-owned byte storage.
// The compatibility flat import is derived below.
//
//go:embed endian.oak
var endianSource string

// buffer is the allocation-free contiguous byte queue and value-state builder.
// The compatibility flat import is derived below.
//
//go:embed buffer.oak
var bufferSource string

// array_list is the allocation-free bounded vector over caller storage.
// The compatibility flat import is derived below.
//
//go:embed array_list.oak
var arrayListSource string

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

//go:embed utf8.oak
var utf8Source string

//go:embed literals.oak
var literalsSource string

//go:embed wide.oak
var wideSource string

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

// shape: matrices whose dimensions are const parameters, so shape
// agreement is a type equation (docs/spec/56-kernels.md section 8b).
//
//go:embed shape.oak
var shapeSource string

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

// timehost is the freestanding realization of the time port
// (docs/spec/90-backend.md §2a): the two clocks are extern hooks the
// kernel or firmware defines, so no target constant and no libc.
//
//go:embed timehost.oak
var timehostSource string

// objc is a library package only (import("objc")), Darwin-only: the
// Objective-C runtime's class and selector lookups; messages are sent with
// the language form c.msg_send (docs/spec/92-ffi.md section 2.12).
//
//go:embed objc.oak
var objcSource string

// host is a library package only (import("host")): the host boundary's
// write hook from Oak (docs/spec/90-backend.md §2a) — the same program
// prints on the host and over a UART on firmware.
//
//go:embed host.oak
var hostSource string

// slab is a library package only (import("slab")): a bounded typed slab
// over caller-owned storage with generation handles
// (docs/spec/60-effects-allocation.md sections 7 and 8).
//
//go:embed slab.oak
var slabSource string

// rings is a library package only (import("rings")): SPSC and MPSC rings
// over caller-owned storage as consumers of the memory model
// (docs/spec/65-machine-memory.md section 1; dbs ask 8).
//
//go:embed rings.oak
var ringsSource string

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

// objsim is the simulated realization of the object-store port
// (docs/spec/121-object-store.md): keyed objects with generation
// preconditions, tape-driven unavailability and lost acknowledgements.
//
//go:embed objsim.oak
var objsimSource string

// NativeShim is the C source a library package's realization links: the
// native IO port (ionative) is completion rings over host bindings
// (stdlib/native/oak_io_host.c). `oak build` and `oak test` link the shim
// whenever the package is part of the program (compiler.LinkInput of kind
// "source"), so `replace io => ionative` needs no `link` line and no copy
// of the shim in the consumer's tree (docs/notes/oak-requests-2026-09-13.md
// finding 6).
type NativeShim struct {
	File   string
	Source string
}

//go:embed native/oak_io_host.c
var ioHostShimSource string

// NativeShims maps a library package to the shim its realization links.
var NativeShims = map[string]NativeShim{
	"ionative": {File: "oak_io_host.c", Source: ioHostShimSource},
}

// Prelude is the bootstrap core (std.oak): Option, Result, Overflow, and the
// helpers not yet cut into qualified packages. Every standard library package
// builds on it unqualified, and the loader splices it into any program that
// imports a library package.
var Prelude = baseSource

// Source is the legacy flat prelude of `import(std)`: the core plus every
// library package flattened — package clauses and imports dropped, qualified
// cross-references de-qualified — in dependency order. Library sources are
// written once as real packages (docs/spec/83-modules.md section 9); the
// flat spelling is derived here so the two views cannot drift.
var Source = baseSource + "\n" + flattenBytes(bytesSource) + "\n" + flattenBitset(bitsetSource) + "\n" + flattenEndian(endianSource) + "\n" + flattenBuffer(bufferSource) + "\n" + flattenArrayList(arrayListSource) + "\n" + flattenLegacy(causalFrontierSource) + "\n" + flattenLegacy(unicodeSource) + "\n" +
	flattenLegacy(stringsSource) + "\n" + flattenLegacy(jsonSource) + "\n" + flattenLegacy(filtersSource) + "\n" +
	flattenLegacy(hashTableSource) + "\n" + flattenLegacy(bitsetAlgebraSource) + "\n" + flattenLegacy(encodingSource) + "\n" +
	flattenLegacy(sortSource) + "\n" + flattenLegacy(varintSource) + "\n" + flattenLegacy(randomSource) + "\n" + flattenLegacy(urlSource) + "\n" + flattenLegacy(uuidSource) + "\n" + flattenLegacy(pathSource) + "\n" + flattenLegacy(graphemeSource) + "\n" + flattenLegacy(floatSource) + "\n" + flattenLegacy(normalizeSource)

var (
	clauseLine = regexp.MustCompile(`(?m)^package [a-z_]+\n`)
	importLine = regexp.MustCompile(`(?m)^import\("[a-z_]+"\)\n`)
	// A package qualifier is only a qualifier when nothing precedes it: after
	// a `.` it is a field named like a package (the `Url` record's `path`), so
	// the leading context is kept and only the qualifier is dropped.
	qualification     = regexp.MustCompile(`(^|[^.\w])(bytes|bitset|endian|buffer|array_list|unicode|strings|json|filters|hash_table|bitset_algebra|causal_frontier|encoding|sort|varint|random|url|uuid|path|grapheme|float|normalize)\.`)
	bytesFlatName     = regexp.MustCompile(`\b(RangeError|range_fits|copy_into|equal|find|fill|copy_at|move_within|compare)\b`)
	bitsetFlatName    = regexp.MustCompile(`\b(Error|storage_bytes|contains|set|count_ones)\b`)
	endianFlatName    = regexp.MustCompile(`\b(Error|read_u16_le|write_u16_le|read_u16_be|write_u16_be|read_u32_le|write_u32_le|read_u32_be|write_u32_be|read_u64_le|write_u64_le|read_u64_be|write_u64_be)\b`)
	bufferFlatType    = regexp.MustCompile(`\b(Cursor|Error|Builder)\b`)
	bufferFlatFunc    = regexp.MustCompile(`\b(check|live_len|tail_space|append|peek_into|consume|read_into|compact|reset|finish)\b`)
	arrayListFlatType = regexp.MustCompile(`\b(Cursor|Error)\b`)
	arrayListFlatFunc = regexp.MustCompile(`\b(check|push|get|set|pop|insert|remove|swap_remove|clear)\b`)
)

// flatten derives the prelude spelling of a library package: no clause, no
// imports, unqualified references. Library identifiers are unique across
// files (they were one namespace), so de-qualification is unambiguous.
func flatten(text string) string {
	text = clauseLine.ReplaceAllString(text, "")
	text = importLine.ReplaceAllString(text, "")
	return qualification.ReplaceAllString(text, "$1")
}

// flattenLegacy preserves collision-resistant foundation names when deriving
// import(std). Generic flattening keeps the short names for extraction and
// other internal package composition.
func flattenLegacy(text string) string {
	// Qualified foundation packages deliberately use short Go-shaped names.
	// Preserve the older collision-resistant spellings only in import(std).
	text = strings.NewReplacer(
		"bytes.RangeError", "ByteRangeError",
		"bytes.range_fits", "bytes_range_fits",
		"bytes.copy_into", "bytes_copy_into",
		"bytes.equal", "bytes_equal",
		"bytes.find", "bytes_find",
		"bytes.fill", "bytes_fill",
		"bytes.copy_at", "bytes_copy_at",
		"bytes.move_within", "bytes_move_within",
		"bytes.compare", "bytes_compare",
		"bitset.Error", "BitSetError",
		"bitset.storage_bytes", "bitset_storage_bytes",
		"bitset.contains", "bitset_contains",
		"bitset.set", "bitset_set",
		"bitset.count_ones", "bitset_count",
		"endian.Error", "EndianError",
		"endian.read_u16_le", "bytes_read_u16_le",
		"endian.write_u16_le", "bytes_write_u16_le",
		"endian.read_u16_be", "bytes_read_u16_be",
		"endian.write_u16_be", "bytes_write_u16_be",
		"endian.read_u32_le", "bytes_read_u32_le",
		"endian.write_u32_le", "bytes_write_u32_le",
		"endian.read_u32_be", "bytes_read_u32_be",
		"endian.write_u32_be", "bytes_write_u32_be",
		"endian.read_u64_le", "bytes_read_u64_le",
		"endian.write_u64_le", "bytes_write_u64_le",
		"endian.read_u64_be", "bytes_read_u64_be",
		"endian.write_u64_be", "bytes_write_u64_be",
		"buffer.Cursor", "ByteBufferCursor",
		"buffer.Error", "BufferError",
		"buffer.live_len", "buffer_len",
		"buffer.tail_space", "buffer_tail_space",
		"buffer.append", "buffer_append",
		"buffer.peek_into", "buffer_peek_into",
		"buffer.consume", "buffer_consume",
		"buffer.read_into", "buffer_read_into",
		"buffer.compact", "buffer_compact",
		"buffer.reset", "buffer_reset",
		"buffer.Builder", "ByteBuilder",
		"buffer.builder", "byte_builder",
		"buffer.finish", "finish_bytes",
	).Replace(text)
	return flatten(text)
}

// flattenBytes derives the collision-resistant legacy declarations without
// adding the package's short Go-shaped names to import(std).
func flattenBytes(text string) string {
	text = flatten(text)
	return bytesFlatName.ReplaceAllStringFunc(text, func(name string) string {
		if name == "RangeError" {
			return "ByteRangeError"
		}
		return "bytes_" + name
	})
}

// flattenBitset derives the legacy type and function declarations without
// reserving Error, storage_bytes, contains, set, or count_ones in import(std).
func flattenBitset(text string) string {
	text = flatten(text)
	return bitsetFlatName.ReplaceAllStringFunc(text, func(name string) string {
		if name == "Error" {
			return "BitSetError"
		}
		if name == "count_ones" {
			return "bitset_count"
		}
		return "bitset_" + name
	})
}

// flattenEndian derives the older bytes_read/write spellings while the real
// package exposes the shorter read/write names behind its qualifier.
func flattenEndian(text string) string {
	text = flattenLegacy(text)
	return endianFlatName.ReplaceAllStringFunc(text, func(name string) string {
		if name == "Error" {
			return "EndianError"
		}
		return "bytes_" + name
	})
}

// flattenBuffer keeps the established byte-buffer and builder names in the
// compatibility prelude without reserving the package's short API names.
func flattenBuffer(text string) string {
	text = flatten(text)
	text = bufferFlatType.ReplaceAllStringFunc(text, func(name string) string {
		switch name {
		case "Cursor":
			return "ByteBufferCursor"
		case "Error":
			return "BufferError"
		default:
			return "ByteBuilder"
		}
	})
	text = bufferFlatFunc.ReplaceAllStringFunc(text, func(name string) string {
		switch name {
		case "live_len":
			return "buffer_len"
		case "finish":
			return "finish_bytes"
		default:
			return "buffer_" + name
		}
	})
	return strings.Replace(text, "pub builder:", "pub byte_builder:", 1)
}

// flattenArrayList preserves the original flat collection API. The qualified
// package has the narrow errors its operations can return; import(std) already
// declares the broader CollectionError shared with intrusive collections.
func flattenArrayList(text string) string {
	text = strings.Replace(text, "pub Error: type = Full | Empty | OutOfBounds\n\n", "", 1)
	text = flatten(text)
	text = arrayListFlatType.ReplaceAllStringFunc(text, func(name string) string {
		if name == "Cursor" {
			return "ArrayListCursor"
		}
		return "CollectionError"
	})
	return arrayListFlatFunc.ReplaceAllString(text, "array_list_$1")
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
	"bytes":           bytesSource,
	"bitset":          bitsetSource,
	"endian":          endianSource,
	"buffer":          bufferSource,
	"array_list":      arrayListSource,
	"iosim":           iosimSource,
	"ionative":        ionativeSource,
	"objsim":          objsimSource,
	"strings":         stringsSource,
	"unicode":         unicodeSource,
	"json":            jsonSource,
	"utf8":            utf8Source,
	"literals":        literalsSource,
	"wide":            wideSource,
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
	"shape":           shapeSource,
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
	"timehost":        timehostSource,
	"arena":           arenaSource,
	"host":            hostSource,
	"slab":            slabSource,
	"rings":           ringsSource,
	"objc":            objcSource,
}

// CompatibilityName relates a generated or legacy flat spelling to the real
// exported member of one qualified package. The module loader installs an
// alias only when that package is actually loaded; this table never widens a
// package's exports or emits a second implementation.
type CompatibilityName struct {
	Name   string
	Member string
}

// CompatibilityNames are the flat spellings compiler-generated library sugar
// may still use while the bootstrap prelude is being split into packages.
var CompatibilityNames = map[string][]CompatibilityName{
	"bytes": {{Name: "bytes_range_fits", Member: "range_fits"}},
}

// Flatten derives the prelude spelling of one library package's text: no
// package clause, no imports, qualified cross-references de-qualified. The
// Lean extraction of the standard library builds a package's program from
// the core prelude plus the flattened texts of the package and its
// dependencies (compiler/lean_stdlib_extract_test.go).
func Flatten(text string) string { return flatten(text) }
