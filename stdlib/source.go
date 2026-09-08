// Package stdlib embeds Oak source, not host-language implementations.
package stdlib

import _ "embed"

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

var Source = baseSource + "\n" + causalFrontierSource + "\n" + unicodeSource + "\n" + stringsSource + "\n" + jsonSource + "\n" + filtersSource + "\n" + hashTableSource + "\n" + bitsetAlgebraSource


// TestingSource is the opt-in import(testing) module. Its reporting boundary
// is supplied by oak test; generated target helpers use caller-owned storage.
//go:embed testing.oak
var TestingSource string
