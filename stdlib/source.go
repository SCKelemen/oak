// Package stdlib embeds Oak source, not host-language implementations.
package stdlib

import _ "embed"

// baseSource is the opt-in bootstrap module loaded by import(std).
//
//go:embed std.oak
var baseSource string

// The host compiler composes bounded frontier helpers into import(std).
// Generated target code keeps no runtime module descriptor.
//go:embed causal_frontier.oak
var causalFrontierSource string

var Source = baseSource + "\n" + causalFrontierSource
