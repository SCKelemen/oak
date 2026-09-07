// Package stdlib embeds Oak source, not host-language implementations.
package stdlib

import _ "embed"

// Source is the opt-in bootstrap module loaded by import(std).
//
//go:embed std.oak
var Source string
