package codegen

// C identifier mangling for Oak names (docs/spec/90-backend.md): an Oak
// identifier is emitted verbatim into generated C unless its spelling is a
// C keyword, a leading-underscore name (reserved to the C implementation),
// or a name in the emitter's own `oak_` namespace — those become
// `oak_id_<name>`, so an Oak local called `short`, `signed`, `default`, or
// `oak_assert` can never produce invalid or aliasing C. Function names are
// not routed here: they already carry the `oak_` (or package) prefix.

import "strings"

var cReservedWords = map[string]bool{
	"auto": true, "break": true, "case": true, "char": true, "const": true,
	"continue": true, "default": true, "do": true, "double": true, "else": true,
	"enum": true, "extern": true, "float": true, "for": true, "goto": true,
	"if": true, "inline": true, "long": true, "register": true,
	"restrict": true, "return": true, "short": true, "signed": true,
	"sizeof": true, "static": true, "struct": true, "switch": true,
	"typedef": true, "union": true, "unsigned": true, "void": true,
	"volatile": true, "while": true, "bool": true, "true": true, "false": true,
	// C runtime spellings the emitted preamble relies on.
	"main": false, "int": false, // Oak's own `int` type spelling lowers by the type table, never mangled
}

// cIdent maps an Oak value/field identifier to its C spelling.
func cIdent(name string) string {
	if strings.HasPrefix(name, "oak_id_") {
		return name // already mangled (idempotent through nested emitters)
	}
	if cReservedWords[name] || strings.HasPrefix(name, "_") || strings.HasPrefix(name, "oak_") {
		return "oak_id_" + name
	}
	return name
}
