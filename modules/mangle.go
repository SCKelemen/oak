// Package modules implements the pure decision procedures of the Oak module
// system (docs/spec/83-modules.md): injective package-qualified naming,
// dependency ordering, import-path validation, manifest parsing, minimal
// version selection, and the visibility/sealing lookup rule. Nothing here
// touches the filesystem or the syntax tree; the compiler's loader
// (compiler/modules.go) drives these procedures. The functions are kept as
// line-for-line transliterations of `Oak.Modules` (Lean), which proves their
// laws.
package modules

import (
	"fmt"
	"strings"
)

// Separator joins the escaped package path and the escaped declaration name
// in an internal (mangled) name. Escaped text never contains two adjacent
// underscores, so the first occurrence of Separator is the unique split
// point (Oak.Modules.Mangle.decode_mangle).
const Separator = "__"

// Escape maps a package path or identifier to the alphabet `[A-Za-z0-9_]`
// such that no two consecutive underscores ever appear in the output:
//
//	ASCII letter or digit -> itself
//	'_'                   -> "_u"
//	'/'                   -> "_s"
//	'.'                   -> "_d"
//	'-'                   -> "_h"
//	any other code point  -> "_x" + six lowercase hex digits
//
// Every '_' in the output is followed by one of `u s d h x`, never by '_'.
// Escape is injective (Oak.Modules.Mangle.unescape_escape).
func Escape(text string) string {
	var out strings.Builder
	for _, r := range text {
		switch {
		case isASCIIAlnum(r):
			out.WriteRune(r)
		case r == '_':
			out.WriteString("_u")
		case r == '/':
			out.WriteString("_s")
		case r == '.':
			out.WriteString("_d")
		case r == '-':
			out.WriteString("_h")
		default:
			fmt.Fprintf(&out, "_x%06x", r)
		}
	}
	return out.String()
}

// Unescape inverts Escape. It reports false for text that Escape cannot
// have produced (a lone '_', an unknown escape letter, a non-alphanumeric
// literal character, or a malformed hex run).
func Unescape(text string) (string, bool) {
	var out strings.Builder
	runes := []rune(text)
	for i := 0; i < len(runes); i++ {
		r := runes[i]
		if r != '_' {
			if !isASCIIAlnum(r) {
				return "", false
			}
			out.WriteRune(r)
			continue
		}
		if i+1 >= len(runes) {
			return "", false
		}
		i++
		switch runes[i] {
		case 'u':
			out.WriteRune('_')
		case 's':
			out.WriteRune('/')
		case 'd':
			out.WriteRune('.')
		case 'h':
			out.WriteRune('-')
		case 'x':
			// Six hex digits must follow at runes[i+1 .. i+6].
			if i+7 > len(runes) {
				return "", false
			}
			value := rune(0)
			for _, h := range runes[i+1 : i+7] {
				d, ok := hexDigit(h)
				if !ok {
					return "", false
				}
				value = value*16 + rune(d)
			}
			out.WriteRune(value)
			i += 6
		default:
			return "", false
		}
	}
	return out.String(), true
}

// Mangle produces the internal name of declaration `name` owned by the
// package at import path `path`. The result is a valid Oak and C identifier
// fragment that user code can never spell, because identifiers containing
// Separator are reserved (Reserved).
func Mangle(path, name string) string {
	return Escape(path) + Separator + Escape(name)
}

// Demangle recovers the package path and declaration name of a mangled
// internal name. It reports false for text that is not a canonical mangling.
func Demangle(internal string) (path, name string, ok bool) {
	index := strings.Index(internal, Separator)
	if index < 0 {
		return "", "", false
	}
	path, ok = Unescape(internal[:index])
	if !ok {
		return "", "", false
	}
	name, ok = Unescape(internal[index+len(Separator):])
	if !ok {
		return "", "", false
	}
	if Mangle(path, name) != internal {
		return "", "", false
	}
	return path, name, true
}

// Reserved reports whether an identifier spelled by user code collides with
// the internal-name space: identifiers containing two adjacent underscores
// are reserved for the compiler (and, as it happens, for C).
func Reserved(identifier string) bool {
	return strings.Contains(identifier, Separator)
}

// DemangleText rewrites every canonical mangled name inside free text to its
// `path.name` source spelling, so diagnostics rendered from the elaborated
// program read as the programmer wrote them.
func DemangleText(text string) string {
	var out strings.Builder
	i := 0
	for i < len(text) {
		if !isIdentStart(text[i]) {
			out.WriteByte(text[i])
			i++
			continue
		}
		j := i
		for j < len(text) && isIdentByte(text[j]) {
			j++
		}
		word := text[i:j]
		if path, name, ok := Demangle(word); ok {
			out.WriteString(path)
			out.WriteByte('.')
			out.WriteString(name)
		} else {
			out.WriteString(word)
		}
		i = j
	}
	return out.String()
}

func isASCIIAlnum(r rune) bool {
	return ('a' <= r && r <= 'z') || ('A' <= r && r <= 'Z') || ('0' <= r && r <= '9')
}

func isIdentStart(b byte) bool {
	return ('a' <= b && b <= 'z') || ('A' <= b && b <= 'Z') || b == '_'
}

func isIdentByte(b byte) bool {
	return isIdentStart(b) || ('0' <= b && b <= '9')
}

func hexDigit(r rune) (int, bool) {
	switch {
	case '0' <= r && r <= '9':
		return int(r - '0'), true
	case 'a' <= r && r <= 'f':
		return int(r-'a') + 10, true
	}
	return 0, false
}

// OpenBind is the loader's check for `open import(path)`
// (docs/spec/83-modules.md section 3.2), a transliteration of
// Oak.Modules.OpenImports.openBind: given the names the importing package
// already binds and the opened package's exports, it either rejects — some
// export is already bound, returned as the offending names — or accepts and
// binds exactly the exports. Acceptance never rebinds a name, so what an
// identifier means never depends on precedence.
func OpenBind(bound func(name string) bool, exports []string) (names []string, collisions []string) {
	for _, name := range exports {
		if bound(name) {
			collisions = append(collisions, name)
		}
	}
	if len(collisions) != 0 {
		return nil, collisions
	}
	return append([]string(nil), exports...), nil
}
