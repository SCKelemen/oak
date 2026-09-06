package diagnostic

import (
	"unicode/utf16"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/lsp"
	"github.com/SCKelemen/oak/token"
)

// DiagnosticSeverity represents the severity of a diagnostic
type DiagnosticSeverity int

const (
	SeverityError DiagnosticSeverity = 1
	SeverityWarning DiagnosticSeverity = 2
	SeverityInformation DiagnosticSeverity = 3
	SeverityHint DiagnosticSeverity = 4
)

type DiagnosticTag int

const (
	TagUnnecessary DiagnosticTag = 1
	TagDeprecated DiagnosticTag = 2
)

type DiagnosticRelatedInformation struct {
	Location lsp.Location
	Message string
}

type CodeDescription struct {
	Href string
}

type Diagnostic struct {
	Range lsp.Range
	Severity DiagnosticSeverity
	Code string
	CodeDescription *CodeDescription
	Source string
	Message string
	Tags []DiagnosticTag
	RelatedInformation []DiagnosticRelatedInformation
	Data interface{}
}

func NewDiagnostic(rng lsp.Range, source, message string) *Diagnostic {
	return &Diagnostic{Range: rng, Severity: SeverityError, Source: source, Message: message}
}

func NewDiagnosticWithCode(rng lsp.Range, source, code, message string) *Diagnostic {
	return &Diagnostic{Range: rng, Severity: SeverityError, Source: source, Code: code, Message: message}
}

func NewWarning(rng lsp.Range, source, message string) *Diagnostic {
	return &Diagnostic{Range: rng, Severity: SeverityWarning, Source: source, Message: message}
}

func NewInformation(rng lsp.Range, source, message string) *Diagnostic {
	return &Diagnostic{Range: rng, Severity: SeverityInformation, Source: source, Message: message}
}

func NewHint(rng lsp.Range, source, message string) *Diagnostic {
	return &Diagnostic{Range: rng, Severity: SeverityHint, Source: source, Message: message}
}

func (d *Diagnostic) AddRelatedInformation(loc lsp.Location, msg string) {
	d.RelatedInformation = append(d.RelatedInformation, DiagnosticRelatedInformation{Location: loc, Message: msg})
}

func (d *Diagnostic) AddTag(tag DiagnosticTag) { d.Tags = append(d.Tags, tag) }

type DiagnosticReporter interface {
	AddDiagnostic(*Diagnostic)
	Diagnostics() []*Diagnostic
}

type DiagnosticCollector struct {
	diagnostics []*Diagnostic
}

func NewDiagnosticCollector() *DiagnosticCollector {
	return &DiagnosticCollector{diagnostics: []*Diagnostic{}}
}

func (dc *DiagnosticCollector) AddDiagnostic(d *Diagnostic) {
	dc.diagnostics = append(dc.diagnostics, d)
}

func (dc *DiagnosticCollector) Diagnostics() []*Diagnostic { return dc.diagnostics }

func (dc *DiagnosticCollector) Errors() []*Diagnostic {
	var errors []*Diagnostic
	for _, d := range dc.diagnostics {
		if d.Severity == SeverityError {
			errors = append(errors, d)
		}
	}
	return errors
}

func (dc *DiagnosticCollector) Warnings() []*Diagnostic {
	var warnings []*Diagnostic
	for _, d := range dc.diagnostics {
		if d.Severity == SeverityWarning {
			warnings = append(warnings, d)
		}
	}
	return warnings
}

func (dc *DiagnosticCollector) HasErrors() bool {
	for _, d := range dc.diagnostics {
		if d.Severity == SeverityError {
			return true
		}
	}
	return false
}

func (dc *DiagnosticCollector) Clear() { dc.diagnostics = []*Diagnostic{} }

// TokenToPosition converts Oak's 1-based UTF-16 token coordinates to LSP's
// 0-based UTF-16 coordinates.
func TokenToPosition(tok *token.Token) lsp.Position {
	return lsp.Position{Line: tok.Line - 1, Character: tok.Column - 1}
}

// TokenToEndPosition returns the exact scanner-recorded end coordinate. The
// fallback exists only for hand-constructed/legacy tokens that predate end
// coordinates; normal compiler tokens never estimate their range.
func TokenToEndPosition(tok *token.Token) lsp.Position {
	if tok.EndLine > 0 && tok.EndColumn > 0 {
		return lsp.Position{Line: tok.EndLine - 1, Character: tok.EndColumn - 1}
	}
	start := TokenToPosition(tok)
	return lsp.Position{Line: start.Line, Character: start.Character + utf16Width(tok.Literal)}
}

func TokenToRange(tok *token.Token) lsp.Range {
	return lsp.Range{Start: TokenToPosition(tok), End: TokenToEndPosition(tok)}
}

func TokenPairToRange(startTok, endTok *token.Token) lsp.Range {
	return lsp.Range{Start: TokenToPosition(startTok), End: TokenToEndPosition(endTok)}
}

func NewDiagnosticFromToken(tok *token.Token, source, message string) *Diagnostic {
	return NewDiagnostic(TokenToRange(tok), source, message)
}

func NewDiagnosticFromTokenWithCode(tok *token.Token, source, code, message string) *Diagnostic {
	return NewDiagnosticWithCode(TokenToRange(tok), source, code, message)
}

func NodeToRange(node ast.Node) lsp.Range {
	switch n := node.(type) {
	case *ast.Identifier:
		return TokenToRange(&n.Token)
	case *ast.IntegerLiteral:
		return TokenToRange(&n.Token)
	case *ast.StringLiteral:
		return TokenToRange(&n.Token)
	case *ast.Boolean:
		return TokenToRange(&n.Token)
	case *ast.VariantExpression:
		return TokenToRange(&n.Token)
	case *ast.PrefixExpression:
		return TokenToRange(&n.Token)
	case *ast.InfixExpression:
		return TokenToRange(&n.Token)
	case *ast.IndexExpression:
		return TokenToRange(&n.Token)
	case *ast.SliceExpression:
		return TokenToRange(&n.Token)
	case *ast.InvocationExpression:
		return TokenToRange(&n.Token)
	case *ast.FunctionLiteral:
		return TokenToRange(&n.Token)
	case *ast.RecordLiteral:
		return TokenToRange(&n.Token)
	case *ast.ArrayLiteral:
		return TokenToRange(&n.Token)
	case *ast.MatchExpression:
		return TokenToRange(&n.Token)
	case *ast.VariableDeclaration:
		return TokenToRange(&n.Token)
	case *ast.AssignmentStatement:
		return TokenToRange(&n.Token)
	case *ast.FunctionStatement:
		return TokenToRange(&n.Token)
	case *ast.BlockStatement:
		return TokenToRange(&n.Token)
	case *ast.WhileStatement:
		return TokenToRange(&n.Token)
	case *ast.ADTType:
		return TokenToRange(&n.Token)
	case *ast.InterfaceType:
		return TokenToRange(&n.Token)
	default:
		return lsp.Range{Start: lsp.Position{Line: 0, Character: 0}, End: lsp.Position{Line: 0, Character: 0}}
	}
}

func NewDiagnosticFromNode(node ast.Node, source, message string) *Diagnostic {
	return NewDiagnostic(NodeToRange(node), source, message)
}

func NewDiagnosticFromNodeWithCode(node ast.Node, source, code, message string) *Diagnostic {
	return NewDiagnosticWithCode(NodeToRange(node), source, code, message)
}

func utf16Width(text string) int {
	width := 0
	for _, r := range text {
		if n := utf16.RuneLen(r); n > 0 {
			width += n
		} else {
			width++
		}
	}
	return width
}
