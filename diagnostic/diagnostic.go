package diagnostic

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/lsp"
	"github.com/SCKelemen/oak/token"
)

// DiagnosticSeverity represents the severity of a diagnostic
type DiagnosticSeverity int

const (
	// Error severity - reports an error
	SeverityError DiagnosticSeverity = 1
	// Warning severity - reports a warning
	SeverityWarning DiagnosticSeverity = 2
	// Information severity - reports information
	SeverityInformation DiagnosticSeverity = 3
	// Hint severity - reports a hint
	SeverityHint DiagnosticSeverity = 4
)

// DiagnosticTag represents additional metadata about a diagnostic
type DiagnosticTag int

const (
	// TagUnnecessary - unused or unnecessary code
	TagUnnecessary DiagnosticTag = 1
	// TagDeprecated - deprecated or obsolete code
	TagDeprecated DiagnosticTag = 2
)

// DiagnosticRelatedInformation represents related message and source code location
type DiagnosticRelatedInformation struct {
	// Location of this related diagnostic information
	Location lsp.Location
	// Message of this related diagnostic information
	Message string
}

// CodeDescription provides a description for an error code
type CodeDescription struct {
	// URI to open with more information about the diagnostic error
	Href string
}

// Diagnostic represents a diagnostic, such as a compiler error or warning
type Diagnostic struct {
	// Range at which the message applies
	Range lsp.Range
	// Severity of the diagnostic (defaults to Error if omitted)
	Severity DiagnosticSeverity
	// Diagnostic code (e.g., "E001", "type-mismatch")
	Code string
	// Optional description for the error code
	CodeDescription *CodeDescription
	// Source of this diagnostic (e.g., "scanner", "parser", "typechecker", "borrowchecker")
	Source string
	// Diagnostic message
	Message string
	// Additional metadata tags
	Tags []DiagnosticTag
	// Array of related diagnostic information
	RelatedInformation []DiagnosticRelatedInformation
	// Data entry field preserved between notifications
	Data interface{}
}

// NewDiagnostic creates a new diagnostic with default severity (Error)
func NewDiagnostic(rng lsp.Range, source, message string) *Diagnostic {
	return &Diagnostic{
		Range:    rng,
		Severity: SeverityError,
		Source:   source,
		Message:  message,
	}
}

// NewDiagnosticWithCode creates a new diagnostic with a code
func NewDiagnosticWithCode(rng lsp.Range, source, code, message string) *Diagnostic {
	return &Diagnostic{
		Range:    rng,
		Severity: SeverityError,
		Source:   source,
		Code:     code,
		Message:  message,
	}
}

// NewWarning creates a new warning diagnostic
func NewWarning(rng lsp.Range, source, message string) *Diagnostic {
	return &Diagnostic{
		Range:    rng,
		Severity: SeverityWarning,
		Source:   source,
		Message:  message,
	}
}

// NewInformation creates a new information diagnostic
func NewInformation(rng lsp.Range, source, message string) *Diagnostic {
	return &Diagnostic{
		Range:    rng,
		Severity: SeverityInformation,
		Source:   source,
		Message:  message,
	}
}

// NewHint creates a new hint diagnostic
func NewHint(rng lsp.Range, source, message string) *Diagnostic {
	return &Diagnostic{
		Range:    rng,
		Severity: SeverityHint,
		Source:   source,
		Message:  message,
	}
}

// AddRelatedInformation adds related diagnostic information
func (d *Diagnostic) AddRelatedInformation(loc lsp.Location, msg string) {
	d.RelatedInformation = append(d.RelatedInformation, DiagnosticRelatedInformation{
		Location: loc,
		Message:  msg,
	})
}

// AddTag adds a tag to the diagnostic
func (d *Diagnostic) AddTag(tag DiagnosticTag) {
	d.Tags = append(d.Tags, tag)
}

// DiagnosticReporter is an interface for types that can report diagnostics
type DiagnosticReporter interface {
	AddDiagnostic(*Diagnostic)
	Diagnostics() []*Diagnostic
}

// DiagnosticCollector collects diagnostics from multiple sources
type DiagnosticCollector struct {
	diagnostics []*Diagnostic
}

// NewDiagnosticCollector creates a new diagnostic collector
func NewDiagnosticCollector() *DiagnosticCollector {
	return &DiagnosticCollector{
		diagnostics: []*Diagnostic{},
	}
}

// AddDiagnostic adds a diagnostic to the collector
func (dc *DiagnosticCollector) AddDiagnostic(d *Diagnostic) {
	dc.diagnostics = append(dc.diagnostics, d)
}

// Diagnostics returns all collected diagnostics
func (dc *DiagnosticCollector) Diagnostics() []*Diagnostic {
	return dc.diagnostics
}

// Errors returns only error-severity diagnostics
func (dc *DiagnosticCollector) Errors() []*Diagnostic {
	var errors []*Diagnostic
	for _, d := range dc.diagnostics {
		if d.Severity == SeverityError {
			errors = append(errors, d)
		}
	}
	return errors
}

// Warnings returns only warning-severity diagnostics
func (dc *DiagnosticCollector) Warnings() []*Diagnostic {
	var warnings []*Diagnostic
	for _, d := range dc.diagnostics {
		if d.Severity == SeverityWarning {
			warnings = append(warnings, d)
		}
	}
	return warnings
}

// HasErrors returns true if there are any error-severity diagnostics
func (dc *DiagnosticCollector) HasErrors() bool {
	for _, d := range dc.diagnostics {
		if d.Severity == SeverityError {
			return true
		}
	}
	return false
}

// Clear clears all diagnostics
func (dc *DiagnosticCollector) Clear() {
	dc.diagnostics = []*Diagnostic{}
}

// TokenToPosition converts a token to an LSP Position
// Token uses 1-based line/column, LSP uses 0-based
func TokenToPosition(tok *token.Token) lsp.Position {
	return lsp.Position{
		Line:      tok.Line - 1,   // Convert 1-based to 0-based
		Character: tok.Column - 1, // Convert 1-based to 0-based (will be converted to UTF-16 if needed)
	}
}

// TokenToRange converts a token to an LSP Range
// Uses the token's start and end positions
func TokenToRange(tok *token.Token) lsp.Range {
	start := TokenToPosition(tok)
	// For end position, we need to calculate based on the token length
	// If we have ByteEnd, we can use that, otherwise estimate from Column + length
	endLine := tok.Line - 1
	endColumn := tok.Column - 1
	if tok.ByteEnd > tok.ByteStart {
		// Estimate column from byte difference (approximate)
		endColumn = tok.Column - 1 + (tok.ByteEnd - tok.ByteStart)
	} else {
		// Fallback: use start position + literal length
		endColumn = tok.Column - 1 + len(tok.Literal)
	}
	return lsp.Range{
		Start: start,
		End: lsp.Position{
			Line:      endLine,
			Character: endColumn,
		},
	}
}

// TokenPairToRange creates a range from start and end tokens
func TokenPairToRange(startTok, endTok *token.Token) lsp.Range {
	return lsp.Range{
		Start: TokenToPosition(startTok),
		End:   TokenToPosition(endTok),
	}
}

// NewDiagnosticFromToken creates a diagnostic from a token
func NewDiagnosticFromToken(tok *token.Token, source, message string) *Diagnostic {
	return NewDiagnostic(TokenToRange(tok), source, message)
}

// NewDiagnosticFromTokenWithCode creates a diagnostic from a token with a code
func NewDiagnosticFromTokenWithCode(tok *token.Token, source, code, message string) *Diagnostic {
	return NewDiagnosticWithCode(TokenToRange(tok), source, code, message)
}

// NodeToRange converts an AST node to an LSP Range
// Most AST nodes have a Token field that we can use
func NodeToRange(node ast.Node) lsp.Range {
	// Try to get token from common node types
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
		// Fallback: return zero range
		return lsp.Range{
			Start: lsp.Position{Line: 0, Character: 0},
			End:   lsp.Position{Line: 0, Character: 0},
		}
	}
}

// NewDiagnosticFromNode creates a diagnostic from an AST node
func NewDiagnosticFromNode(node ast.Node, source, message string) *Diagnostic {
	return NewDiagnostic(NodeToRange(node), source, message)
}

// NewDiagnosticFromNodeWithCode creates a diagnostic from an AST node with a code
func NewDiagnosticFromNodeWithCode(node ast.Node, source, code, message string) *Diagnostic {
	return NewDiagnosticWithCode(NodeToRange(node), source, code, message)
}
