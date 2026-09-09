package diagnostic

import (
	"fmt"
	"reflect"
	"strings"
	"unicode/utf16"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/lsp"
	"github.com/SCKelemen/oak/token"
)

// DiagnosticSeverity represents the severity of a diagnostic.
type DiagnosticSeverity int

const (
	SeverityError       DiagnosticSeverity = 1
	SeverityWarning     DiagnosticSeverity = 2
	SeverityInformation DiagnosticSeverity = 3
	SeverityHint        DiagnosticSeverity = 4
)

func (s DiagnosticSeverity) String() string {
	switch s {
	case SeverityError:
		return "error"
	case SeverityWarning:
		return "warning"
	case SeverityInformation:
		return "info"
	case SeverityHint:
		return "hint"
	default:
		return "diagnostic"
	}
}

// Category is the semantic subsystem responsible for a diagnostic. Category is
// data, not presentation text; renderers decide how much of it to show.
type Category string

const (
	CategoryUnknown        Category = "unknown"
	CategoryParser         Category = "parser"
	CategoryType           Category = "type"
	CategoryBorrow         Category = "borrow"
	CategoryEffect         Category = "effect"
	CategoryRepresentation Category = "representation"
	CategorySource         Category = "source"
	CategoryCompiler       Category = "compiler"
	CategoryInternal       Category = "internal"
)

// Code is a stable diagnostic identifier. Human wording may improve without
// breaking editor configuration, tests, documentation links, or tooling.
type Code string

const (
	CodeUnknown         Code = "OAK-0000"
	CodeParserGeneric   Code = "OAK-P0000"
	CodeTypeGeneric     Code = "OAK-T0000"
	CodeBorrowGeneric   Code = "OAK-B0000"
	CodeEffectGeneric   Code = "OAK-E0000"
	CodeReprGeneric     Code = "OAK-R0000"
	CodeSourceGeneric   Code = "OAK-S0000"
	CodeCompilerGeneric Code = "OAK-C0000"
	CodeInternalGeneric Code = "OAK-I0000"
)

type DiagnosticTag int

const (
	TagUnnecessary DiagnosticTag = 1
	TagDeprecated  DiagnosticTag = 2
)

type DiagnosticRelatedInformation struct {
	Location lsp.Location
	Message  string
}

type CodeDescription struct {
	Href string
}

// LabelStyle identifies the role one source range plays in explaining a
// diagnostic. A well-formed diagnostic has exactly one primary label.
type LabelStyle int

const (
	LabelPrimary LabelStyle = iota + 1
	LabelSecondary
)

// Label explains why one source range participates in the diagnostic. URI is
// optional for same-file labels; cross-file context continues to use
// RelatedInformation/LSP locations until source IDs are threaded everywhere.
type Label struct {
	Range   lsp.Range
	Style   LabelStyle
	Message string
}

// AdviceKind distinguishes explanation from an actionable suggestion.
type AdviceKind int

const (
	AdviceNote AdviceKind = iota + 1
	AdviceHelp
)

type Advice struct {
	Kind    AdviceKind
	Message string
}

// Diagnostic is Oak's first-class error/warning model. Message and Range are
// retained as LSP-compatible compatibility fields; Title, Labels, and Advice
// are the richer compiler-facing structure. New constructors populate both.
type Diagnostic struct {
	Range    lsp.Range
	Severity DiagnosticSeverity
	// File is the source file the primary cause lives in, when the node's
	// tokens carry one (package builds stamp `package#file` into token
	// contexts, docs/spec/83-modules.md section 7); empty otherwise.
	File               string
	Code               string
	CodeDescription    *CodeDescription
	Source             string
	Category           Category
	Title              string
	Message            string
	Labels             []Label
	Advice             []Advice
	Tags               []DiagnosticTag
	RelatedInformation []DiagnosticRelatedInformation
	Data               interface{}
}

func categoryForSource(source string) Category {
	switch source {
	case "parser":
		return CategoryParser
	case "typechecker", "typecheck", "type":
		return CategoryType
	case "borrowchecker", "borrow":
		return CategoryBorrow
	case "effect", "effects":
		return CategoryEffect
	case "representation", "layout":
		return CategoryRepresentation
	case "source", "scanner":
		return CategorySource
	case "compiler":
		return CategoryCompiler
	case "internal":
		return CategoryInternal
	default:
		return CategoryUnknown
	}
}

func defaultCode(category Category) Code {
	switch category {
	case CategoryParser:
		return CodeParserGeneric
	case CategoryType:
		return CodeTypeGeneric
	case CategoryBorrow:
		return CodeBorrowGeneric
	case CategoryEffect:
		return CodeEffectGeneric
	case CategoryRepresentation:
		return CodeReprGeneric
	case CategorySource:
		return CodeSourceGeneric
	case CategoryCompiler:
		return CodeCompilerGeneric
	case CategoryInternal:
		return CodeInternalGeneric
	default:
		return CodeUnknown
	}
}

func newDiagnostic(rng lsp.Range, severity DiagnosticSeverity, source string, code Code, title string) *Diagnostic {
	category := categoryForSource(source)
	if code == "" {
		code = defaultCode(category)
	}
	return &Diagnostic{
		Range:    rng,
		Severity: severity,
		Code:     string(code),
		Source:   source,
		Category: category,
		Title:    title,
		Message:  title,
		Labels: []Label{{
			Range: rng,
			Style: LabelPrimary,
		}},
	}
}

func NewDiagnostic(rng lsp.Range, source, message string) *Diagnostic {
	return newDiagnostic(rng, SeverityError, source, "", message)
}

func NewDiagnosticWithCode(rng lsp.Range, source, code, message string) *Diagnostic {
	return newDiagnostic(rng, SeverityError, source, Code(code), message)
}

func NewWarning(rng lsp.Range, source, message string) *Diagnostic {
	return newDiagnostic(rng, SeverityWarning, source, "", message)
}

func NewInformation(rng lsp.Range, source, message string) *Diagnostic {
	return newDiagnostic(rng, SeverityInformation, source, "", message)
}

func NewHint(rng lsp.Range, source, message string) *Diagnostic {
	return newDiagnostic(rng, SeverityHint, source, "", message)
}

// SetPrimary replaces the diagnostic's primary source cause while preserving
// all secondary labels. This keeps Range synchronized for LSP compatibility.
func (d *Diagnostic) SetPrimary(rng lsp.Range, msg string) *Diagnostic {
	if d == nil {
		return d
	}
	labels := d.Labels[:0]
	for _, label := range d.Labels {
		if label.Style != LabelPrimary {
			labels = append(labels, label)
		}
	}
	d.Labels = append([]Label{{Range: rng, Style: LabelPrimary, Message: msg}}, labels...)
	d.Range = rng
	return d
}

func (d *Diagnostic) AddSecondary(rng lsp.Range, msg string) *Diagnostic {
	if d != nil {
		d.Labels = append(d.Labels, Label{Range: rng, Style: LabelSecondary, Message: msg})
	}
	return d
}

func (d *Diagnostic) AddNote(msg string) *Diagnostic {
	if d != nil && msg != "" {
		d.Advice = append(d.Advice, Advice{Kind: AdviceNote, Message: msg})
	}
	return d
}

func (d *Diagnostic) AddHelp(msg string) *Diagnostic {
	if d != nil && msg != "" {
		d.Advice = append(d.Advice, Advice{Kind: AdviceHelp, Message: msg})
	}
	return d
}

func (d *Diagnostic) AddRelatedInformation(loc lsp.Location, msg string) {
	d.RelatedInformation = append(d.RelatedInformation, DiagnosticRelatedInformation{Location: loc, Message: msg})
}

func (d *Diagnostic) AddTag(tag DiagnosticTag) { d.Tags = append(d.Tags, tag) }

// Validate checks structural diagnostic invariants independently of rendering.
func (d *Diagnostic) Validate() error {
	if d == nil {
		return fmt.Errorf("nil diagnostic")
	}
	if d.Code == "" {
		return fmt.Errorf("diagnostic has no stable code")
	}
	if strings.TrimSpace(d.Title) == "" {
		return fmt.Errorf("diagnostic has no title")
	}
	primary := 0
	for _, label := range d.Labels {
		if label.Style == LabelPrimary {
			primary++
		}
	}
	if primary != 1 {
		return fmt.Errorf("diagnostic must have exactly one primary label, got %d", primary)
	}
	return nil
}

// PlainText renders the semantic diagnostic without source snippets. CLI code
// can add file/excerpt rendering around this while LSP consumes the same object.
func (d *Diagnostic) PlainText() string {
	if d == nil {
		return ""
	}
	var out strings.Builder
	switch {
	case d.File != "":
		fmt.Fprintf(&out, "%s[%s]: %s:%d:%d: %s", d.Severity.String(), d.Code, d.File, d.Range.Start.Line+1, d.Range.Start.Character+1, d.Title)
	case d.Range.Start.Line != 0 || d.Range.Start.Character != 0:
		// A known position is rendered even when the file is unknown
		// (single-source compilations): docs/spec/15-diagnostics.md
		// section 10 — never drop an exact location the value carries.
		fmt.Fprintf(&out, "%s[%s]: %d:%d: %s", d.Severity.String(), d.Code, d.Range.Start.Line+1, d.Range.Start.Character+1, d.Title)
	default:
		fmt.Fprintf(&out, "%s[%s]: %s", d.Severity.String(), d.Code, d.Title)
	}
	for _, label := range d.Labels {
		if label.Message == "" {
			continue
		}
		kind := "primary"
		if label.Style == LabelSecondary {
			kind = "secondary"
		}
		fmt.Fprintf(&out, "\n  = %s: %s", kind, label.Message)
	}
	for _, advice := range d.Advice {
		kind := "note"
		if advice.Kind == AdviceHelp {
			kind = "help"
		}
		fmt.Fprintf(&out, "\n  = %s: %s", kind, advice.Message)
	}
	return out.String()
}

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
	case *ast.BlockExpression:
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
	d := NewDiagnostic(NodeToRange(node), source, message)
	d.File = NodeFile(node)
	return d
}

func NewDiagnosticFromNodeWithCode(node ast.Node, source, code, message string) *Diagnostic {
	d := NewDiagnosticWithCode(NodeToRange(node), source, code, message)
	d.File = NodeFile(node)
	return d
}

// NodeFile reads the source file a node's first token was stamped with
// (`package#file` in SemanticContext); "" when unknown.
func NodeFile(node ast.Node) string {
	if node == nil {
		return ""
	}
	tok, ok := firstToken(reflect.ValueOf(node), 0)
	if !ok {
		return ""
	}
	context := tok.SemanticContext
	if index := strings.IndexByte(context, '|'); index >= 0 {
		context = context[:index]
	}
	if index := strings.IndexByte(context, '#'); index >= 0 {
		return context[index+1:]
	}
	return ""
}

var tokenReflectType = reflect.TypeOf(token.Token{})

func firstToken(v reflect.Value, depth int) (token.Token, bool) {
	if depth > 3 {
		return token.Token{}, false
	}
	switch v.Kind() {
	case reflect.Interface, reflect.Pointer:
		if v.IsNil() {
			return token.Token{}, false
		}
		return firstToken(v.Elem(), depth)
	case reflect.Struct:
		if v.Type() == tokenReflectType {
			return v.Interface().(token.Token), true
		}
		for i := 0; i < v.NumField(); i++ {
			if !v.Type().Field(i).IsExported() {
				continue
			}
			if tok, ok := firstToken(v.Field(i), depth+1); ok {
				return tok, true
			}
		}
	}
	return token.Token{}, false
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
