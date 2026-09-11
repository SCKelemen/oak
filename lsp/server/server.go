package server

// The Oak language server (docs/spec/115-tooling.md section 4): `oak lsp`
// speaks the Language Server Protocol over stdio — JSON-RPC 2.0 messages in
// Content-Length frames — and answers from the same compiler pipeline every
// other tool uses. Open documents are compiled through an overlay
// (compiler.Compilation.WithOverlay), so the editor's unsaved text is what
// the checker sees and nothing is ever written to disk. Diagnostics are the
// semantic model's, hover is the checked type of the identifier under the
// cursor, definition finds the declaration in the same package, document
// symbols are the top-level declarations, and semantic tokens classify the
// scanner's tokens for highlighting. The server never opens a socket.

import (
	"bufio"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/url"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"sync"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/lsp"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/token"
)

// LSP wire forms: the lsp package's Position/Range/Location carry no JSON
// tags (they are shared with the diagnostics' own serialization), so the
// server renders them with the protocol's lowercase keys.
type wirePosition struct {
	Line      int `json:"line"`
	Character int `json:"character"`
}

type wireRange struct {
	Start wirePosition `json:"start"`
	End   wirePosition `json:"end"`
}

type wireLocation struct {
	URI   string    `json:"uri"`
	Range wireRange `json:"range"`
}

func wirePos(p lsp.Position) wirePosition { return wirePosition{Line: p.Line, Character: p.Character} }

func wireRng(r lsp.Range) wireRange { return wireRange{Start: wirePos(r.Start), End: wirePos(r.End)} }

// MaxMessageBytes bounds one JSON-RPC message.
const MaxMessageBytes = 16 << 20

// Server is one language server session over a reader/writer pair.
type Server struct {
	in  *bufio.Reader
	out io.Writer
	log io.Writer

	mu     sync.Mutex
	docs   map[string]string // absolute path -> text
	models map[string]*analysis
}

// analysis is the last compilation of a package directory.
type analysis struct {
	model *compiler.SemanticModel
	err   error
}

// Serve runs a session until `exit`, the input closes, or a malformed frame
// arrives (which ends the session with an error rather than being partially
// processed).
func Serve(in io.Reader, out, log io.Writer) error {
	s := &Server{in: bufio.NewReaderSize(in, 1<<16), out: out, log: log, docs: map[string]string{}, models: map[string]*analysis{}}
	for {
		body, err := s.readFrame()
		if err != nil {
			if errors.Is(err, io.EOF) {
				return nil
			}
			return err
		}
		var message struct {
			ID     json.RawMessage `json:"id"`
			Method string          `json:"method"`
			Params json.RawMessage `json:"params"`
		}
		if err := json.Unmarshal(body, &message); err != nil {
			return fmt.Errorf("malformed JSON-RPC message: %w", err)
		}
		if message.Method == "exit" {
			return nil
		}
		if exit := s.dispatch(message.ID, message.Method, message.Params); exit {
			return nil
		}
	}
}

// readFrame reads one Content-Length framed message.
func (s *Server) readFrame() ([]byte, error) {
	length := -1
	for {
		line, err := s.in.ReadString('\n')
		if err != nil {
			return nil, err
		}
		line = strings.TrimRight(line, "\r\n")
		if line == "" {
			break
		}
		name, value, ok := strings.Cut(line, ":")
		if !ok {
			return nil, fmt.Errorf("malformed header %q", line)
		}
		if strings.EqualFold(strings.TrimSpace(name), "Content-Length") {
			n, err := strconv.Atoi(strings.TrimSpace(value))
			if err != nil || n < 0 {
				return nil, fmt.Errorf("malformed Content-Length %q", value)
			}
			if n > MaxMessageBytes {
				return nil, fmt.Errorf("message of %d bytes exceeds %d", n, MaxMessageBytes)
			}
			length = n
		}
	}
	if length < 0 {
		return nil, errors.New("frame without Content-Length")
	}
	body := make([]byte, length)
	if _, err := io.ReadFull(s.in, body); err != nil {
		return nil, err
	}
	return body, nil
}

func (s *Server) send(payload interface{}) {
	body, err := json.Marshal(payload)
	if err != nil {
		fmt.Fprintf(s.log, "oak lsp: encode: %v\n", err)
		return
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	fmt.Fprintf(s.out, "Content-Length: %d\r\n\r\n", len(body))
	s.out.Write(body)
}

func (s *Server) reply(id json.RawMessage, result interface{}) {
	if id == nil {
		return
	}
	s.send(map[string]interface{}{"jsonrpc": "2.0", "id": id, "result": result})
}

func (s *Server) replyError(id json.RawMessage, code int, message string) {
	if id == nil {
		return
	}
	s.send(map[string]interface{}{"jsonrpc": "2.0", "id": id, "error": map[string]interface{}{"code": code, "message": message}})
}

func (s *Server) notify(method string, params interface{}) {
	s.send(map[string]interface{}{"jsonrpc": "2.0", "method": method, "params": params})
}

// semanticTokenTypes is the legend, in index order.
var semanticTokenTypes = []string{"keyword", "function", "variable", "type", "string", "number", "comment", "operator", "namespace", "property"}

const (
	tokKeyword = iota
	tokFunction
	tokVariable
	tokType
	tokString
	tokNumber
	tokComment
	tokOperator
	tokNamespace
	tokProperty
)

// dispatch handles one message; it reports whether the session should end.
func (s *Server) dispatch(id json.RawMessage, method string, params json.RawMessage) bool {
	switch method {
	case "initialize":
		s.reply(id, map[string]interface{}{
			"capabilities": map[string]interface{}{
				"textDocumentSync":       1,
				"hoverProvider":          true,
				"definitionProvider":     true,
				"documentSymbolProvider": true,
				"semanticTokensProvider": map[string]interface{}{
					"legend": map[string]interface{}{"tokenTypes": semanticTokenTypes, "tokenModifiers": []string{}},
					"full":   true,
				},
			},
			"serverInfo": map[string]string{"name": "oak"},
		})
	case "initialized", "$/cancelRequest", "textDocument/willSave", "workspace/didChangeConfiguration":
	case "shutdown":
		s.reply(id, nil)
	case "textDocument/didOpen":
		var p struct {
			TextDocument struct {
				URI  string `json:"uri"`
				Text string `json:"text"`
			} `json:"textDocument"`
		}
		if path, ok := s.decode(id, params, &p, p.TextDocument.URI); ok {
			s.open(path, p.TextDocument.Text)
		}
	case "textDocument/didChange":
		var p struct {
			TextDocument struct {
				URI string `json:"uri"`
			} `json:"textDocument"`
			ContentChanges []struct {
				Text string `json:"text"`
			} `json:"contentChanges"`
		}
		if path, ok := s.decode(id, params, &p, p.TextDocument.URI); ok && len(p.ContentChanges) != 0 {
			s.open(path, p.ContentChanges[len(p.ContentChanges)-1].Text)
		}
	case "textDocument/didSave":
		var p struct {
			TextDocument struct {
				URI string `json:"uri"`
			} `json:"textDocument"`
		}
		if path, ok := s.decode(id, params, &p, p.TextDocument.URI); ok {
			s.analyze(filepath.Dir(path))
		}
	case "textDocument/didClose":
		var p struct {
			TextDocument struct {
				URI string `json:"uri"`
			} `json:"textDocument"`
		}
		if path, ok := s.decode(id, params, &p, p.TextDocument.URI); ok {
			s.mu.Lock()
			delete(s.docs, path)
			s.mu.Unlock()
			s.notify("textDocument/publishDiagnostics", map[string]interface{}{"uri": fileURI(path), "diagnostics": []interface{}{}})
		}
	case "textDocument/hover":
		var p positionParams
		if path, ok := s.decode(id, params, &p, p.TextDocument.URI); ok {
			s.reply(id, s.hover(path, p.Position))
		}
	case "textDocument/definition":
		var p positionParams
		if path, ok := s.decode(id, params, &p, p.TextDocument.URI); ok {
			s.reply(id, s.definition(path, p.Position))
		}
	case "textDocument/documentSymbol":
		var p struct {
			TextDocument struct {
				URI string `json:"uri"`
			} `json:"textDocument"`
		}
		if path, ok := s.decode(id, params, &p, p.TextDocument.URI); ok {
			s.reply(id, s.documentSymbols(path))
		}
	case "textDocument/semanticTokens/full":
		var p struct {
			TextDocument struct {
				URI string `json:"uri"`
			} `json:"textDocument"`
		}
		if path, ok := s.decode(id, params, &p, p.TextDocument.URI); ok {
			s.reply(id, map[string]interface{}{"data": s.semanticTokens(path)})
		}
	default:
		if id != nil {
			s.replyError(id, -32601, "method not found: "+method)
		}
	}
	return false
}

type positionParams struct {
	TextDocument struct {
		URI string `json:"uri"`
	} `json:"textDocument"`
	Position lsp.Position `json:"position"`
}

// decode unmarshals params and resolves the document URI. The uri argument
// is read after unmarshaling through the pointer, so callers pass the field
// of the struct they decode into.
func (s *Server) decode(id json.RawMessage, params json.RawMessage, into interface{}, _ string) (string, bool) {
	if err := json.Unmarshal(params, into); err != nil {
		s.replyError(id, -32602, "invalid params: "+err.Error())
		return "", false
	}
	uri := uriOf(into)
	path, err := uriPath(uri)
	if err != nil {
		s.replyError(id, -32602, err.Error())
		return "", false
	}
	return path, true
}

// uriOf digs the textDocument.uri out of decoded params via JSON.
func uriOf(params interface{}) string {
	data, _ := json.Marshal(params)
	var shape struct {
		TextDocument struct {
			URI string `json:"uri"`
		} `json:"textDocument"`
	}
	_ = json.Unmarshal(data, &shape)
	return shape.TextDocument.URI
}

// uriPath converts a file: URI to an absolute path; any other scheme is
// rejected.
func uriPath(uri string) (string, error) {
	u, err := url.Parse(uri)
	if err != nil {
		return "", fmt.Errorf("invalid document uri %q", uri)
	}
	if u.Scheme != "file" {
		return "", fmt.Errorf("unsupported document uri scheme %q (only file:)", u.Scheme)
	}
	path := u.Path
	if path == "" {
		return "", fmt.Errorf("document uri %q has no path", uri)
	}
	return filepath.Abs(filepath.FromSlash(path))
}

func fileURI(path string) string {
	return (&url.URL{Scheme: "file", Path: filepath.ToSlash(path)}).String()
}

// open records a document and re-analyzes its package.
func (s *Server) open(path, text string) {
	s.mu.Lock()
	s.docs[path] = text
	s.mu.Unlock()
	s.analyze(filepath.Dir(path))
}

// analyze compiles the package at dir with the open documents overlaid and
// publishes diagnostics for every open document of that package.
func (s *Server) analyze(dir string) {
	s.mu.Lock()
	overlay := map[string]string{}
	var open []string
	for path, text := range s.docs {
		overlay[path] = text
		if filepath.Dir(path) == dir {
			open = append(open, path)
		}
	}
	s.mu.Unlock()
	model, err := compiler.New().WithPackageDir(dir).WithOverlay(overlay).SemanticModel().Get()
	s.mu.Lock()
	s.models[dir] = &analysis{model: model, err: err}
	s.mu.Unlock()

	var all []*diagnostic.Diagnostic
	if model != nil {
		all = append(all, model.Diagnostics...)
	}
	var diagErr *compiler.DiagnosticError
	if errors.As(err, &diagErr) {
		all = append(all, diagErr.Diagnostics...)
	} else if err != nil && len(open) != 0 {
		// A failure without diagnostics (a manifest problem, an unreadable
		// dependency): attach it to the first open document.
		all = append(all, &diagnostic.Diagnostic{File: open[0], Severity: diagnostic.SeverityError, Code: "OAK-LSP", Message: err.Error()})
	}
	sort.Strings(open)
	for _, path := range open {
		s.notify("textDocument/publishDiagnostics", map[string]interface{}{"uri": fileURI(path), "diagnostics": lspDiagnostics(all, path, dir)})
	}
}

// lspDiagnostics renders the diagnostics that belong to path.
func lspDiagnostics(all []*diagnostic.Diagnostic, path, dir string) []map[string]interface{} {
	out := []map[string]interface{}{}
	seen := map[string]bool{}
	for _, d := range all {
		if d == nil {
			continue
		}
		file := d.File
		if abs, err := filepath.Abs(file); err == nil && file != "" {
			file = abs
		}
		if file != path && !(file == "" && filepath.Dir(path) == dir && isOnlyDocument(path, dir)) {
			continue
		}
		message := d.Title
		if message == "" {
			message = d.Message
		}
		message = modules.DemangleText(message)
		for _, label := range d.Labels {
			if label.Message != "" {
				message += "\n" + modules.DemangleText(label.Message)
				break
			}
		}
		severity := 1
		switch d.Severity {
		case diagnostic.SeverityWarning:
			severity = 2
		case diagnostic.SeverityInformation:
			severity = 3
		}
		entry := map[string]interface{}{
			"range":    wireRng(d.Range),
			"severity": severity,
			"code":     d.Code,
			"source":   "oak",
			"message":  message,
		}
		key := fmt.Sprintf("%d:%d:%s:%s", d.Range.Start.Line, d.Range.Start.Character, d.Code, message)
		if !seen[key] {
			seen[key] = true
			out = append(out, entry)
		}
	}
	return out
}

// isOnlyDocument reports whether path is the only source file of its
// directory, in which case file-less diagnostics belong to it.
func isOnlyDocument(path, dir string) bool {
	entries, err := os.ReadDir(dir)
	if err != nil {
		return true
	}
	count := 0
	for _, entry := range entries {
		if !entry.IsDir() && strings.HasSuffix(entry.Name(), ".oak") {
			count++
		}
	}
	return count <= 1
}

// tokensOf scans a document.
func tokensOf(text string) []token.Token {
	sc := scanner.New(text)
	var tokens []token.Token
	for {
		tok := sc.NextToken()
		if tok.TokenKind == token.EOF {
			break
		}
		if tok.TokenKind == token.TRIVIA {
			continue
		}
		tokens = append(tokens, tok)
	}
	return tokens
}

// identifierAt finds the identifier token covering an LSP position, and the
// index of that token.
func identifierAt(tokens []token.Token, position lsp.Position) (token.Token, int, bool) {
	for i, tok := range tokens {
		if tok.TokenKind != token.IDENT || tok.Line-1 != position.Line {
			continue
		}
		if tok.Column-1 <= position.Character && position.Character < tok.EndColumn-1 {
			return tok, i, true
		}
	}
	return token.Token{}, -1, false
}

func (s *Server) document(path string) (string, bool) {
	s.mu.Lock()
	defer s.mu.Unlock()
	text, ok := s.docs[path]
	return text, ok
}

func (s *Server) modelFor(dir string) *compiler.SemanticModel {
	s.mu.Lock()
	defer s.mu.Unlock()
	if a := s.models[dir]; a != nil {
		return a.model
	}
	return nil
}

// hover reports the type of the identifier under the cursor.
func (s *Server) hover(path string, position lsp.Position) interface{} {
	text, ok := s.document(path)
	if !ok {
		return nil
	}
	tokens := tokensOf(text)
	tok, index, found := identifierAt(tokens, position)
	if !found {
		return nil
	}
	name := tok.Literal
	rendered := ""
	if index > 0 && tokens[index-1].TokenKind == token.DOT {
		rendered = fmt.Sprintf("%s: member", name)
	} else if model := s.modelFor(filepath.Dir(path)); model != nil && model.TypeChecker != nil {
		if scheme, ok := model.TypeChecker.Env().Get(name); ok && scheme != nil && scheme.Type != nil {
			rendered = fmt.Sprintf("%s: %s", name, modules.DemangleText(scheme.Type.String()))
		}
	}
	if rendered == "" {
		if decl := localDeclaration(text, name, position); decl != "" {
			rendered = decl
		}
	}
	if rendered == "" {
		// Without a checked model (the package does not type check yet), the
		// document's own declaration still says what the name is.
		rendered = declaredSignature(text, name)
	}
	if rendered == "" {
		return nil
	}
	return map[string]interface{}{
		"contents": map[string]string{"kind": "markdown", "value": "```oak\n" + rendered + "\n```"},
		"range":    wireRng(tokenRange(tok)),
	}
}

func tokenRange(tok token.Token) lsp.Range {
	return lsp.Range{Start: lsp.Position{Line: tok.Line - 1, Character: tok.Column - 1}, End: lsp.Position{Line: tok.EndLine - 1, Character: tok.EndColumn - 1}}
}

// localDeclaration renders a parameter or local declaration of name in the
// function enclosing position, from the document's own syntax.
func localDeclaration(text, name string, position lsp.Position) string {
	program := parser.New(scanner.New(text)).ParseProgram()
	if program == nil {
		return ""
	}
	for _, stmt := range program.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || !enclosesLine(fn, position.Line+1) {
			continue
		}
		for _, parameter := range fn.Parameters {
			if parameter != nil && parameter.Name != nil && parameter.Name.Value == name && parameter.Type != nil {
				return fmt.Sprintf("%s: %s (parameter)", name, parameter.Type.String())
			}
		}
		rendered := ""
		walkDeclarations(fn.Body, func(decl *ast.VariableDeclaration) {
			if decl.Name == nil || decl.Name.Value != name || rendered != "" {
				return
			}
			if decl.Type != nil {
				rendered = fmt.Sprintf("%s: %s", name, decl.Type.String())
			} else {
				rendered = fmt.Sprintf("%s := %s", name, truncate(decl.Value.String(), 60))
			}
		})
		if rendered != "" {
			return rendered
		}
	}
	return ""
}

// declaredSignature renders a top-level declaration of name from the
// document's syntax alone.
func declaredSignature(text, name string) string {
	program := parser.New(scanner.New(text)).ParseProgram()
	if program == nil {
		return ""
	}
	for _, stmt := range program.Statements {
		switch d := stmt.(type) {
		case *ast.FunctionStatement:
			if d.Name == nil || d.Name.Value != name {
				continue
			}
			params := make([]string, 0, len(d.Parameters))
			for _, parameter := range d.Parameters {
				if parameter == nil || parameter.Name == nil {
					continue
				}
				if parameter.Type != nil {
					params = append(params, parameter.Name.Value+": "+parameter.Type.String())
				} else {
					params = append(params, parameter.Name.Value)
				}
			}
			result := ""
			if d.ReturnType != nil {
				result = ": " + d.ReturnType.String()
			}
			return fmt.Sprintf("%s: (%s)%s", name, strings.Join(params, ", "), result)
		case *ast.VariableDeclaration:
			if d.Name != nil && d.Name.Value == name {
				if d.Type != nil {
					return fmt.Sprintf("%s: %s", name, d.Type.String())
				}
				return fmt.Sprintf("%s := %s", name, truncate(d.Value.String(), 60))
			}
		case *ast.ADTType:
			if d.Name != nil && d.Name.Value == name {
				return name + ": type"
			}
		case *ast.InterfaceType:
			if d.Name != nil && d.Name.Value == name {
				return name + ": interface"
			}
		}
	}
	return ""
}

func truncate(text string, limit int) string {
	if len(text) <= limit {
		return text
	}
	return text[:limit] + "…"
}

// enclosesLine reports whether a function's source span covers the 1-based
// line.
func enclosesLine(fn *ast.FunctionStatement, line int) bool {
	start := fn.Token.Line
	end := fn.EndToken.Line
	if end == 0 {
		end = start
	}
	return start <= line && line <= end
}

// walkDeclarations visits variable declarations under an expression.
func walkDeclarations(expr ast.Expression, visit func(*ast.VariableDeclaration)) {
	var walkStmt func(ast.Statement)
	var walkExpr func(ast.Expression)
	walkStmt = func(stmt ast.Statement) {
		switch s := stmt.(type) {
		case *ast.VariableDeclaration:
			visit(s)
			walkExpr(s.Value)
		case *ast.WhileStatement:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					walkStmt(inner)
				}
			}
		case *ast.BlockStatement:
			for _, inner := range s.Statements {
				walkStmt(inner)
			}
		case *ast.UnsafeBlock:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					walkStmt(inner)
				}
			}
		case *ast.ExpressionStatement:
			walkExpr(s.Expression)
		}
	}
	walkExpr = func(expr ast.Expression) {
		switch e := expr.(type) {
		case *ast.BlockExpression:
			if e.Block != nil {
				for _, inner := range e.Block.Statements {
					walkStmt(inner)
				}
			}
		case *ast.MatchExpression:
			for _, arm := range e.Arms {
				walkExpr(arm.Body)
			}
		}
	}
	walkExpr(expr)
}

// declarationSite is a top-level declaration's name token.
type declarationSite struct {
	name string
	kind int // LSP SymbolKind
	tok  token.Token
	end  token.Token
}

// declarations lists a program's top-level declarations.
func declarations(program *ast.Program) []declarationSite {
	var out []declarationSite
	if program == nil {
		return nil
	}
	for _, stmt := range program.Statements {
		switch d := stmt.(type) {
		case *ast.FunctionStatement:
			if d.Name != nil {
				kind := 12
				if d.Receiver != nil {
					kind = 6
				}
				out = append(out, declarationSite{d.Name.Value, kind, d.Name.Token, d.EndToken})
			}
		case *ast.VariableDeclaration:
			if d.Name != nil {
				out = append(out, declarationSite{d.Name.Value, 13, d.Name.Token, d.Name.Token})
			}
		case *ast.ADTType:
			if d.Name != nil {
				kind := 10
				if len(d.Variants) == 1 && d.Variants[0] != nil && d.Variants[0].Literal != nil {
					kind = 23
				}
				out = append(out, declarationSite{d.Name.Value, kind, d.Name.Token, d.Name.Token})
			}
		case *ast.InterfaceType:
			if d.Name != nil {
				out = append(out, declarationSite{d.Name.Value, 11, d.Name.Token, d.Name.Token})
			}
		case *ast.ModuleDeclaration:
			if d.Name != nil {
				out = append(out, declarationSite{d.Name.Value, 2, d.Name.Token, d.Name.Token})
			}
		case *ast.TagDeclaration:
			if d.Name != nil {
				out = append(out, declarationSite{d.Name.Value, 7, d.Name.Token, d.Name.Token})
			}
		}
	}
	return out
}

// definition locates the declaration of the identifier under the cursor: a
// local of the enclosing function, a top-level declaration of the document,
// or a top-level declaration of another file of the same package.
func (s *Server) definition(path string, position lsp.Position) interface{} {
	text, ok := s.document(path)
	if !ok {
		return nil
	}
	tokens := tokensOf(text)
	tok, index, found := identifierAt(tokens, position)
	if !found || (index > 0 && tokens[index-1].TokenKind == token.DOT) {
		return nil
	}
	name := tok.Literal
	program := parser.New(scanner.New(text)).ParseProgram()
	// Locals first.
	if program != nil {
		for _, stmt := range program.Statements {
			fn, ok := stmt.(*ast.FunctionStatement)
			if !ok || !enclosesLine(fn, position.Line+1) {
				continue
			}
			for _, parameter := range fn.Parameters {
				if parameter != nil && parameter.Name != nil && parameter.Name.Value == name {
					return wireLocation{URI: fileURI(path), Range: wireRng(tokenRange(parameter.Name.Token))}
				}
			}
			var site *token.Token
			walkDeclarations(fn.Body, func(decl *ast.VariableDeclaration) {
				if decl.Name != nil && decl.Name.Value == name && site == nil && decl.Name.Token.Line <= position.Line+1 {
					t := decl.Name.Token
					site = &t
				}
			})
			if site != nil {
				return wireLocation{URI: fileURI(path), Range: wireRng(tokenRange(*site))}
			}
		}
	}
	for _, decl := range declarations(program) {
		if decl.name == name {
			return wireLocation{URI: fileURI(path), Range: wireRng(tokenRange(decl.tok))}
		}
	}
	// Other files of the package.
	dir := filepath.Dir(path)
	entries, err := os.ReadDir(dir)
	if err != nil {
		return nil
	}
	for _, entry := range entries {
		if entry.IsDir() || !strings.HasSuffix(entry.Name(), ".oak") {
			continue
		}
		other := filepath.Join(dir, entry.Name())
		if other == path {
			continue
		}
		otherText, ok := s.document(other)
		if !ok {
			data, err := os.ReadFile(other)
			if err != nil {
				continue
			}
			otherText = string(data)
		}
		for _, decl := range declarations(parser.New(scanner.New(otherText)).ParseProgram()) {
			if decl.name == name {
				return wireLocation{URI: fileURI(other), Range: wireRng(tokenRange(decl.tok))}
			}
		}
	}
	return nil
}

// documentSymbols lists the document's top-level declarations.
func (s *Server) documentSymbols(path string) interface{} {
	text, ok := s.document(path)
	if !ok {
		return []interface{}{}
	}
	out := []map[string]interface{}{}
	for _, decl := range declarations(parser.New(scanner.New(text)).ParseProgram()) {
		selection := tokenRange(decl.tok)
		full := selection
		if decl.end.Line != 0 && (decl.end.Line > decl.tok.Line || (decl.end.Line == decl.tok.Line && decl.end.EndColumn > decl.tok.EndColumn)) {
			full.End = lsp.Position{Line: decl.end.EndLine - 1, Character: decl.end.EndColumn - 1}
			if decl.end.EndLine == 0 {
				full.End = lsp.Position{Line: decl.end.Line - 1, Character: decl.end.Column}
			}
		}
		out = append(out, map[string]interface{}{
			"name":           decl.name,
			"kind":           decl.kind,
			"range":          wireRng(full),
			"selectionRange": wireRng(selection),
		})
	}
	return out
}

// builtinTypes are the type names highlighted as types.
var builtinTypes = map[string]bool{
	"u8": true, "u16": true, "u32": true, "u64": true, "i8": true, "i16": true, "i32": true, "i64": true,
	"int": true, "uint": true, "uptr": true, "byte": true, "rune": true, "f32": true, "f64": true, "f16": true, "bf16": true,
	"Bool": true, "String": true, "string": true, "type": true,
}

// semanticTokens classifies the document's tokens, encoded as LSP relative
// deltas. Tokens spanning lines are emitted for their first line only.
func (s *Server) semanticTokens(path string) []uint32 {
	text, ok := s.document(path)
	if !ok {
		return []uint32{}
	}
	tokens := tokensOf(text)
	program := parser.New(scanner.New(text)).ParseProgram()
	functions, types, namespaces := map[string]bool{}, map[string]bool{}, map[string]bool{}
	for _, decl := range declarations(program) {
		switch decl.kind {
		case 12, 6:
			functions[decl.name] = true
		case 10, 23, 11:
			types[decl.name] = true
		case 2:
			namespaces[decl.name] = true
		}
	}
	if program != nil {
		for _, stmt := range program.Statements {
			if imp, ok := stmt.(*ast.ImportStatement); ok {
				if imp.Alias != nil {
					namespaces[imp.Alias.Value] = true
				} else if imp.Path != nil && len(imp.Names) == 0 && !imp.Open {
					namespaces[modules.LastSegment(imp.Path.Value)] = true
				}
			}
		}
	}
	data := []uint32{}
	prevLine, prevStart := 0, 0
	for i, tok := range tokens {
		kind := -1
		switch {
		case tok.TokenKind.IsKeyword():
			kind = tokKeyword
		case tok.TokenKind == token.COMMENT:
			kind = tokComment
		case tok.TokenKind == token.STRING:
			kind = tokString
		case tok.TokenKind == token.INT || tok.TokenKind == token.FLOAT:
			kind = tokNumber
		case tok.TokenKind == token.IDENT:
			name := tok.Literal
			previousDot := i > 0 && tokens[i-1].TokenKind == token.DOT
			nextParen := i+1 < len(tokens) && tokens[i+1].TokenKind == token.LPAREN
			switch {
			case name == "open" || name == "module" || name == "derive":
				kind = tokKeyword
			case (name == "effects" || name == "forbids" || name == "laws") && i+1 < len(tokens) && tokens[i+1].TokenKind == token.LBRACE,
				name == "operator" && nextParen:
				// Contextual clause keywords (docs/spec/60-effects-allocation.md
				// section 2, 10-syntax.md section 14): keywords only in front of
				// their brace or parenthesis, identifiers elsewhere.
				kind = tokKeyword
			case previousDot:
				kind = tokProperty
				if nextParen {
					kind = tokFunction
				}
			case namespaces[name]:
				kind = tokNamespace
			case functions[name] || nextParen && !builtinTypes[name]:
				kind = tokFunction
			case types[name] || builtinTypes[name] || (name != "" && name[0] >= 'A' && name[0] <= 'Z'):
				kind = tokType
			default:
				kind = tokVariable
			}
		case tok.TokenKind >= token.LCHEV && tok.TokenKind <= token.LOR && tok.TokenKind != token.COMMA && tok.TokenKind != token.DOT && tok.TokenKind != token.COLON && tok.TokenKind != token.SEMI:
			kind = tokOperator
		}
		if kind < 0 || tok.Line != tok.EndLine && tok.EndLine != 0 && tok.EndLine != tok.Line {
			if kind < 0 {
				continue
			}
		}
		line, start := tok.Line-1, tok.Column-1
		length := tok.EndColumn - tok.Column
		if tok.EndLine != tok.Line {
			// First line only: to the end of the line the token starts on.
			length = lineLength(text, line) - start
		}
		if length <= 0 || line < prevLine || (line == prevLine && start < prevStart) {
			continue
		}
		deltaLine := line - prevLine
		deltaStart := start
		if deltaLine == 0 {
			deltaStart = start - prevStart
		}
		data = append(data, uint32(deltaLine), uint32(deltaStart), uint32(length), uint32(kind), 0)
		prevLine, prevStart = line, start
	}
	return data
}

// lineLength is the UTF-16 length of the 0-based line.
func lineLength(text string, line int) int {
	lines := strings.Split(text, "\n")
	if line < 0 || line >= len(lines) {
		return 0
	}
	return lsp.UTF8ToUTF16Offset(lines[line], len(lines[line]))
}

// ServeStdio runs the server on the process's standard streams.
func ServeStdio() error {
	return Serve(os.Stdin, os.Stdout, os.Stderr)
}
