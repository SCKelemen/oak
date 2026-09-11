package parser

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

// The `via` clause of a protocol transition carries the whole resource
// contract (docs/spec/112-protocols.md section 5.1): the callable (a
// function or Type.method), parameter and receiver modes, callable
// contracts on function-typed parameters, a result identity, and the
// trusted marker. The AST preserves every part and prints it back.
func TestParser_ProtocolViaClauseRoundTrip(t *testing.T) {
	input := `Lifecycle: protocol = {
  resource Arena
  initial Open
  make: Open -> Open via open(): fresh
  cursor: Open -> Open via cursor_of(borrowed a): borrow a, b
  edit: Open -> Open via mut_cursor(borrowed mut a): borrow mut a
  same: Open -> Open via peek(borrowed a): alias a
  each: Open -> Open via with_each(op(borrowed, _): fresh, borrowed a)
  look: Open -> Open via Cursor.read(borrowed receiver)
  raw: Open -> Open via unsafe cursor_raw(borrowed a): alias a
  plain: Open -> Closed via free(consumed a)
}`
	p := New(scanner.New(input))
	program := p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatalf("unexpected errors: %v", p.Errors())
	}
	decl, ok := program.Statements[0].(*ast.ProtocolDeclaration)
	if !ok {
		t.Fatalf("expected a protocol declaration, got %T", program.Statements[0])
	}
	byName := map[string]*ast.ProtocolTransition{}
	for _, transition := range decl.Transitions {
		byName[transition.Name.Value] = transition
	}
	if r := byName["make"].Result; r == nil || r.Kind != "fresh" || len(r.Names) != 0 {
		t.Errorf("make: result %+v", byName["make"].Result)
	}
	if r := byName["cursor"].Result; r == nil || r.Kind != "borrow" || len(r.Names) != 2 || r.Names[1].Value != "b" {
		t.Errorf("cursor: result %+v", byName["cursor"].Result)
	}
	if r := byName["edit"].Result; r == nil || r.Kind != "borrow mut" || byName["edit"].Modes[0].Mode != "borrowed mut" {
		t.Errorf("edit: result %+v modes %+v", byName["edit"].Result, byName["edit"].Modes[0])
	}
	if r := byName["same"].Result; r == nil || r.Kind != "alias" || r.Names[0].Value != "a" {
		t.Errorf("same: result %+v", byName["same"].Result)
	}
	each := byName["each"]
	if len(each.Modes) != 2 || each.Modes[0].Contract == nil || each.Modes[0].Name.Value != "op" ||
		strings.Join(each.Modes[0].Contract.Modes, ",") != "borrowed,_" || !each.Modes[0].Contract.ReturnsFresh ||
		each.Modes[1].Mode != "borrowed" || each.Modes[1].Name.Value != "a" {
		t.Errorf("each: modes %+v", each.Modes)
	}
	look := byName["look"]
	if look.CallableType == nil || look.CallableType.Value != "Cursor" || look.Callable.Value != "read" || look.Modes[0].Name.Value != "receiver" {
		t.Errorf("look: callable %+v.%+v", look.CallableType, look.Callable)
	}
	if raw := byName["raw"]; !raw.Trusted || raw.Result == nil || raw.Result.Kind != "alias" {
		t.Errorf("raw: trusted %v result %+v", raw.Trusted, raw.Result)
	}
	if plain := byName["plain"]; plain.Trusted || plain.Result != nil || plain.Modes[0].Mode != "consumed" {
		t.Errorf("plain: %+v", plain)
	}

	printed := decl.String()
	for _, want := range []string{
		"via open: fresh",
		"via cursor_of(borrowed a): borrow a, b",
		"via mut_cursor(borrowed mut a): borrow mut a",
		"via peek(borrowed a): alias a",
		"via with_each(op(borrowed, _): fresh, borrowed a)",
		"via Cursor.read(borrowed receiver)",
		"via unsafe cursor_raw(borrowed a): alias a",
		"via free(consumed a)",
	} {
		if !strings.Contains(printed, want) {
			t.Errorf("String() lacks %q:\n%s", want, printed)
		}
	}
}

func TestParser_ProtocolViaClauseRejectsUnknownWords(t *testing.T) {
	for name, line := range map[string]string{
		"result word":     "via peek(borrowed a): owned a",
		"mode word":       "via peek(owned a)",
		"contract mode":   "via each(op(owned))",
		"contract result": "via each(op(borrowed): alias)",
		"missing name":    "via peek(borrowed a): alias",
	} {
		p := New(scanner.New("L: protocol = {\n  resource A\n  initial Open\n  t: Open -> Open " + line + "\n}"))
		p.ParseProgram()
		if len(p.Errors()) == 0 {
			t.Errorf("%s: expected a parse error for %q", name, line)
		}
	}
}
