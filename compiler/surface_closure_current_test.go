package compiler

import (
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

func init() {
	current := map[string]syntaxContract{
		"literals/float.exit42.oak":              {Status: syntaxCanonical, Spec: "20-types.md §11.3"},
		"expressions/try.exit42.oak":             {Status: syntaxCanonical, Spec: "10-syntax.md §2d"},
		"control/break.exit42.oak":               {Status: syntaxCanonical, Spec: "85-discipline.md §3"},
		"control/return.exit42.oak":              {Status: syntaxCanonical, Spec: "10-syntax.md §4"},
		"control/defer.exit42.oak":               {Status: syntaxCanonical, Spec: "10-syntax.md §4b"},
		"blocks/bare.exit42.oak":                 {Status: syntaxCanonical, Spec: "10-syntax.md §4c"},
		"declarations/discard.exit42.oak":        {Status: syntaxCanonical, Spec: "85-discipline.md §6"},
		"modules/pub.exit42.oak":                 {Status: syntaxCanonical, Spec: "83-modules.md §6"},
		"modules/import_expression.parse.oak":    {Status: syntaxCanonical, Spec: "83-modules.md §3", NoNativeReason: "an isolated import expression needs a package graph; multi-package native execution is covered by compiler/e2e_modules_test.go"},
		"modules/type_kind_expression.parse.oak": {Status: syntaxCanonical, Spec: "83-modules.md §6.3", NoNativeReason: "type is a compile-time signature member kind; module-signature execution is covered by compiler/e2e_modules_test.go"},
		"modules/open_import.parse.oak":           {Status: syntaxCanonical, Spec: "83-modules.md §3.2", NoNativeReason: "open import requires a package graph; native module execution is covered by compiler/e2e_modules_test.go"},
		"modules/selective_import.parse.oak":      {Status: syntaxCanonical, Spec: "83-modules.md §3", NoNativeReason: "selective import requires a package graph; native module execution is covered by compiler/e2e_modules_test.go"},
		"modules/nested.parse.oak":                {Status: syntaxCanonical, Spec: "83-modules.md §3.5", NoNativeReason: "nested modules are package structure; native nested-module execution is covered by compiler/e2e_modules_test.go"},
		"modules/export.parse.oak":                {Status: syntaxCanonical, Spec: "92-ffi.md §2.9", NoNativeReason: "export syntax defines an external ABI surface; compiler/e2e_c_exports_test.go executes it with a C consumer"},
		"operators/custom.exit42.oak":             {Status: syntaxCanonical, Spec: "10-syntax.md §14"},
		"parallel/order.parse.oak":                {Status: syntaxCanonical, Spec: "55-parallelism.md §4", NoNativeReason: "an order block only changes reduce lowering; compiler/e2e_reduce_order_test.go executes all three orders with the reduce package"},
		"kernels/declaration.exit42.oak":          {Status: syntaxCanonical, Spec: "56-kernels.md"},
	}
	for rel, contract := range current {
		syntaxContracts[rel] = contract
	}

	syntaxFamilies["floating point"] = append(syntaxFamilies["floating point"], "literals/float.exit42.oak")
	syntaxFamilies["propagation"] = append(syntaxFamilies["propagation"], "expressions/try.exit42.oak")
	syntaxFamilies["control flow"] = append(syntaxFamilies["control flow"], "control/break.exit42.oak", "control/return.exit42.oak", "control/defer.exit42.oak")
	syntaxFamilies["blocks"] = append(syntaxFamilies["blocks"], "blocks/bare.exit42.oak")
	syntaxFamilies["declarations"] = append(syntaxFamilies["declarations"], "declarations/discard.exit42.oak")
	syntaxFamilies["modules"] = append(syntaxFamilies["modules"],
		"modules/pub.exit42.oak",
		"modules/import_expression.parse.oak",
		"modules/type_kind_expression.parse.oak",
		"modules/open_import.parse.oak",
		"modules/selective_import.parse.oak",
		"modules/nested.parse.oak",
		"modules/export.parse.oak",
	)
	syntaxFamilies["operators"] = append(syntaxFamilies["operators"], "operators/custom.exit42.oak")
	syntaxFamilies["parallelism"] = append(syntaxFamilies["parallelism"], "parallel/order.parse.oak")
	syntaxFamilies["kernels"] = append(syntaxFamilies["kernels"], "kernels/declaration.exit42.oak")

	syntaxProductionWitnesses["prefix:FLOAT"] = "literals/float.exit42.oak"
	syntaxProductionWitnesses["prefix:IMPORT"] = "modules/import_expression.parse.oak"
	syntaxProductionWitnesses["prefix:TYPE"] = "modules/type_kind_expression.parse.oak"
	syntaxProductionWitnesses["prefix:TRY"] = "expressions/try.exit42.oak"

	syntaxStatementWitnesses["BREAK"] = "control/break.exit42.oak"
	syntaxStatementWitnesses["RETURN"] = "control/return.exit42.oak"
	syntaxStatementWitnesses["DEFER"] = "control/defer.exit42.oak"
	syntaxStatementWitnesses["PUB"] = "modules/pub.exit42.oak"
	syntaxStatementWitnesses["LBRACE"] = "blocks/bare.exit42.oak"
}

var parseStatementHelperCall = regexp.MustCompile(`p\.(parse[A-Za-z0-9_]+)\(`)
var parseStatementContextualRoute = regexp.MustCompile(`p\.currentToken\.Literal == "([^"]+)"`)

var statementHelperWitnesses = map[string]string{
	"parseADTType":                              "adts/type_keyword_legacy.parse.oak",
	"parseAssignmentStatement":                  "declarations/typed.exit42.oak",
	"parseBlockStatement":                       "blocks/bare.exit42.oak",
	"parseDeferStatement":                       "control/defer.exit42.oak",
	"parseDiscardStatement":                     "declarations/discard.exit42.oak",
	"parseExportDeclaration":                    "modules/export.parse.oak",
	"parseExpressionStatementOrIndexAssignment": "expressions/address_of.exit42.oak",
	"parseFunctionDefinitionFromName":           "functions/colonless.exit42.oak",
	"parseFunctionStatement":                    "functions/fn_form.exit42.oak",
	"parseIdentLedStatement":                    "declarations/typed.exit42.oak",
	"parseImportStatement":                      "packages/import.parse.oak",
	"parseInterfaceType":                        "interfaces/keyword_legacy.parse.oak",
	"parseKernelDeclaration":                    "kernels/declaration.exit42.oak",
	"parseModuleDeclaration":                    "modules/nested.parse.oak",
	"parseOpenImport":                           "modules/open_import.parse.oak",
	"parseOperatorDeclaration":                  "operators/custom.exit42.oak",
	"parseOrderBlock":                           "parallel/order.parse.oak",
	"parsePackageStatement":                     "packages/package.parse.oak",
	"parsePubDeclaration":                       "modules/pub.exit42.oak",
	"parseREPLCommand":                          "repl/exit.parse.oak",
	"parseReturnStatement":                      "control/return.exit42.oak",
	"parseShortVariableDeclaration":             "declarations/inferred_or.exit42.oak",
	"parseSelectiveImport":                      "modules/selective_import.parse.oak",
	"parseUnsafeBlock":                          "unsafe/block.check.oak",
	"parseWhileStatement":                       "functions/variadic.exit42.oak",
}

var contextualStatementWitnesses = map[string]string{
	"open":     "modules/open_import.parse.oak",
	"operator": "operators/custom.exit42.oak",
	"kernel":   "kernels/declaration.exit42.oak",
	"export":   "modules/export.parse.oak",
	"module":   "modules/nested.parse.oak",
	"order":    "parallel/order.parse.oak",
	"_":        "declarations/discard.exit42.oak",
}

func currentParseStatementBody(t *testing.T) string {
	t.Helper()
	source, err := os.ReadFile(filepath.Join("..", "parser", "parser.go"))
	if err != nil {
		t.Fatal(err)
	}
	text := string(source)
	start := strings.Index(text, "func (p *Parser) parseStatement() ast.Statement")
	if start < 0 {
		t.Fatal("parseStatement entry point not found")
	}
	endRel := strings.Index(text[start:], "func (p *Parser) parseExpressionStatementOrIndexAssignment")
	if endRel < 0 {
		t.Fatal("parseStatement end marker not found")
	}
	return text[start : start+endRel]
}

func TestEveryParseStatementHelperHasCorpusEvidence(t *testing.T) {
	body := currentParseStatementBody(t)
	seen := make(map[string]bool)
	for _, match := range parseStatementHelperCall.FindAllStringSubmatch(body, -1) {
		name := match[1]
		seen[name] = true
		witness, ok := statementHelperWitnesses[name]
		if !ok {
			t.Errorf("parseStatement helper %s has no syntax-corpus witness", name)
			continue
		}
		if _, ok := syntaxContracts[witness]; !ok {
			t.Errorf("parseStatement helper %s points at uncontracted witness %s", name, witness)
		}
	}
	for name, witness := range statementHelperWitnesses {
		if !seen[name] {
			t.Errorf("stale parseStatement helper witness %s -> %s", name, witness)
		}
	}
}

func TestEveryContextualStatementRouteHasCorpusEvidence(t *testing.T) {
	body := currentParseStatementBody(t)
	seen := make(map[string]bool)
	for _, match := range parseStatementContextualRoute.FindAllStringSubmatch(body, -1) {
		word := match[1]
		seen[word] = true
		witness, ok := contextualStatementWitnesses[word]
		if !ok {
			t.Errorf("contextual statement route %q has no syntax-corpus witness", word)
			continue
		}
		if _, ok := syntaxContracts[witness]; !ok {
			t.Errorf("contextual statement route %q points at uncontracted witness %s", word, witness)
		}
	}
	for word, witness := range contextualStatementWitnesses {
		if !seen[word] {
			t.Errorf("stale contextual statement witness %q -> %s", word, witness)
		}
	}
}


func init() {
	more := map[string]syntaxContract{
		"functions/typed_literal.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §3c"},
		"declarations/tag.exit42.oak": {Status: syntaxCanonical, Spec: "40-records.md field tags"},
		"declarations/protocol.exit42.oak": {Status: syntaxCanonical, Spec: "112-protocols.md §1"},
		"declarations/literals.exit2.oak": {Status: syntaxCanonical, Spec: "113-literals.md §1"},
		"declarations/theorem.parse.oak": {Status: syntaxCanonical, Spec: "125-verification.md", NoNativeReason: "theorem declarations are verification obligations; parsing/extraction/proof checking is the semantic observation rather than ordinary process execution"},
		"declarations/measured.exit40.oak": {Status: syntaxCanonical, Spec: "60-effects-allocation.md §10b"},
		"declarations/section.check.oak": {Status: syntaxCanonical, Spec: "65-machine-memory.md", NoNativeReason: "section placement is an emitted-object/layout property rather than a distinct process behavior"},
		"declarations/threadgroup.parse.oak": {Status: syntaxCanonical, Spec: "56-kernels.md §2a", NoNativeReason: "threadgroup selects Metal address-space storage; compiler/e2e_kernels_test.go exercises the specialized backend"},
		"types/refinement.exit24.oak": {Status: syntaxCanonical, Spec: "20-types.md §12"},
		"functions/effect_clauses.exit42.oak": {Status: syntaxCanonical, Spec: "60-effects-allocation.md §2"},
		"functions/laws.parse.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §14a", NoNativeReason: "laws are compile-time algebraic claims; ordered/reassociated execution is exercised by compiler/e2e_reduce_order_test.go"},
		"functions/dispatch.parse.oak": {Status: syntaxCanonical, Spec: "93-simd.md §6", NoNativeReason: "dispatch selects target-feature realizations; target-specific execution is covered by SIMD/backend e2e tests"},
		"types/function_effect_row.parse.oak": {Status: syntaxCanonical, Spec: "60-effects-allocation.md §2a", NoNativeReason: "a function-type effect row is a static callable contract with no independent runtime representation"},
	}
	for rel, contract := range more {
		syntaxContracts[rel] = contract
	}
	syntaxFamilies["function values"] = append(syntaxFamilies["function values"], "functions/typed_literal.exit42.oak")
	syntaxFamilies["contextual declarations"] = append(syntaxFamilies["contextual declarations"],
		"declarations/tag.exit42.oak",
		"declarations/protocol.exit42.oak",
		"declarations/literals.exit2.oak",
		"declarations/theorem.parse.oak",
	)
	syntaxFamilies["declaration clauses"] = append(syntaxFamilies["declaration clauses"],
		"declarations/measured.exit40.oak",
		"declarations/section.check.oak",
		"declarations/threadgroup.parse.oak",
	)
	syntaxFamilies["refinements"] = append(syntaxFamilies["refinements"], "types/refinement.exit24.oak")
	syntaxFamilies["effect clauses"] = append(syntaxFamilies["effect clauses"], "functions/effect_clauses.exit42.oak", "types/function_effect_row.parse.oak")
	syntaxFamilies["operator laws"] = append(syntaxFamilies["operator laws"], "functions/laws.parse.oak")
	syntaxFamilies["target dispatch"] = append(syntaxFamilies["target dispatch"], "functions/dispatch.parse.oak")

	// FN now has a real canonical native witness; keep the old untyped literal
	// case as an explicit compatibility case rather than the production's best evidence.
	syntaxProductionWitnesses["prefix:FN"] = "functions/typed_literal.exit42.oak"
}

var identContextualKeyword = regexp.MustCompile(`p\.currentToken\.Literal == "([^"]+)"`)
var functionContextualKeyword = regexp.MustCompile(`p\.peekToken\.Literal == "([^"]+)"`)
var declarationClauseCase = regexp.MustCompile(`case "([^"]+)":`)

var identContextualWitnesses = map[string]string{
	"tag":      "declarations/tag.exit42.oak",
	"protocol": "declarations/protocol.exit42.oak",
	"literals": "declarations/literals.exit2.oak",
	"theorem":  "declarations/theorem.parse.oak",
}

var functionClauseWitnesses = map[string]string{
	"effects":  "functions/effect_clauses.exit42.oak",
	"forbids":  "functions/effect_clauses.exit42.oak",
	"laws":     "functions/laws.parse.oak",
	"dispatch": "functions/dispatch.parse.oak",
}

var declarationClauseWitnesses = map[string]string{
	"section":     "declarations/section.check.oak",
	"threadgroup": "declarations/threadgroup.parse.oak",
	"measured":    "declarations/measured.exit40.oak",
}

func parserFunctionBodyForClosure(t *testing.T, name string) string {
	t.Helper()
	source, err := os.ReadFile(filepath.Join("..", "parser", "parser.go"))
	if err != nil {
		t.Fatal(err)
	}
	text := string(source)
	startNeedle := "func (p *Parser) " + name
	start := strings.Index(text, startNeedle)
	if start < 0 {
		t.Fatalf("parser function %s not found", name)
	}
	rest := text[start:]
	if end := strings.Index(rest[len(startNeedle):], "\nfunc "); end >= 0 {
		return rest[:len(startNeedle)+end]
	}
	return rest
}

func requireKeywordClosure(t *testing.T, body string, pattern *regexp.Regexp, witnesses map[string]string, label string) {
	t.Helper()
	seen := make(map[string]bool)
	for _, match := range pattern.FindAllStringSubmatch(body, -1) {
		word := match[1]
		seen[word] = true
		witness, ok := witnesses[word]
		if !ok {
			t.Errorf("%s keyword %q has no syntax-corpus witness", label, word)
			continue
		}
		if _, ok := syntaxContracts[witness]; !ok {
			t.Errorf("%s keyword %q points at uncontracted witness %s", label, word, witness)
		}
	}
	for word, witness := range witnesses {
		if !seen[word] {
			t.Errorf("stale %s keyword witness %q -> %s", label, word, witness)
		}
	}
}

func TestIdentifierLedContextualDeclarationsHaveCorpusEvidence(t *testing.T) {
	requireKeywordClosure(t,
		parserFunctionBodyForClosure(t, "parseIdentLedStatement"),
		identContextualKeyword,
		identContextualWitnesses,
		"identifier-led declaration",
	)
}

func TestFunctionContextualClausesHaveCorpusEvidence(t *testing.T) {
	// Canonical and fn declarations delegate their clauses to this shared grammar.
	requireKeywordClosure(t,
		parserFunctionBodyForClosure(t, "parseFunctionDefinitionWithStyle"),
		functionContextualKeyword,
		functionClauseWitnesses,
		"function clause",
	)
}

func TestVariableDeclarationClausesHaveCorpusEvidence(t *testing.T) {
	requireKeywordClosure(t,
		parserFunctionBodyForClosure(t, "parseVarDeclFromNameAndTypeStart"),
		declarationClauseCase,
		declarationClauseWitnesses,
		"declaration clause",
	)
}

func TestFunctionTypeEffectRowHasCorpusEvidence(t *testing.T) {
	body := parserFunctionBodyForClosure(t, "parseFunctionTypeRow")
	if !strings.Contains(body, `p.peekToken.Literal == "effects"`) {
		t.Fatal("function-type effect-row parser no longer exposes the effects contextual route")
	}
	if _, ok := syntaxContracts["types/function_effect_row.parse.oak"]; !ok {
		t.Fatal("function-type effects route has no contracted syntax witness")
	}
}

func TestRefinementWhereHasCorpusEvidence(t *testing.T) {
	body := parserFunctionBodyForClosure(t, "parseADTTypeFromName")
	if !strings.Contains(body, `p.peekToken.Literal == "where"`) {
		t.Fatal("refinement parser no longer exposes the where contextual route")
	}
	if _, ok := syntaxContracts["types/refinement.exit24.oak"]; !ok {
		t.Fatal("refinement where route has no contracted syntax witness")
	}
}
