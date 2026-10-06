package compiler

import (
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

type surfaceEvidenceLane string

const (
	surfaceNative surfaceEvidenceLane = "native"
	surfaceParse  surfaceEvidenceLane = "parse"
)

type surfaceEvidence struct {
	Path   string
	Test   string
	Needle string
	Lane   surfaceEvidenceLane
	Reason string
}

var parserRegistrationPattern = regexp.MustCompile("p\\.register(Prefix|Infix)\\(token\\.([A-Z_]+),\\s*p\\.([A-Za-z0-9_]+)\\)")
var statementTokenPattern = regexp.MustCompile("case token\\.([A-Z_]+):")
var contextualStatementPattern = regexp.MustCompile("p\\.currentToken\\.Literal == \"([^\"]+)\"")

func native(path, test, needle string) surfaceEvidence {
	return surfaceEvidence{Path: path, Test: test, Needle: needle, Lane: surfaceNative}
}

func parseOnly(path, test, needle, reason string) surfaceEvidence {
	return surfaceEvidence{Path: path, Test: test, Needle: needle, Lane: surfaceParse, Reason: reason}
}

var expressionSurfaceEvidence = map[string][]surfaceEvidence{
	"prefix:IDENT": {
		native("e2e_test.go", "TestE2EExitCodePassthrough", "main: (): i32 = 42"),
		native("e2e_quantifier_test.go", "TestE2EQuantifiers", "forall (x: u16)"),
	},
	"prefix:INT":     {native("e2e_test.go", "TestE2EExitCodePassthrough", "i32 = 42")},
	"prefix:FLOAT":   {native("e2e_floats_test.go", "TestE2EFloatSemantics", "a: f32 = 0.1")},
	"prefix:STRING":  {native("e2e_string_equality_test.go", "TestE2EStringEquality", "greet: (): string = \"hi\"")},
	"prefix:BANG":    {native("e2e_test.go", "TestE2EIfStatementsAndLogicalOperators", "!f.masked")},
	"prefix:NEG":     {native("e2e_statement_ergonomics_test.go", "TestE2ELineStartMinusBeginsStatement", "-x ==")},
	"prefix:AMP":     {native("e2e_test.go", "TestE2ESpanWritesRoundTrip", "span(&data)")},
	"prefix:CARET":   {native("e2e_bitwise_test.go", "TestE2ERegisterBitfields", "^hcrFMO")},
	"prefix:TRUE":    {native("e2e_test.go", "TestE2EIfStatementsAndLogicalOperators", "pending: true")},
	"prefix:FALSE":   {native("e2e_test.go", "TestE2EIfStatementsAndLogicalOperators", "masked: false")},
	"prefix:DOT": {
		native("e2e_elm_ergonomics_test.go", "TestE2EFirstClassFieldAccessor", ".name"),
		native("e2e_test.go", "TestE2EADTConstructAndMatch", ".Circle"),
	},
	"prefix:LPAREN":  {native("e2e_bitwise_test.go", "TestE2ERegisterBitfields", "(hcr >> 3)")},
	"prefix:STRUCT":  {parseOnly("surface_contract_test.go", "TestSurfaceStaticExpressionRoutes", "struct { x: 1 }", "anonymous struct literals are parser compatibility; named structs carry the runtime representation contract")},
	"prefix:LBRACE":  {parseOnly("surface_contract_test.go", "TestSurfaceStaticExpressionRoutes", "value := { x: 1 }", "anonymous semantic records intentionally do not promise a byte representation")},
	"prefix:LBRACK":  {native("e2e_uniform_call_test.go", "TestE2EUniformCallSyntax", "xs: [3]u32 = [7, 8, 9]")},
	"prefix:FN":      {native("e2e_statement_ergonomics_test.go", "TestE2ETypedFunctionLiterals", "fn(x: u32)")},
	"prefix:IMPORT":  {native("e2e_modules_test.go", "TestE2EModulesMultiPackageProgram", "geo := import(")},
	"prefix:TYPE":    {parseOnly("surface_contract_test.go", "TestSurfaceStaticExpressionRoutes", "Key: type", "type-kind expressions are compile-time module-signature syntax")},
	"prefix:TRY":     {native("e2e_try_test.go", "TestE2ETryCompiled", "try above(n)")},

	"infix:SUM":          {native("e2e_test.go", "TestE2EDeclarationFormCallsAndAssertSuccess", "base * factor, 1")},
	"infix:AMP":          {native("e2e_bitwise_test.go", "TestE2ERegisterBitfields", "hcr & hcrFMO")},
	"infix:PIPE":         {native("e2e_bitwise_test.go", "TestE2ERegisterBitfields", "hcrVM | hcrFMO")},
	"infix:PIPE_FORWARD": {native("e2e_elm_ergonomics_test.go", "TestE2EElmPipelineAndFieldAccessor", "|>")},
	"infix:CARET":        {native("e2e_bitwise_test.go", "TestE2ERegisterBitfields", "hcr ^ hcrVM")},
	"infix:SHL":          {native("e2e_bitwise_test.go", "TestE2ERegisterBitfields", "<< 27")},
	"infix:SHR":          {native("e2e_bitwise_test.go", "TestE2ERegisterBitfields", "hcr >> 3")},
	"infix:NEG":          {native("e2e_statement_ergonomics_test.go", "TestE2ELineStartMinusBeginsStatement", "50 -")},
	"infix:MUL":          {native("e2e_test.go", "TestE2EDeclarationFormCallsAndAssertSuccess", "base * factor")},
	"infix:QUO":          {native("e2e_floats_test.go", "TestE2EFloatSemantics", "1.0 / zero")},
	"infix:REM":          {native("e2e_try_test.go", "TestE2ETryCompiled", "n % u32(2)")},
	"infix:LAND":         {native("e2e_test.go", "TestE2EIfStatementsAndLogicalOperators", "&&")},
	"infix:LOR":          {native("e2e_test.go", "TestE2EIfStatementsAndLogicalOperators", "||")},
	"infix:EQL":          {native("e2e_test.go", "TestE2EIfStatementsAndLogicalOperators", "n == 0")},
	"infix:NEQL":         {native("e2e_string_equality_test.go", "TestE2EStringEquality", "a != b")},
	"infix:LCHEV":        {native("e2e_test.go", "TestE2EIfStatementsAndLogicalOperators", "n < 0")},
	"infix:LEQ":          {native("e2e_quantifier_test.go", "TestE2EQuantifiers", "x <= i8(127)")},
	"infix:GEQ":          {native("e2e_quantifier_test.go", "TestE2EQuantifiers", "x >= i8(-128)")},
	"infix:RCHEV":        {native("e2e_try_test.go", "TestE2ETryCompiled", "n > u32(4)")},
	"infix:QMARK":        {native("e2e_value_conditionals_test.go", "TestE2EValueConditionals", "?")},
	"infix:LPAREN":       {native("e2e_test.go", "TestE2EDeclarationFormCallsAndAssertSuccess", "scale(10, 5)")},
	"infix:DOT":          {native("e2e_uniform_call_test.go", "TestE2EUniformCallSyntax", "v.scale(2.0).norm1()")},
	"infix:LBRACK":       {native("e2e_test.go", "TestE2ESpanWritesRoundTrip", "s[0]")},
	"infix:LBRACE":       {native("e2e_test.go", "TestE2ERecordsEndToEnd", "Point { x: 11, y: 31 }")},
}

var statementSurfaceEvidence = map[string][]surfaceEvidence{
	"PACKAGE":   {native("e2e_modules_test.go", "TestE2EModulesMultiPackageProgram", "package geometry")},
	"IMPORT":    {native("e2e_modules_test.go", "TestE2EModulesMultiPackageProgram", "import(\"example.com/hello/geometry\")")},
	"TYPE":      {parseOnly("surface_contract_test.go", "TestSurfaceLegacyKeywordRoutes", "type Color: type", "keyword-prefixed type declarations are accepted compatibility syntax")},
	"INTERFACE": {parseOnly("surface_contract_test.go", "TestSurfaceLegacyKeywordRoutes", "interface Reader: interface", "keyword-prefixed interface declarations are accepted compatibility syntax")},
	"FN":        {native("e2e_elm_ergonomics_test.go", "TestE2EFirstClassFieldAccessor", "fn apply(")},
	"WHILE":     {native("e2e_test.go", "TestE2EBoundedLoopIndexingSum", "while i < n")},
	"BREAK":     {native("e2e_break_test.go", "TestE2EBreak", "break")},
	"RETURN":    {native("surface_contract_test.go", "TestE2ESurfaceReturnRoute", "return 42")},
	"DEFER":     {native("e2e_defer_test.go", "TestE2EDeferCompiled", "defer")},
	"UNSAFE":    {native("e2e_unsafe_block_test.go", "TestE2EUnsafeBlockExecutes", "unsafe {")},
	"PUB":       {native("e2e_modules_test.go", "TestE2EModulesMultiPackageProgram", "pub origin:")},
	"LBRACE": {
		native("e2e_statement_ergonomics_test.go", "TestE2EBareBlockStatementScopes", "{\n    y: u32 = 41"),
		native("e2e_modules_test.go", "TestE2EModulesSelectiveImport", "{ f, g }"),
	},
	"IDENT": {
		native("e2e_test.go", "TestE2EExitCodePassthrough", "main: (): i32 = 42"),
		native("e2e_test.go", "TestE2EColonlessDefinitionForm", "add(l: i32, r: i32)"),
	},
	"SEMI":  {native("surface_contract_test.go", "TestE2ESurfaceSemicolonRoute", "; x: i32 = 40;")},
	"COLON": {parseOnly("surface_contract_test.go", "TestSurfaceREPLRoute", ":exit", "REPL directives are tooling syntax, not compiled-program runtime")},
}

var contextualStatementEvidence = map[string][]surfaceEvidence{
	"open":     {native("e2e_modules_test.go", "TestE2EModulesOpenImport", "open import")},
	"operator": {native("e2e_reduce_order_test.go", "TestE2EOrderScopes", "operator(+)")},
	"kernel":   {native("e2e_kernels_test.go", "TestE2EKernelsRunOnTheHost", "kernel ")},
	"export":   {native("e2e_c_exports_test.go", "TestE2EExportsFromAnyPackage", "export(\"")},
	"module":   {native("e2e_modules_test.go", "TestE2EModulesNestedModules", "module ")},
	"order":    {native("e2e_reduce_order_test.go", "TestE2EOrderScopes", "order tree")},
	"_":        {native("e2e_try_test.go", "TestE2ETryCompiled", "_ = try")},
}

func testFunctionBody(t *testing.T, path, name string) string {
	t.Helper()
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("%s: %v", path, err)
	}
	text := string(data)
	start := strings.Index(text, "func "+name+"(")
	if start < 0 {
		t.Fatalf("%s does not define %s", path, name)
	}
	rest := text[start+1:]
	end := strings.Index(rest, "\nfunc Test")
	if end < 0 {
		return text[start:]
	}
	return text[start : start+1+end]
}

func validateSurfaceEvidence(t *testing.T, key string, evidence []surfaceEvidence) {
	t.Helper()
	if len(evidence) == 0 {
		t.Fatalf("%s has no evidence", key)
	}
	for _, witness := range evidence {
		body := testFunctionBody(t, witness.Path, witness.Test)
		if witness.Needle == "" || !strings.Contains(body, witness.Needle) {
			t.Errorf("%s: %s/%s does not contain witness %q", key, witness.Path, witness.Test, witness.Needle)
		}
		switch witness.Lane {
		case surfaceNative:
			if !strings.HasPrefix(filepath.Base(witness.Path), "e2e_") && witness.Path != "surface_contract_test.go" {
				t.Errorf("%s: native witness %s must live in an e2e test file", key, witness.Path)
			}
			if !strings.HasPrefix(witness.Test, "TestE2E") {
				t.Errorf("%s: native witness %s must be an E2E test", key, witness.Test)
			}
			if !strings.Contains(body, "buildAndRun(") && !strings.Contains(body, "buildPackageAndRun(") && !strings.Contains(body, "buildAndRunFrom(") {
				t.Errorf("%s: native witness %s does not execute compiled code", key, witness.Test)
			}
		case surfaceParse:
			if witness.Reason == "" {
				t.Errorf("%s: parse-only witness %s needs an explicit non-native reason", key, witness.Test)
			}
		default:
			t.Errorf("%s: unknown evidence lane %q", key, witness.Lane)
		}
	}
}

func parserSource(t *testing.T) string {
	t.Helper()
	data, err := os.ReadFile(filepath.Join("..", "parser", "parser.go"))
	if err != nil {
		t.Fatal(err)
	}
	return string(data)
}

func TestEveryRegisteredExpressionProductionHasOwnedEvidence(t *testing.T) {
	source := parserSource(t)
	seen := make(map[string]bool)
	for _, match := range parserRegistrationPattern.FindAllStringSubmatch(source, -1) {
		key := strings.ToLower(match[1]) + ":" + match[2]
		seen[key] = true
		evidence, ok := expressionSurfaceEvidence[key]
		if !ok {
			t.Errorf("registered parser production %s (%s) has no owned evidence", key, match[3])
			continue
		}
		validateSurfaceEvidence(t, key, evidence)
	}
	for key := range expressionSurfaceEvidence {
		if !seen[key] {
			t.Errorf("stale expression evidence for %s: parser no longer registers it", key)
		}
	}
}

func TestEveryStatementEntryPointHasOwnedEvidence(t *testing.T) {
	source := parserSource(t)
	start := strings.Index(source, "func (p *Parser) parseStatement() ast.Statement")
	end := strings.Index(source, "func (p *Parser) parseExpressionStatementOrIndexAssignment")
	if start < 0 || end <= start {
		t.Fatal("could not isolate parseStatement")
	}
	body := source[start:end]
	seen := make(map[string]bool)
	for _, match := range statementTokenPattern.FindAllStringSubmatch(body, -1) {
		key := match[1]
		seen[key] = true
		evidence, ok := statementSurfaceEvidence[key]
		if !ok {
			t.Errorf("statement token %s has no owned evidence", key)
			continue
		}
		validateSurfaceEvidence(t, "statement:"+key, evidence)
	}
	for _, special := range []struct {
		key, needle string
	}{
		{"SEMI", "p.currentTokenIs(token.SEMI)"},
		{"COLON", "p.currentTokenIs(token.COLON) && p.peekTokenIs(token.IDENT)"},
	} {
		if strings.Contains(body, special.needle) {
			seen[special.key] = true
			validateSurfaceEvidence(t, "statement:"+special.key, statementSurfaceEvidence[special.key])
		}
	}
	for key := range statementSurfaceEvidence {
		if !seen[key] {
			t.Errorf("stale statement evidence for %s", key)
		}
	}

	contextualSeen := make(map[string]bool)
	for _, match := range contextualStatementPattern.FindAllStringSubmatch(body, -1) {
		key := match[1]
		contextualSeen[key] = true
		evidence, ok := contextualStatementEvidence[key]
		if !ok {
			t.Errorf("contextual statement route %q has no owned evidence", key)
			continue
		}
		validateSurfaceEvidence(t, "contextual:"+key, evidence)
	}
	for key := range contextualStatementEvidence {
		if !contextualSeen[key] {
			t.Errorf("stale contextual statement evidence for %q", key)
		}
	}
}

func mustParseSurface(t *testing.T, name, source string) {
	t.Helper()
	if _, err := New().WithSource(name+".oak", source).Parse().Get(); err != nil {
		t.Fatalf("%s: %v", name, err)
	}
}

func TestSurfaceLegacyKeywordRoutes(t *testing.T) {
	mustParseSurface(t, "legacy_type", "type Color: type = Red | Blue\n")
	mustParseSurface(t, "legacy_interface", "interface Reader: interface = fn (self) read(buf: [*]Byte) -> Result[u32, Error]\n")
}

func TestSurfaceStaticExpressionRoutes(t *testing.T) {
	mustParseSurface(t, "anonymous_struct", "value := struct { x: 1 }\n")
	mustParseSurface(t, "anonymous_record", "value := { x: 1 }\n")
	mustParseSurface(t, "type_kind", "h: { Key: type } = import(\"example.com/x\")\n")
}

func TestSurfaceREPLRoute(t *testing.T) {
	mustParseSurface(t, "repl_exit", ":exit\n")
}

func TestE2ESurfaceSemicolonRoute(t *testing.T) {
	code, abnormal := buildAndRun(t, "surface_semicolon", "main: (): i32 = { ; x: i32 = 40; x + 2 }\n")
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v), want 42", code, abnormal)
	}
}

func TestE2ESurfaceReturnRoute(t *testing.T) {
	code, abnormal := buildAndRun(t, "surface_return", "f: (x: i32): i32 { x == 0 ? { return 42 }\n x }\nmain: (): i32 = f(0)\n")
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v), want 42", code, abnormal)
	}
}
