package compiler

import (
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

var parserRegistration = regexp.MustCompile(`p\.register(Prefix|Infix)\(token\.([A-Z_]+),\s*p\.([A-Za-z0-9_]+)\)`)

var syntaxProductionWitnesses = map[string]string{
	"prefix:IDENT": "declarations/typed.exit42.oak",
	"prefix:INT": "declarations/typed.exit42.oak",
	"prefix:STRING": "expressions/string.exit42.oak",
	"prefix:BANG": "expressions/operators.exit42.oak",
	"prefix:NEG": "expressions/operators.exit42.oak",
	"prefix:AMP": "expressions/address_of.exit42.oak",
	"prefix:CARET": "expressions/operators.exit42.oak",
	"prefix:TRUE": "matching/positional_inline.exit42.oak",
	"prefix:DOT": "adts/dot_variant.exit42.oak",
	"prefix:FALSE": "matching/positional_inline.exit42.oak",
	"prefix:LPAREN": "expressions/operators.exit42.oak",
	"prefix:STRUCT": "expressions/struct_literal.parse.oak",
	"prefix:LBRACE": "expressions/record_literal.parse.oak",
	"prefix:LBRACK": "arrays/contextual_literal.exit42.oak",
	"prefix:FN": "functions/function_literal.parse.oak",
	"infix:SUM": "expressions/operators.exit42.oak",
	"infix:AMP": "expressions/operators.exit42.oak",
	"infix:PIPE": "expressions/operators.exit42.oak",
	"infix:PIPE_FORWARD": "expressions/pipeline.exit42.oak",
	"infix:CARET": "expressions/operators.exit42.oak",
	"infix:SHL": "expressions/operators.exit42.oak",
	"infix:SHR": "expressions/operators.exit42.oak",
	"infix:NEG": "expressions/operators.exit42.oak",
	"infix:MUL": "expressions/operators.exit42.oak",
	"infix:QUO": "expressions/operators.exit42.oak",
	"infix:EQL": "expressions/operators.exit42.oak",
	"infix:REM": "expressions/operators.exit42.oak",
	"infix:LAND": "expressions/operators.exit42.oak",
	"infix:LOR": "expressions/operators.exit42.oak",
	"infix:NEQL": "expressions/operators.exit42.oak",
	"infix:LCHEV": "expressions/operators.exit42.oak",
	"infix:LEQ": "expressions/operators.exit42.oak",
	"infix:GEQ": "expressions/operators.exit42.oak",
	"infix:RCHEV": "expressions/operators.exit42.oak",
	"infix:QMARK": "matching/positional_inline.exit42.oak",
	"infix:LPAREN": "functions/declaration_colon.exit42.oak",
	"infix:DOT": "records/struct.exit42.oak",
	"infix:LBRACK": "arrays/slice.exit42.oak",
	"infix:LBRACE": "records/struct.exit42.oak",
}

func TestEveryRegisteredExpressionProductionHasCorpusEvidence(t *testing.T) {
	parserSource, err := os.ReadFile(filepath.Join("..", "parser", "parser.go"))
	if err != nil {
		t.Fatal(err)
	}
	registered := make(map[string]string)
	for _, match := range parserRegistration.FindAllStringSubmatch(string(parserSource), -1) {
		key := strings.ToLower(match[1]) + ":" + match[2]
		registered[key] = match[3]
		witness, ok := syntaxProductionWitnesses[key]
		if !ok {
			t.Errorf("registered parser production %s (%s) has no syntax-corpus witness", key, match[3])
			continue
		}
		if _, ok := syntaxContracts[witness]; !ok {
			t.Errorf("production %s points at uncontracted witness %s", key, witness)
		}
	}
	for key, witness := range syntaxProductionWitnesses {
		if _, ok := registered[key]; !ok {
			t.Errorf("stale production witness %s -> %s: parser no longer registers that production", key, witness)
		}
	}
}
