package main

import (
	"os"
	"regexp"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/compiler"
)

// Literal casts such as u32(1) in the checker sources exist only to name the
// literal's type. With contextual literal typing the bare literal has the same
// type, so removing every literal cast must leave the generated C identical
// once the cast wrapper the backend prints for the explicit spelling is
// normalized away. This pins the equivalence the compiler change claims on the
// actual verification decoder rather than on a toy program.
var literalCast = regexp.MustCompile(`\b(u8|u16|u32|u64|i8|i16|i32|i64)\(([0-9]+)\)`)
var emittedCast = regexp.MustCompile(`\(\((u8|u16|u32|u64|i8|i16|i32|i64)\)\( ([0-9]+) \)\)`)

func checkerSources(t *testing.T) string {
	t.Helper()
	var source strings.Builder
	for _, path := range []string{"self_hosted_rup.oak", "self_hosted_stream.oak", "self_hosted_text.oak"} {
		data, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		source.Write(data)
		source.WriteByte('\n')
	}
	source.WriteString("main: (): i32 {\n cnf: [1]u8\n proof: [1]u8\n cv: []u8 = cnf[0:0]\n pv: []u8 = proof[0:0]\n rup_text_check(cv, pv) ? { 1 } | { 0 }\n}\n")
	return source.String()
}
func emitChecker(t *testing.T, name, source string) string {
	t.Helper()
	generated, err := compiler.New().WithSource(name, source).EmitC().Get()
	if err != nil {
		t.Fatalf("%s: %v", name, err)
	}
	return generated
}
func TestLiteralCastsAreRedundantInChecker(t *testing.T) {
	original := checkerSources(t)
	stripped := literalCast.ReplaceAllString(original, "$2")
	removed := len(literalCast.FindAllStringIndex(original, -1))
	if removed < 150 {
		t.Fatalf("expected the checker sources to carry many literal casts, found %d", removed)
	}
	if literalCast.MatchString(stripped) {
		t.Fatal("literal casts survived stripping")
	}
	withCasts := emittedCast.ReplaceAllString(emitChecker(t, "checker_casts.oak", original), "$2")
	withoutCasts := emitChecker(t, "checker_literals.oak", stripped)
	// Source annotation comments carry the file name and column spans, which the
	// shorter source changes; compare the code only.
	sourceNote := regexp.MustCompile(`(?m)^// @source: .*$`)
	normalize := func(c string) string { return sourceNote.ReplaceAllString(c, "// @source") }
	if normalize(withCasts) != normalize(withoutCasts) {
		a, b := strings.Split(normalize(withCasts), "\n"), strings.Split(normalize(withoutCasts), "\n")
		for i := 0; i < len(a) && i < len(b); i++ {
			if a[i] != b[i] {
				t.Fatalf("generated C differs at line %d:\n casts:    %s\n literals: %s", i+1, a[i], b[i])
			}
		}
		t.Fatalf("generated C differs in length: %d vs %d lines", len(a), len(b))
	}
	t.Logf("checker sources: %d literal casts removed, generated C identical after normalizing the cast wrapper", removed)
}
