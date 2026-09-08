package compiler

import (
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"testing"
)

type syntaxContract struct {
	Status            string
	Spec              string
	NoNativeReason    string
	CompatibilityNote string
}

const (
	syntaxCanonical     = "canonical"
	syntaxCompatibility = "compatibility"
)

var syntaxContracts = map[string]syntaxContract{
	"declarations/typed.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §2"},
	"declarations/inferred.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §2"},
	"declarations/semicolon_block.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §5"},
	"packages/package.parse.oak": {Status: syntaxCanonical, Spec: "10-syntax.md package declarations", NoNativeReason: "package declaration selects compilation identity and has no standalone process behavior"},
	"packages/import.parse.oak": {Status: syntaxCanonical, Spec: "10-syntax.md import declarations", NoNativeReason: "import syntax is a compile-time dependency surface and this isolated corpus does not resolve external packages"},
	"functions/declaration_colon.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §3"},
	"functions/declaration_arrow.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §3"},
	"functions/colonless.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §3"},
	"functions/fn_form.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §3"},
	"functions/layout_body.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §4"},
	"functions/variadic.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §3 variadic"},
	"functions/generic_declaration.exit42.oak": {Status: syntaxCanonical, Spec: "20-types.md §11.2"},
	"functions/generic_fn.parse.oak": {Status: syntaxCompatibility, Spec: "10-syntax.md §3", NoNativeReason: "legacy generic fn spelling is protected as parser compatibility; canonical generics use name[T] declarations", CompatibilityNote: "retain while historical fn-generic sources remain accepted"},
	"functions/function_literal.parse.oak": {Status: syntaxCompatibility, Spec: "05-ergonomics-and-cost.md closure direction", NoNativeReason: "captureless function literals are accepted but C function-literal emission is not the canonical function-value surface", CompatibilityNote: "accepted parser surface pending an explicit literal syntax decision"},
	"matching/positional_inline.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §3a"},
	"matching/pattern_fat_arrow.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §7"},
	"matching/braced_fat_arrow.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §7"},
	"matching/legacy_arrow.parse.oak": {Status: syntaxCompatibility, Spec: "10-syntax.md §1", NoNativeReason: "legacy -> match arms are parser compatibility only; => is the canonical match token", CompatibilityNote: "migration alias; formatter must not emit it"},
	"matching/legacy_typed_qualified_pattern.parse.oak": {Status: syntaxCompatibility, Spec: "10-syntax.md §7", NoNativeReason: "typed Type::Case payload patterns are historical parser compatibility", CompatibilityNote: "canonical patterns use .Case(binding) or Type.Case(binding) without an inline payload type annotation"},
	"expressions/operators.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §§3a,3b"},
	"expressions/address_of.exit42.oak": {Status: syntaxCanonical, Spec: "50-borrowing.md"},
	"expressions/pipeline.exit42.oak": {Status: syntaxCanonical, Spec: "05-ergonomics-and-cost.md pipeline ergonomics"},
	"expressions/field_accessor_pipeline.exit42.oak": {Status: syntaxCanonical, Spec: "05-ergonomics-and-cost.md pipeline ergonomics"},
	"expressions/string.exit42.oak": {Status: syntaxCanonical, Spec: "70-strings.md"},
	"expressions/record_literal.parse.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §8", NoNativeReason: "anonymous semantic record literal has no promised runtime representation without contextual representation selection"},
	"expressions/struct_literal.parse.oak": {Status: syntaxCompatibility, Spec: "10-syntax.md §8", NoNativeReason: "anonymous struct value spelling is parser surface; named concrete construction is the representation-bearing canonical boundary form", CompatibilityNote: "prefer named Type { ... } construction"},
	"literals/decimal.exit42.oak": {Status: syntaxCanonical, Spec: "20-types.md integer literals"},
	"literals/hex.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §3b"},
	"literals/binary.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §3b"},
	"literals/radix.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §3b"},
	"literals/radix_separator.exit42.oak": {Status: syntaxCanonical, Spec: "20-types.md integer literals"},
	"literals/unicode_radix.exit242.oak": {Status: syntaxCanonical, Spec: "20-types.md integer literals"},
	"arrays/contextual_literal.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §1 array forms"},
	"arrays/slice.exit42.oak": {Status: syntaxCanonical, Spec: "50-borrowing.md"},
	"arrays/slice_open_low.exit42.oak": {Status: syntaxCanonical, Spec: "50-borrowing.md"},
	"arrays/slice_open_high.exit42.oak": {Status: syntaxCanonical, Spec: "50-borrowing.md"},
	"arrays/slice_all.exit42.oak": {Status: syntaxCanonical, Spec: "50-borrowing.md"},
	"arrays/typed_literal_legacy.parse.oak": {Status: syntaxCompatibility, Spec: "10-syntax.md array migration", NoNativeReason: "typed aggregate literal [N]T{...} is historical parser compatibility", CompatibilityNote: "canonical source uses contextual [a, b, ...] literals with an expected [N]T"},
	"arrays/nested_typed_legacy.parse.oak": {Status: syntaxCompatibility, Spec: "10-syntax.md array migration", NoNativeReason: "nested typed aggregate literal syntax is historical parser compatibility", CompatibilityNote: "retain only while old aggregate sources remain accepted"},
	"adts/dot_variant.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §6"},
	"adts/qualified_dot.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §6"},
	"adts/qualified_colon_colon.parse.oak": {Status: syntaxCompatibility, Spec: "10-syntax.md §1", NoNativeReason: "Type::Case is a legacy constructor spelling", CompatibilityNote: "migration alias; canonical qualification is Type.Case"},
	"adts/brace_legacy.parse.oak": {Status: syntaxCompatibility, Spec: "10-syntax.md §6", NoNativeReason: "brace-delimited ADT declaration is historical parser compatibility", CompatibilityNote: "canonical multiline ADTs use layout with leading pipes"},
	"adts/shorthand_legacy.parse.oak": {Status: syntaxCompatibility, Spec: "10-syntax.md §6", NoNativeReason: "Name := A | B shorthand is historical parser compatibility", CompatibilityNote: "canonical ADTs use Name: type = ..."},
	"adts/type_keyword_legacy.parse.oak": {Status: syntaxCompatibility, Spec: "10-syntax.md §6", NoNativeReason: "keyword-prefixed type Name: type = ... is a parser compatibility entry point", CompatibilityNote: "canonical declarations are Name: type = ..."},
	"adts/indexed.check.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §6", NoNativeReason: "this case establishes indexed constructor-result typing; runtime GADT specialization is tested separately"},
	"records/semantic.check.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §8", NoNativeReason: "semantic record shape intentionally does not promise byte representation"},
	"records/struct.exit42.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §8"},
	"records/extensible.parse.oak": {Status: syntaxCanonical, Spec: "05-ergonomics-and-cost.md extensible records", NoNativeReason: "row-polymorphic record syntax is a semantic typing surface rather than a standalone runtime representation"},
	"records/composition.parse.oak": {Status: syntaxCompatibility, Spec: "10-syntax.md §9", NoNativeReason: "record composition is accepted definition-time syntax without a standalone runtime observation", CompatibilityNote: "kept while the shared & token remains accepted for record composition"},
	"interfaces/generic_typed_self.parse.oak": {Status: syntaxCompatibility, Spec: "10-syntax.md §9", NoNativeReason: "generic interface receiver syntax is compile-time contract syntax and has no runtime interface object", CompatibilityNote: "accepted historical interface spelling until interface syntax is normalized"},
	"interfaces/keyword_legacy.parse.oak": {Status: syntaxCompatibility, Spec: "10-syntax.md §9", NoNativeReason: "keyword-prefixed interface Name: interface = ... is a parser compatibility route", CompatibilityNote: "canonical source uses Name: interface = ..."},
	"methods/legacy_colon_colon.parse.oak": {Status: syntaxCompatibility, Spec: "10-syntax.md §3", NoNativeReason: "legacy receiver method syntax is parser compatibility and has no canonical runtime witness", CompatibilityNote: "retain only while Point::method source remains accepted"},
	"types/array_forms.parse.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §1", NoNativeReason: "type-form inventory has no independent runtime behavior"},
	"types/generic_application.check.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §1", NoNativeReason: "generic application typing is the observation; executable generic instantiations have separate native cases"},
	"types/lowercase_bool.parse.oak": {Status: syntaxCompatibility, Spec: "20-types.md primitive naming", NoNativeReason: "lowercase bool is a historical parser spelling", CompatibilityNote: "canonical Boolean type is Bool"},
	"unsafe/block.check.oak": {Status: syntaxCanonical, Spec: "10-syntax.md §10", NoNativeReason: "unsafe is a static assumption boundary; this case observes acceptance without pretending the marker has runtime behavior"},
	"repl/exit.parse.oak": {Status: syntaxCompatibility, Spec: "REPL command surface", NoNativeReason: "REPL directives are tooling syntax, not compiled program runtime", CompatibilityNote: "kept as an interactive parser route rather than canonical compilation-unit syntax"},
}

var syntaxFamilies = map[string][]string{
	"declarations": {"declarations/typed.exit42.oak", "declarations/inferred.exit42.oak", "declarations/semicolon_block.exit42.oak"},
	"package and import": {"packages/package.parse.oak", "packages/import.parse.oak"},
	"function declarations": {"functions/declaration_colon.exit42.oak", "functions/declaration_arrow.exit42.oak", "functions/colonless.exit42.oak", "functions/fn_form.exit42.oak", "functions/layout_body.exit42.oak"},
	"function values": {"functions/function_literal.parse.oak"},
	"generics": {"functions/generic_declaration.exit42.oak", "functions/generic_fn.parse.oak", "types/generic_application.check.oak"},
	"variadics": {"functions/variadic.exit42.oak"},
	"matches and conditionals": {"matching/positional_inline.exit42.oak", "matching/pattern_fat_arrow.exit42.oak", "matching/braced_fat_arrow.exit42.oak", "matching/legacy_arrow.parse.oak", "matching/legacy_typed_qualified_pattern.parse.oak"},
	"operators": {"expressions/operators.exit42.oak", "expressions/address_of.exit42.oak", "expressions/pipeline.exit42.oak", "expressions/field_accessor_pipeline.exit42.oak"},
	"integer literals": {"literals/decimal.exit42.oak", "literals/hex.exit42.oak", "literals/binary.exit42.oak", "literals/radix.exit42.oak", "literals/radix_separator.exit42.oak", "literals/unicode_radix.exit242.oak"},
	"literals": {"expressions/string.exit42.oak", "arrays/contextual_literal.exit42.oak", "arrays/typed_literal_legacy.parse.oak", "arrays/nested_typed_legacy.parse.oak", "expressions/record_literal.parse.oak", "expressions/struct_literal.parse.oak"},
	"arrays and slices": {"arrays/contextual_literal.exit42.oak", "arrays/slice.exit42.oak", "arrays/slice_open_low.exit42.oak", "arrays/slice_open_high.exit42.oak", "arrays/slice_all.exit42.oak", "arrays/typed_literal_legacy.parse.oak", "arrays/nested_typed_legacy.parse.oak", "types/array_forms.parse.oak"},
	"ADTs": {"adts/dot_variant.exit42.oak", "adts/qualified_dot.exit42.oak", "adts/qualified_colon_colon.parse.oak", "adts/brace_legacy.parse.oak", "adts/shorthand_legacy.parse.oak", "adts/type_keyword_legacy.parse.oak", "adts/indexed.check.oak"},
	"records": {"records/semantic.check.oak", "records/struct.exit42.oak", "records/extensible.parse.oak", "records/composition.parse.oak"},
	"interfaces": {"interfaces/generic_typed_self.parse.oak", "interfaces/keyword_legacy.parse.oak"},
	"methods": {"methods/legacy_colon_colon.parse.oak"},
	"primitive compatibility": {"types/lowercase_bool.parse.oak"},
	"unsafe boundary": {"unsafe/block.check.oak"},
	"REPL tooling": {"repl/exit.parse.oak"},
}

func TestSyntaxContractClosesCorpus(t *testing.T) {
	root := filepath.Join("testdata", "syntax")
	owned := make(map[string][]string)
	for family, paths := range syntaxFamilies {
		if len(paths) == 0 {
			t.Errorf("syntax family %q has no cases", family)
		}
		for _, rel := range paths {
			owned[rel] = append(owned[rel], family)
		}
	}
	for rel, contract := range syntaxContracts {
		if contract.Status != syntaxCanonical && contract.Status != syntaxCompatibility {
			t.Errorf("%s has invalid syntax status %q", rel, contract.Status)
		}
		if contract.Spec == "" {
			t.Errorf("%s has no specification anchor", rel)
		}
		if contract.Status == syntaxCompatibility && contract.CompatibilityNote == "" {
			t.Errorf("compatibility syntax %s lacks an explicit migration note", rel)
		}
		if !syntaxExitCase.MatchString(rel) && contract.NoNativeReason == "" {
			t.Errorf("non-native syntax case %s must explain why it stops before native execution", rel)
		}
		if len(owned[rel]) == 0 {
			t.Errorf("syntax contract %s belongs to no family", rel)
		}
		if _, err := os.Stat(filepath.Join(root, filepath.FromSlash(rel))); err != nil {
			t.Errorf("syntax contract %s points at missing source: %v", rel, err)
		}
	}

	seen := 0
	err := filepath.WalkDir(root, func(path string, entry fs.DirEntry, walkErr error) error {
		if walkErr != nil {
			return walkErr
		}
		if entry.IsDir() || !strings.HasSuffix(entry.Name(), ".oak") {
			return nil
		}
		rel, err := filepath.Rel(root, path)
		if err != nil {
			return err
		}
		rel = filepath.ToSlash(rel)
		seen++
		if _, ok := syntaxContracts[rel]; !ok {
			t.Errorf("accepted syntax case %s has no canonical/compatibility contract", rel)
		}
		if len(owned[rel]) == 0 {
			t.Errorf("accepted syntax case %s belongs to no syntax family", rel)
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	if seen == 0 {
		t.Fatal("syntax corpus is empty")
	}

	families := make([]string, 0, len(syntaxFamilies))
	for family := range syntaxFamilies {
		families = append(families, family)
	}
	sort.Strings(families)
	for _, family := range families {
		for _, rel := range syntaxFamilies[family] {
			if _, ok := syntaxContracts[rel]; !ok {
				t.Errorf("family %q references uncontracted case %s", family, rel)
			}
		}
	}
}
