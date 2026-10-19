package typechecker

import (
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// Keep these bounded examples tied to their authoritative Markdown, rather
// than copying their source into fixtures that can drift independently.
func syntaxSpecText(t *testing.T, name string) string {
	t.Helper()
	data, err := os.ReadFile(filepath.Join("..", "docs", "spec", name))
	if err != nil {
		t.Fatal(err)
	}
	return string(data)
}

func syntaxSpecBlock(t *testing.T, name, contains string) string {
	t.Helper()
	fences := regexp.MustCompile("(?ms)^[ \\t]*```oak\\n(.*?)^[ \\t]*```[ \\t]*$")
	var matches []string
	for _, block := range fences.FindAllStringSubmatch(syntaxSpecText(t, name), -1) {
		if strings.Contains(block[1], contains) {
			matches = append(matches, block[1])
		}
	}
	if len(matches) != 1 {
		t.Fatalf("%s: want one Oak block containing %q, found %d", name, contains, len(matches))
	}
	return matches[0]
}

func parseSyntaxSpec(t *testing.T, source string) *ast.Program {
	t.Helper()
	p := parser.New(scanner.New(source))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("documented source rejected by parser: %v\n%s", errs, source)
	}
	return program
}

func checkSyntaxSpec(t *testing.T, source string) {
	t.Helper()
	tc := setupTypeChecker(source)
	tc.CheckProgram(parseSyntaxSpec(t, source))
	if errs := tc.Errors(); len(errs) != 0 {
		t.Fatalf("documented source rejected by typechecker: %v\n%s", errs, source)
	}
}

func TestAuthoritativeSyntaxKernelExamples(t *testing.T) {
	for _, example := range []struct {
		name    string
		kernels []string
		check   bool
	}{
		{"clamp_relu:", []string{"relu", "axpy"}, true},
		{"reverse_blocks:", []string{"reverse_blocks"}, true},
		{"scale_shift:", []string{"scale", "shift", "scale_shift"}, true},
		{"store_row:", []string{"store_row"}, true},
		// The tensor example depends on imported library declarations. Check
		// its complete syntax here without pretending to check those imports.
		{"matmul[A, B, C]:", []string{"matmul"}, false},
	} {
		t.Run(example.kernels[0], func(t *testing.T) {
			source := syntaxSpecBlock(t, "56-kernels.md", example.name)
			program := parseSyntaxSpec(t, source)
			found := map[string]bool{}
			for _, stmt := range program.Statements {
				if fn, ok := stmt.(*ast.FunctionStatement); ok && fn.Kernel {
					found[fn.Name.Value] = true
				}
			}
			if len(found) != len(example.kernels) {
				t.Fatalf("kernel markers changed: got %v, want %v", found, example.kernels)
			}
			for _, name := range example.kernels {
				if !found[name] {
					t.Fatalf("%s lost its kernel marker", name)
				}
			}
			if example.check {
				checkSyntaxSpec(t, source)
			}

			// A regression to the previous prefix is a migration error, not
			// a second accepted spelling. Mutate an actual documented example.
			head := regexp.MustCompile(`(?m)^([ \t]*)` + regexp.QuoteMeta(example.kernels[0]) + `([:\[])`)
			legacy := head.ReplaceAllString(source, "${1}kernel "+example.kernels[0]+"${2}")
			legacy = strings.Replace(legacy, " (kernel)", "", 1)
			p := parser.New(scanner.New(legacy))
			p.ParseProgram()
			if !strings.Contains(strings.Join(p.Errors(), "\n"), "move kernel after the signature") {
				t.Fatalf("prefix kernel did not report its migration diagnostic: %v", p.Errors())
			}
		})
	}
}

func TestAuthoritativeSyntaxStatusKernel(t *testing.T) {
	text := syntaxSpecText(t, "STATUS.md")
	var examples []string
	for _, inline := range strings.Split(text, "`") {
		if strings.HasPrefix(inline, "name: (gid:") {
			examples = append(examples, inline)
		}
	}
	if len(examples) != 1 {
		t.Fatalf("want one status kernel example, found %d", len(examples))
	}
	program := parseSyntaxSpec(t, examples[0])
	fn, ok := program.Statements[0].(*ast.FunctionStatement)
	if !ok || !fn.Kernel {
		t.Fatal("status example lost its kernel marker")
	}
	checkSyntaxSpec(t, examples[0])
}

func TestAuthoritativeSyntaxDeclarationExamples(t *testing.T) {
	for _, example := range []string{"zeroed:", "identity[T]:", "length2[T: XY]:"} {
		t.Run(example, func(t *testing.T) {
			checkSyntaxSpec(t, syntaxSpecBlock(t, "10-syntax.md", example))
		})
	}

	t.Run("generic compatibility alias", func(t *testing.T) {
		text := syntaxSpecText(t, "10-syntax.md")
		for _, inline := range strings.Split(text, "`") {
			if strings.HasPrefix(inline, "fn [T] identity(") {
				checkSyntaxSpec(t, inline+"\nresult: u32 = identity[u32](7)")
				return
			}
		}
		t.Fatal("missing documented generic compatibility alias")
	})

	t.Run("variadic signature", func(t *testing.T) {
		// This block is explicitly a signature, not a complete definition.
		parseSyntaxSpec(t, syntaxSpecBlock(t, "10-syntax.md", "total: (base:"))
	})

	t.Run("explicit constrained call is unsupported", func(t *testing.T) {
		source := syntaxSpecBlock(t, "10-syntax.md", "length2[T: XY]:")
		source = strings.Replace(source, "tag_of(p)", "tag_of[Point](p)", 1)
		tc := setupTypeChecker(source)
		tc.CheckProgram(parseSyntaxSpec(t, source))
		if len(tc.Errors()) == 0 {
			t.Fatal("explicit constrained calls are now accepted; update the documented limitation")
		}
	})

	t.Run("shape contract at declaration", func(t *testing.T) {
		source := syntaxSpecBlock(t, "10-syntax.md", "length2[T: XY]:")
		// Remove the concrete declarations and calls: the contract must be
		// enforced even when no call instantiates the function.
		source = strings.Split(source, "Point: type")[0]
		bad := strings.Replace(source, "value.x * value.x", "value.z * value.z", 1)
		tc := setupTypeChecker(bad)
		tc.CheckProgram(parseSyntaxSpec(t, bad))
		if !strings.Contains(strings.Join(tc.Errors(), "\n"), "not guaranteed by constraints") {
			t.Fatalf("missing declaration-time shape constraint error: %v", tc.Errors())
		}
	})
}
