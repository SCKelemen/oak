package asm

import (
	"crypto/sha256"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// This is a repository-maintained ownership boundary, not protection against
// malicious package code, unsafe, reflection, or a compromised runtime. Trusted
// projection bodies and every graph-reading helper are pinned below: changing
// a transitive helper requires renewed mutation/alias review, not just an edit
// to the allowlist. Standard formatting, sorting of local copies, and local
// writer methods do not receive a graph reference.
func TestCheckedTypedCNFSourceInventory(t *testing.T) {
	trusted := map[string]string{
		"cnf_typed_replay.go:checkTypedCNFImplication":                   "d58be22721dc62902666227f25384ef58b2dce2a95c0eb86778a681bb648e66e",
		"cnf_checked_snapshot.go:typedCNFAudit.stats":                    "4ff934c930be7505e7cc68abe06dedbee45dd09dec0cdef15ec3c7fba0602b70",
		"cnf_checked_snapshot.go:typedCNFAudit.writeDIMACS":              "6ea03eee5d7e3895cc78e666fcfa86a42615865d08d3188824a0b8c92abe75b8",
		"cnf_checked_projection_test.go:typedCNFAudit.checkValues":       "2e26f0ae471dac33d827e047921d423cbe01ca5679c5102c7cc3cfd040cc6322",
		"cnf_typed_instance_test.go:typedCNFAudit.emitInstance":          "6cedc2d6189acb833aa3516322e9ddb21b10faf22d7432067d6900bc53976218",
		"cnf_typed_instance_test.go:typedInstanceRoots":                  "1464de514f6a0be65b80b7714df5f53f0a7de6d0a2ea4244f5f3a392491ed224",
		"cnf_checked_snapshot_test.go:typedCNFAudit.testIdentity":        "3c77af7aa1853bb45ef0838d3c823ffa9404a02270f3e7fc7e6df068a650c787",
		"cnf_checked_snapshot_test.go:TestCheckedTypedCNFZeroAndPartial": "8fc6299ab075b0528f2c3604de62ec44992735cc2985a15e71addc60b15413eb",
		"cnf_typed_replay_test.go:typedCNFValue":                         "fdc784adab28a97a94fb7519aea74575ba73417dad2618a410de63767a99f1d4",
		"verify.go:mask":                                                 "3cbb8dc649906e491a2f071b3506815c6021abf94ed161e9a67df21294a621dc",
		"verify.go:term.declaredWidth":                                   "37b7d78a58f5b4a0a63d86e94de205227c850b6b24551786a835ab11efc1bbf0",
		"native_bitwise_certificate.go:replayAdapt":                      "ee3d26752d9daf9f4f0b95c8426511e3d2f5a37227da8e919b70feff01674539",
		"cnf_allocation_refinement_test.go:renderCNFAllocationSnapshot":  "ed6e576c74a34f9170cf436f84d58c156bfbae2d47f5e59b9bef716edc6046a0",
		"cnf_trace_refinement_test.go:renderCNFTraceClauses":             "7019baeead52db69df81718dd7aec96b4d3a065ac2e15fd0aa151684e5e8f977",
	}
	seen := map[string]bool{}
	paths, err := filepath.Glob("*.go")
	if err != nil {
		t.Fatal(err)
	}
	for _, path := range paths {
		source, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		set := token.NewFileSet()
		file, err := parser.ParseFile(set, path, source, 0)
		if err != nil {
			t.Fatal(err)
		}
		for _, decl := range file.Decls {
			fn, isFunc := decl.(*ast.FuncDecl)
			key := ""
			if isFunc {
				key = path + ":" + fn.Name.Name
				if fn.Recv != nil {
					receiver := fn.Recv.List[0].Type
					if ptr, ok := receiver.(*ast.StarExpr); ok {
						receiver = ptr.X
					}
					key = path + ":" + receiver.(*ast.Ident).Name + "." + fn.Name.Name
				}
			}
			if want, ok := trusted[key]; ok {
				got := fmt.Sprintf("%x", sha256.Sum256(source[set.Position(fn.Pos()).Offset:set.Position(fn.End()).Offset]))
				if got != want {
					t.Errorf("renew graph mutation/alias review for %s: %s", key, got)
				}
				seen[key] = true
				continue
			}
			// Only the two storage declarations may name owned storage outside
			// the exact trusted function bodies; aliases cannot widen access.
			if gen, ok := decl.(*ast.GenDecl); ok && path == "cnf_typed_replay.go" && gen.Tok == token.TYPE && len(gen.Specs) == 1 {
				name := gen.Specs[0].(*ast.TypeSpec).Name.Name
				if name == "typedCNFAudit" || name == "checkedTypedCNFSnapshot" {
					continue
				}
			}
			ast.Inspect(decl, func(node ast.Node) bool {
				switch n := node.(type) {
				case *ast.Ident:
					if n.Name == "checkedTypedCNFSnapshot" {
						t.Errorf("unreviewed owned storage reference in %s at %s", path, set.Position(n.Pos()))
					}
				case *ast.SelectorExpr:
					if n.Sel.Name == "checked" {
						t.Errorf("raw owner access in %s at %s", path, set.Position(n.Pos()))
					}
				case *ast.CompositeLit:
					if name, ok := n.Type.(*ast.Ident); ok && name.Name == "typedCNFAudit" && len(n.Elts) != 0 {
						t.Errorf("audit minted outside constructor in %s", path)
					}
				case *ast.TypeSpec:
					if name, ok := n.Type.(*ast.Ident); ok && (name.Name == "typedCNFAudit" || name.Name == "checkedTypedCNFSnapshot") {
						t.Errorf("owner type alias in %s", path)
					}
				}
				return true
			})
		}
	}
	for key := range trusted {
		if !seen[key] {
			t.Errorf("missing reviewed graph consumer %s", key)
		}
	}
	if !strings.HasSuffix(checkedTypedCNFLabel, "diagnostic only") {
		t.Fatal("audit-only label")
	}
}
