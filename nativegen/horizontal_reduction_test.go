package nativegen

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

const horizontalFreeSource = `reduce: (v: simd.U32x4, seed: u32): u32 {
  acc: u32 = seed
  lanes: [4]u32 = [4]u32{0, 0, 0, 0}
  simd.store_u32x4(span(&lanes), u32(0), v)
  acc = acc + ((lanes[0] + lanes[1]) + (lanes[2] + lanes[3]))
  acc
}`

func horizontalTestSource(typ string) string {
	if typ == "u64" {
		return strings.NewReplacer("U32x4", "U64x2", "store_u32x4", "store_u64x2",
			"u32", "u64", "[4]", "[2]", "{0, 0, 0, 0}", "{0, 0}",
			"((lanes[0] + lanes[1]) + (lanes[2] + lanes[3]))", "(lanes[0] + lanes[1])").Replace(
			strings.Replace(horizontalFreeSource, "u32(0)", "0", 1))
	}
	return horizontalFreeSource
}

func markHorizontalTestBody(fn *ast.FunctionStatement) []ast.Statement {
	stmts := fn.Body.(*ast.BlockExpression).Block.Statements
	decl := stmts[1].(*ast.VariableDeclaration)
	decl.Token = markHorizontalReduction(decl.Token)
	return stmts[1:]
}

func TestHorizontalReductionFreeInputs(t *testing.T) {
	for _, typ := range []string{"u32", "u64"} {
		t.Run(typ, func(t *testing.T) {
			source, shape, mnemonic, lane, class := horizontalTestSource(typ), "u32x4", "addv", "s", asm.ClassW
			if typ == "u64" {
				shape, mnemonic, lane, class = "u64x2", "addp", "d", asm.ClassX
			}
			for _, suffix := range []string{"acc", "acc + (simd.any_" + shape + "(v) ? " + typ + "(1) | " + typ + "(0))"} {
				t.Run(suffix, func(t *testing.T) {
					original, functions, _, tc := checkedFillFunction(t, strings.Replace(source, "\n  acc\n}", "\n  "+suffix+"\n}", 1), "reduce")
					before := cloneNode(original)
					fn := cloneNode(original).(*ast.FunctionStatement)
					markHorizontalTestBody(fn)
					// Materialization clones the metadata and ordinary source shape.
					fn = cloneNode(fn).(*ast.FunctionStatement)
					functions["reduce"] = fn
					body, err := CompileFor(Lane{Arch: asm.ArchArm64, NoReductions: true}, fn, functions, nil, nil, nil, tc)
					if err != nil {
						t.Fatal(err)
					}
					text := Describe(body)
					if strings.Count(text, mnemonic+" ") != 1 || !strings.Contains(text, "umov ") || strings.Contains(text, "str q") {
						t.Fatalf("missing in-register combine:\n%s", text)
					}
					if findings := asm.Check(body, original, map[string]bool{body.Name: true}); len(findings) != 0 {
						t.Fatalf("checker: %v\n%s", findings, text)
					}
					if _, _, err := asm.EncodeFunction(body); err != nil {
						t.Fatalf("encoding: %v\n%s", err, text)
					}
					if verdict := asm.Verify(body, original, original.Body); verdict.Kind != asm.VerdictProven {
						t.Fatalf("free vector and seed: %s: %s\n%s", verdict.Kind, verdict.Message, text)
					}
					if !reflect.DeepEqual(original, before) {
						t.Fatal("original verifier input mutated")
					}
					for _, mutation := range []string{"wrong_lane", "drop_seed", "source_clobber"} {
						if mutation == "source_clobber" && suffix == "acc" {
							continue // the second fixture observes all source lanes after the combine
						}
						mutant := *body
						mutant.Items = append([]asm.Item(nil), body.Items...)
						changed := false
						for i, item := range mutant.Items {
							ins, ok := item.(asm.Instruction)
							if !ok {
								continue
							}
							ins.Operands = append([]asm.Operand(nil), ins.Operands...)
							switch {
							case mutation == "wrong_lane" && ins.Mnemonic == "umov":
								src := ins.Operands[1].(asm.Register)
								ins.Operands[1] = laneReg(src.Num, lane, 1)
							case mutation == "drop_seed" && ins.Mnemonic == "add" && len(ins.Operands) == 3:
								if dst, ok := ins.Operands[0].(asm.Register); !ok || dst.Class != class {
									continue
								}
								ins.Operands[1] = reg(31, scalars[typ])
							case mutation == "source_clobber" && ins.Mnemonic == mnemonic:
								source := ins.Operands[1].(asm.Register)
								// An extra write corrupts the live source, while the correct
								// reduction destination/result remain unchanged.
								zero := asm.Instruction{Mnemonic: "movi", Operands: []asm.Operand{vreg(source.Num, "16b"), imm(0)}}
								mutant.Items = append(mutant.Items[:i+1], append([]asm.Item{zero}, mutant.Items[i+1:]...)...)
								changed = true
								continue
							default:
								continue
							}
							mutant.Items[i], changed = ins, true
							break
						}
						if !changed {
							t.Fatalf("mutation %s did not fire", mutation)
						}
						if verdict := asm.Verify(&mutant, original, original.Body); verdict.Kind != asm.VerdictMismatch {
							t.Fatalf("%s: want mismatch, got %s: %s\n%s", mutation, verdict.Kind, verdict.Message, Describe(&mutant))
						}
					}
					originalTree := "((lanes[0] + lanes[1]) + (lanes[2] + lanes[3]))"
					trees := []string{"((lanes[0] + lanes[1]) + (lanes[2] + lanes[2]))", "((lanes[0] + lanes[1]) + lanes[2])", "(((lanes[0] + lanes[1]) + (lanes[2] + lanes[3])) + lanes[3])"}
					if typ == "u64" {
						originalTree, trees = "(lanes[0] + lanes[1])", []string{"(lanes[0] + lanes[0])", "lanes[0]", "((lanes[0] + lanes[1]) + lanes[1])"}
					}
					for _, tree := range trees {
						wrong, _, _, _ := checkedFillFunction(t, strings.Replace(source, originalTree, tree, 1), "reduce")
						// Use the plain-result fixture so the only disagreement is the lane multiset.
						if suffix == "acc" {
							if verdict := asm.Verify(body, wrong, wrong.Body); verdict.Kind != asm.VerdictMismatch {
								t.Fatalf("wrong source lane tree: %s: %s", verdict.Kind, verdict.Message)
							}
						}
					}
				})
			}
		})
	}
}

func TestHorizontalReductionRefusesNearMisses(t *testing.T) {
	for _, typ := range []string{"u32", "u64"} {
		t.Run(typ, func(t *testing.T) {
			shape, last := vecShapes["U32x4"], int64(3)
			if typ == "u64" {
				shape, last = vecShapes["U64x2"], 1
			}
			for name, mutate := range map[string]func(*generator, []ast.Statement){
				"rv64":                func(g *generator, _ []ast.Statement) { g.rvLane = true },
				"missing_marker":      func(_ *generator, s []ast.Statement) { s[0].(*ast.VariableDeclaration).Token = token.Token{} },
				"forged_context_only": func(_ *generator, s []ast.Statement) { s[0].(*ast.VariableDeclaration).Token.TokenKind = token.IDENT },
				"wrong_context": func(_ *generator, s []ast.Statement) {
					s[0].(*ast.VariableDeclaration).Token.SemanticContext += ".similar"
				},
				"not_synthetic": func(_ *generator, s []ast.Statement) { s[0].(*ast.VariableDeclaration).Token.Synthetic = false },
				"nonzero_initializer": func(_ *generator, s []ast.Statement) {
					s[0].(*ast.VariableDeclaration).Value.(*ast.ArrayLiteral).Elements[0].(*ast.IntegerLiteral).Value = 1
				},
				"mismatched_array_width": func(_ *generator, s []ast.Statement) {
					s[0].(*ast.VariableDeclaration).Type.(*ast.IndexExpression).Left.(*ast.Identifier).Value = "u16"
				},
				"float_source":       func(g *generator, _ []ast.Statement) { g.types["v"] = vecShapes["F32x4"] },
				"signed_accumulator": func(g *generator, _ []ast.Statement) { g.types["acc"] = scalars["i32"] },
				"store_offset": func(_ *generator, s []ast.Statement) {
					s[1].(*ast.ExpressionStatement).Expression.(*ast.InvocationExpression).Arguments[1] = &ast.IntegerLiteral{Value: 1}
				},
				"other_operator": func(_ *generator, s []ast.Statement) {
					s[2].(*ast.AssignmentStatement).Value.(*ast.InfixExpression).Right.(*ast.InfixExpression).Operator = "-"
				},
				"duplicate_lane": func(_ *generator, s []ast.Statement) {
					walk(s[2], func(n ast.Node) {
						if index, ok := n.(*ast.IndexExpression); ok && !index.Dot {
							if k, ok := index.Index.(*ast.IntegerLiteral); ok && k.Value == last {
								k.Value = last - 1
							}
						}
					})
				},
				"suffix_read": func(g *generator, _ []ast.Statement) {
					g.fn.Body.(*ast.BlockExpression).Block.Statements = append(g.fn.Body.(*ast.BlockExpression).Block.Statements, &ast.ExpressionStatement{Expression: &ast.Identifier{Value: "lanes"}})
				},
				"shared_pointer_escape": func(g *generator, s []ast.Statement) {
					borrow := s[1].(*ast.ExpressionStatement).Expression.(*ast.InvocationExpression).Arguments[0]
					g.fn.Body.(*ast.BlockExpression).Block.Statements = append(g.fn.Body.(*ast.BlockExpression).Block.Statements, &ast.ExpressionStatement{Expression: borrow})
				},
				"nested_escape": func(g *generator, _ []ast.Statement) {
					g.fn.Body.(*ast.BlockExpression).Block.Statements = append(g.fn.Body.(*ast.BlockExpression).Block.Statements, &ast.BlockStatement{Statements: []ast.Statement{&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "lanes"}}}})
				},
				"extra_assignment_target": func(g *generator, _ []ast.Statement) {
					g.fn.Body.(*ast.BlockExpression).Block.Statements = append(g.fn.Body.(*ast.BlockExpression).Block.Statements, &ast.AssignmentStatement{Name: &ast.Identifier{Value: "lanes"}, Value: &ast.IntegerLiteral{Value: 0}})
				},
				"extra_declaration": func(g *generator, _ []ast.Statement) {
					g.fn.Body.(*ast.BlockExpression).Block.Statements = append(g.fn.Body.(*ast.BlockExpression).Block.Statements, &ast.VariableDeclaration{Name: &ast.Identifier{Value: "lanes"}, Value: &ast.IntegerLiteral{Value: 0}})
				},
				"parameter_collision": func(g *generator, _ []ast.Statement) { g.fn.Parameters[1].Name.Value = "lanes" },
				"detached_group":      func(g *generator, _ []ast.Statement) { g.fn = cloneNode(g.fn).(*ast.FunctionStatement) },
			} {
				t.Run(name, func(t *testing.T) {
					fn, _, _, _ := checkedFillFunction(t, horizontalTestSource(typ), "reduce")
					stmts := markHorizontalTestBody(fn)
					g := generator{fn: fn, types: map[string]scalar{"v": shape, "acc": scalars[typ]}}
					if _, ok := g.horizontalReduction(stmts); !ok {
						t.Fatal("baseline not recognized")
					}
					mutate(&g, stmts)
					if _, ok := g.horizontalReduction(stmts); ok {
						t.Fatal("unsafe near miss recognized")
					}
				})
			}
		})
	}
}

func TestHorizontalReductionScratchExhaustion(t *testing.T) {
	for _, typ := range []string{"u32", "u64"} {
		t.Run(typ, func(t *testing.T) {
			shape := vecShapes["U32x4"]
			if typ == "u64" {
				shape = vecShapes["U64x2"]
			}
			for _, where := range []string{"vector_result", "scalar_result", "seed"} {
				t.Run(where, func(t *testing.T) {
					g := generator{
						types: map[string]scalar{"v": shape, "acc": scalars[typ]},
						regs:  map[string]int{"v": vecBase + 8, "acc": 2},
						free:  []int{9}, freeF: []int{vecBase + 16},
						usedCallee: calleeHigh - calleeLow + 1, ipScratch: 2,
					}
					switch where {
					case "vector_result":
						g.freeF = nil
					case "scalar_result":
						g.free = nil
					case "seed":
						g.regs["acc"] = -1
						g.slots = map[string]int64{"acc": 0}
					}
					free, vectors := append([]int(nil), g.free...), append([]int(nil), g.freeF...)
					err := g.lowerHorizontalReduction(horizontalCombine{vector: &ast.Identifier{Value: "v"}, acc: &ast.Identifier{Value: "acc"}, elem: scalars[typ]})
					if _, unsupported := err.(Unsupported); !unsupported {
						t.Fatalf("want clean refusal, got %v", err)
					}
					if len(g.live) != 0 || !reflect.DeepEqual(g.free, free) || !reflect.DeepEqual(g.freeF, vectors) || len(g.items) != 0 {
						t.Fatalf("scratch/error side effects: live=%v, free=%v, vectors=%v, items=%v", g.live, g.free, g.freeF, g.items)
					}
				})
			}
		})
	}
}

func TestHorizontalReductionGeneratedLoop(t *testing.T) {
	for _, typ := range []string{"u32", "u64", "i32", "f32"} {
		source := `sum: (v: []` + typ + `): ` + typ + ` {
  acc: ` + typ + ` = 0
  i: u32 = 0
  while i < len(v) { acc = acc + v[i]; i = i + u32(1) }
  acc
}`
		if typ == "f32" {
			source = strings.Replace(source, "= 0\n", "= 0.0\n", 1)
		}
		fn, functions, _, tc := checkedFillFunction(t, source, "sum")
		before := cloneNode(fn)
		body, err := CompileFor(Lane{Arch: asm.ArchArm64, VectorReductions: true, VectorHomes: true}, fn, functions, nil, nil, nil, tc)
		if err != nil {
			t.Fatalf("%s: %v", typ, err)
		}
		text := Describe(body)
		if strings.Contains(text, "addv ") != (typ == "u32") {
			t.Fatalf("%s: unexpected horizontal shape:\n%s", typ, text)
		}
		if strings.Contains(text, "addp ") != (typ == "u64") {
			t.Fatalf("%s: unexpected pairwise shape:\n%s", typ, text)
		}
		if (typ == "u32" || typ == "u64") && strings.Contains(text, "str q") {
			t.Fatalf("scratch vector store remains:\n%s", text)
		}
		if findings := asm.Check(body, fn, map[string]bool{body.Name: true}); len(findings) != 0 {
			t.Fatalf("%s checker: %v\n%s", typ, findings, text)
		}
		reference := body.Body
		if reference == nil {
			reference = fn.Body
		}
		if verdict := asm.Verify(body, fn, reference); verdict.Kind != asm.VerdictProven {
			t.Fatalf("%s proof: %s: %s\n%s", typ, verdict.Kind, verdict.Message, text)
		}
		if !reflect.DeepEqual(fn, before) {
			t.Fatal("source body mutated")
		}
		suffix := "u32x4"
		if typ == "u64" {
			suffix = "u64x2"
		}
		if (typ == "u32" || typ == "u64") && (!strings.Contains(reference.String(), "simd.store_"+suffix) || !strings.Contains(reference.String(), "acc_vl")) {
			t.Fatal("proof reference lost original scratch-array semantics")
		}
	}
}
