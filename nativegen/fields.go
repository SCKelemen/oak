package nativegen

import (
	"sort"

	"github.com/SCKelemen/oak/ast"
)

// Record fields in registers (docs/spec/94-assembler.md §9 "Fields in
// registers"). A record local declared at the body's top level whose scalar
// fields a loop reads or writes keeps those fields in callee-saved
// registers, as hidden locals named `record.field`: a field read is the
// register, a field store writes it, and the record's memory sees the
// values only where the record is used whole — copied, passed to a callee
// by address, returned, or read through any other path — when the homes
// are written back first (flush); a whole write of the record — an
// assignment from another record, an initialization by copy, literal,
// call, or zero — reloads the homes from memory afterward. Between, the
// register and the field's memory may differ, and every read of the field
// goes to the register (Oak.FieldPromotion.promoted_reads). Fields whose
// address is taken (`&r.f`, `&r`) stay in memory, as do fields of records
// declared more than once (a shadowing declaration) or inside a loop.

// promotedField is a field kept in a register: its hidden local's name.
type promotedField struct {
	hidden string
	typ    scalar
	offset int64
}

// promotedRecord is a record local with fields in registers.
type promotedRecord struct {
	rec    *recordLocal
	fields map[string]*promotedField
	order  []string
}

// promotableFields finds, per top-level record local, the scalar fields a
// loop touches, most-touched first, with the exclusions above.
func (g *generator) promotableFields(fn *ast.FunctionStatement) map[string][]string {
	if g.rvLane {
		return nil
	}
	block, isBlock := fn.Body.(*ast.BlockExpression)
	if !isBlock || block.Block == nil {
		return nil
	}
	layouts := map[string]*recordLayout{}
	for _, stmt := range block.Block.Statements {
		decl, isDecl := stmt.(*ast.VariableDeclaration)
		if !isDecl || decl.Name == nil || decl.Type == nil {
			continue
		}
		name, isRecord := g.recordTypeName(decl.Type)
		if !isRecord {
			continue
		}
		if layout, err := g.layoutOf(name); err == nil && !layout.isADT() {
			layouts[decl.Name.Value] = layout
		}
	}
	if len(layouts) == 0 {
		return nil
	}
	for _, p := range fn.Parameters {
		if p.Name != nil {
			delete(layouts, p.Name.Value)
		}
	}
	declared := map[string]int{}
	counts := map[string]map[string]int{}
	excluded := map[string]map[string]bool{}
	exclude := func(record, field string) {
		if excluded[record] == nil {
			excluded[record] = map[string]bool{}
		}
		excluded[record][field] = true
	}
	var loops []*ast.WhileStatement
	walk(fn.Body, func(n ast.Node) {
		switch e := n.(type) {
		case *ast.WhileStatement:
			loops = append(loops, e)
		case *ast.VariableDeclaration:
			if e.Name != nil {
				declared[e.Name.Value]++
			}
		case *ast.PrefixExpression:
			if e.Operator == "&" {
				switch target := e.Right.(type) {
				case *ast.Identifier:
					exclude(target.Value, "")
				case *ast.IndexExpression:
					if ident, isIdent := target.Left.(*ast.Identifier); isIdent && target.Dot {
						if field, isField := target.Index.(*ast.Identifier); isField {
							exclude(ident.Value, field.Value)
						}
					} else if root, has := pathRoot(target); has {
						// A path deeper than one field: the whole record's
						// address may be derived from it.
						exclude(root, "")
					}
				}
			}
		}
	})
	for _, loop := range loops {
		count := func(n ast.Node) {
			switch e := n.(type) {
			case *ast.VariableDeclaration:
				if e.Name != nil {
					declared[e.Name.Value]++ // a record declared inside a loop is not promoted
				}
			case *ast.IndexExpression:
				if e.Dot {
					if ident, isIdent := e.Left.(*ast.Identifier); isIdent {
						if field, isField := e.Index.(*ast.Identifier); isField {
							if counts[ident.Value] == nil {
								counts[ident.Value] = map[string]int{}
							}
							counts[ident.Value][field.Value]++
						}
					}
				}
			}
		}
		walk(loop.Condition, count)
		walk(loop.Body, count)
	}
	out := map[string][]string{}
	for record, layout := range layouts {
		if declared[record] != 1 || excluded[record][""] {
			continue
		}
		var fields []string
		for field, n := range counts[record] {
			f, has := layout.fields[field]
			if !has || f.kind != fieldScalar || f.atomic || f.typ.isFloat || f.typ.isVec || (f.typ.bits < 32 && !f.typ.isBool) || excluded[record][field] || n == 0 {
				continue
			}
			fields = append(fields, field)
		}
		sort.Slice(fields, func(i, j int) bool {
			if counts[record][fields[i]] != counts[record][fields[j]] {
				return counts[record][fields[i]] > counts[record][fields[j]]
			}
			return fields[i] < fields[j]
		})
		if len(fields) > 0 {
			out[record] = fields
		}
	}
	return out
}

// promoteFields gives a newly bound record local its register-resident
// fields, while callee-saved registers remain (a home that is not
// callee-saved would not survive the loop's calls). The homes hold
// nothing yet: the declaration's initializer reloads them.
func (g *generator) promoteFields(name string, rec *recordLocal) {
	fields, wanted := g.promotable[name]
	if !wanted || rec == nil || rec.readOnly {
		return
	}
	pr := &promotedRecord{rec: rec, fields: map[string]*promotedField{}}
	for _, field := range fields {
		f := rec.layout.fields[field]
		home, ok := g.takeCalleeRegister()
		if !ok {
			break
		}
		hidden := name + "." + field
		g.declareAt(hidden, f.typ, home)
		pr.fields[field] = &promotedField{hidden: hidden, typ: f.typ, offset: f.offset}
		pr.order = append(pr.order, field)
	}
	if len(pr.order) == 0 {
		return
	}
	if g.promoted == nil {
		g.promoted = map[string]*promotedRecord{}
	}
	g.promoted[name] = pr
	g.promotedCount += len(pr.order)
}

// promotedFieldOf reads `r.f` as a promoted field: the hidden local's
// name and type.
func (g *generator) promotedFieldOf(e *ast.IndexExpression) (string, scalar, bool) {
	if e == nil || !e.Dot {
		return "", scalar{}, false
	}
	ident, isIdent := e.Left.(*ast.Identifier)
	if !isIdent {
		return "", scalar{}, false
	}
	pr, isPromoted := g.promoted[ident.Value]
	if !isPromoted || g.records[ident.Value] != pr.rec {
		return "", scalar{}, false
	}
	field, isField := e.Index.(*ast.Identifier)
	if !isField {
		return "", scalar{}, false
	}
	pf, has := pr.fields[field.Value]
	if !has {
		return "", scalar{}, false
	}
	return pf.hidden, pf.typ, true
}

// flushPromoted writes a record's register-resident fields back to its
// memory: before the record is used whole.
func (g *generator) flushPromoted(name string) error {
	pr, isPromoted := g.promoted[name]
	if !isPromoted || g.records[name] != pr.rec {
		return nil
	}
	for _, field := range pr.order {
		pf := pr.fields[field]
		home := g.regs[pf.hidden]
		if home < 0 {
			continue
		}
		at := pr.rec.loc().plus(pf.offset)
		if err := g.fieldStore(&scalarPlace{offset: at.offset, typ: pf.typ, inReg: at.inReg, reg: at.reg}, home); err != nil {
			return err
		}
	}
	return nil
}

// reloadPromoted reads a record's register-resident fields from its
// memory: after the record was written whole.
func (g *generator) reloadPromoted(name string) error {
	pr, isPromoted := g.promoted[name]
	if !isPromoted || g.records[name] != pr.rec {
		return nil
	}
	for _, field := range pr.order {
		pf := pr.fields[field]
		home := g.regs[pf.hidden]
		if home < 0 {
			continue
		}
		at := pr.rec.loc().plus(pf.offset)
		r, err := g.fieldLoad(&scalarPlace{offset: at.offset, typ: pf.typ, inReg: at.inReg, reg: at.reg})
		if err != nil {
			return err
		}
		g.assignVar(pf.hidden, r)
		g.killLoopFacts(pf.hidden)
	}
	return nil
}

// takeCalleeRegister claims the next callee-saved register for a home, or
// reports none: the free list first, then the unclaimed ones (the save
// area then covers them), never a caller-saved register.
func (g *generator) takeCalleeRegister() (int, bool) {
	// Scalar last-use/scope release also recycles caller homes here. A
	// synthetic persistent home must not inherit their call-clobber class.
	for i := len(g.freeCallee) - 1; i >= 0; i-- {
		r := g.freeCallee[i]
		if r < calleeLow || r > calleeHigh {
			continue
		}
		copy(g.freeCallee[i:], g.freeCallee[i+1:])
		g.freeCallee = g.freeCallee[:len(g.freeCallee)-1]
		return r, true
	}
	if g.usedCallee+fieldHomeReserve >= calleeHigh-calleeLow+1 {
		// The loop-invariant pass's reserve yields to a field a loop
		// touches: a home saves a load and a store per iteration where a
		// hoisted invariant saves one instruction (§9 "The register
		// budget"; the reserve was claimed before the body lowered).
		return g.reclaimReserve()
	}
	if g.saveArea == 0 {
		if g.nslots != 0 {
			return 0, false
		}
		g.saveArea = 8 * (calleeHigh - calleeLow + 1)
	}
	r := calleeLow + g.usedCallee
	g.usedCallee++
	return r, true
}

// fieldHomeReserve is the number of callee-saved registers left unclaimed
// by field homes, for the locals and spans declared after the record.
const fieldHomeReserve = 2
