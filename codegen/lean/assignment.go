package lean

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
)

// assignment builds the value that replaces an assignment's root owner.
// Descend through the checked field/element types, then rebuild each
// enclosing record and array from the leaf out. This handles paths such
// as views[id].shape[d] while retaining the existing getD/setIfInBounds
// totalization and leaving every sibling field and element unchanged.
func (em *emitter) assignment(target *ast.IndexExpression, value ast.Expression) (string, string, error) {
	var path []*ast.IndexExpression
	var base ast.Expression = target
	for {
		access, ok := base.(*ast.IndexExpression)
		if !ok {
			break
		}
		path = append(path, access)
		base = access.Left
	}
	root, ok := base.(*ast.Identifier)
	if !ok {
		return "", "", fmt.Errorf("assignment to %s is outside the extracted subset (a named owner is required)", target.String())
	}
	typ, known := em.scope.lookup(root.Value)
	if !known {
		return "", "", fmt.Errorf("assignment to unknown variable %s", root.Value)
	}
	type step struct{ parent, field, index string }
	var steps []step
	parent := ident(root.Value)
	for i := len(path) - 1; i >= 0; i-- {
		access := path[i]
		if access.Dot {
			field, named := access.Index.(*ast.Identifier)
			if !named {
				return "", "", fmt.Errorf("assignment to %s requires a named field", access.String())
			}
			fieldType, err := em.recordFieldType(typ, field.Value)
			if err != nil {
				return "", "", err
			}
			steps = append(steps, step{parent: parent, field: ident(field.Value)})
			parent, typ = parent+"."+ident(field.Value), fieldType
		} else {
			element, isArray := elementOf(typ)
			if !isArray {
				return "", "", fmt.Errorf("element assignment into non-array %s", access.Left.String())
			}
			// Render outer indices before inner ones and the stored value.
			// Calls are hoisted once; the writeback reuses their bound terms.
			index, err := em.indexTerm(access.Index)
			if err != nil {
				return "", "", err
			}
			steps = append(steps, step{parent: parent, index: index})
			parent, typ = fmt.Sprintf("(%s.getD %s %s)", parent, index, zeroOf(element)), element
		}
	}
	term, err := em.expr(value, typ)
	if err != nil {
		return "", "", err
	}
	for i := len(steps) - 1; i >= 0; i-- {
		s := steps[i]
		if s.field != "" {
			term = fmt.Sprintf("{ %s with %s := %s }", s.parent, s.field, term)
		} else {
			term = fmt.Sprintf("%s.setIfInBounds %s %s", s.parent, s.index, term)
		}
	}
	return root.Value, term, nil
}
