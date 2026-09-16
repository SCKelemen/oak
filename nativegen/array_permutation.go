package nativegen

import "github.com/SCKelemen/oak/ast"

// selfPermutation recognizes a whole-array assignment whose value is only a
// permutation of that same array. Aggregate-helper inlining wraps a one-line
// array result in a block, so that exact one-expression block is accepted too;
// any statement or less constrained expression keeps the ordinary value-copy
// lowering. The returned map says new[i] = old[source[i]].
func (g *generator) selfPermutation(name string, arr *arrayLocal, value ast.Expression) ([]int64, bool) {
	if arr == nil || arr.inReg || arr.readOnly || arr.paramRef || arr.elemLayout != nil || arr.elem.isVec || arr.elem.isBool {
		return nil, false
	}
	if block, isBlock := value.(*ast.BlockExpression); isBlock {
		if block.Block == nil || block.Block.Order != "" || len(block.Block.Statements) != 1 {
			return nil, false
		}
		tail, isExpression := block.Block.Statements[0].(*ast.ExpressionStatement)
		if !isExpression || tail.Discard {
			return nil, false
		}
		value = tail.Expression
	}
	literal, isLiteral := value.(*ast.ArrayLiteral)
	if !isLiteral || int64(len(literal.Elements)) != arr.length {
		return nil, false
	}
	if literal.Type != nil {
		layout, isArray := g.arrayLayoutOf(literal.Type)
		if !isArray || layout != g.arrayLayout(arr.elem, arr.length) {
			return nil, false
		}
	}
	source := make([]int64, arr.length)
	seen := make([]bool, arr.length)
	for destination, element := range literal.Elements {
		index, isIndex := element.(*ast.IndexExpression)
		if !isIndex || index.Dot {
			return nil, false
		}
		base, isIdentifier := index.Left.(*ast.Identifier)
		at, isLiteralIndex := index.Index.(*ast.IntegerLiteral)
		if !isIdentifier || base.Value != name || !isLiteralIndex || at.Wide || at.Value < 0 || at.Value >= arr.length || seen[at.Value] {
			return nil, false
		}
		source[destination] = at.Value
		seen[at.Value] = true
	}
	return source, true
}

// lowerSelfPermutation realizes new[i] = old[source[i]] cycle by cycle in
// the array's own frame storage. Two scalar registers retain the displaced
// value and carry the next value; fixed points need no instructions.
func (g *generator) lowerSelfPermutation(arr *arrayLocal, source []int64) error {
	changed := false
	for destination, at := range source {
		if int64(destination) != at {
			changed = true
			break
		}
	}
	if !changed {
		return nil
	}
	saved, err := g.alloc(arr.elem)
	if err != nil {
		return err
	}
	work, err := g.alloc(arr.elem)
	if err != nil {
		g.release(saved)
		return err
	}
	defer g.release(saved)
	defer g.release(work)

	stride := int64(arr.elem.bits / 8)
	visited := make([]bool, len(source))
	for start := range source {
		if visited[start] {
			continue
		}
		visited[start] = true
		next := int(source[start])
		if next == start {
			continue
		}
		g.emit(loadOf(arr.elem), reg(saved, arr.elem), g.slotMem(arr.offset+int64(start)*stride))
		current := start
		for next != start {
			g.emit(loadOf(arr.elem), reg(work, arr.elem), g.slotMem(arr.offset+int64(next)*stride))
			g.emit(storeOf(arr.elem), reg(work, arr.elem), g.slotMem(arr.offset+int64(current)*stride))
			current = next
			visited[current] = true
			next = int(source[current])
		}
		g.emit(storeOf(arr.elem), reg(saved, arr.elem), g.slotMem(arr.offset+int64(current)*stride))
	}
	return nil
}
