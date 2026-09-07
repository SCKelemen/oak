package typechecker

// Typed struct field tags (docs/spec/40-records.md §12): Go's per-field
// metadata ergonomics with the checking Go never had. A tag namespace must
// be a declared schema (json: tag = { name: string }), so a typo'd
// namespace is a compile error, never silent metadata; every provided
// value typechecks against the schema's field type. Tags live on the
// metadata axis only — they never touch layout, representation, or the
// runtime value. Maintained alongside Oak.FieldTags (Lean), which proves
// the conformance checker sound and complete.

import (
	"github.com/SCKelemen/oak/ast"
)

// tagValueTypeLegal restricts schema fields to the literal-representable
// vocabulary: strings, fixed-width integers, and Bool. Tag values are
// compile-time data for projections, not expressions.
func tagValueTypeLegal(typ Type) bool {
	switch t := typ.(type) {
	case *StringType:
		return true
	case *BoolType:
		return true
	case *PrimitiveType:
		return t != nil
	}
	return false
}

// checkTagDeclaration registers one tag schema, validating that every
// schema field carries a literal-representable type.
func (tc *TypeChecker) checkTagDeclaration(decl *ast.TagDeclaration) {
	if decl == nil || decl.Name == nil || decl.Schema == nil {
		return
	}
	name := decl.Name.Value
	if _, exists := tc.tagSchemas[name]; exists {
		tc.addError(decl.Name, "tag schema %s is already declared", name)
		return
	}
	schemaType := tc.parseRecordTypeFromLiteral(decl.Schema)
	schema, isRecord := schemaType.(*RecordType)
	if !isRecord || len(schema.Order) == 0 {
		tc.addError(decl.Name, "tag schema %s must declare at least one field", name)
		return
	}
	for _, fieldName := range schema.Order {
		if !tagValueTypeLegal(schema.Fields[fieldName]) {
			tc.addError(decl.Name, "tag schema %s field %s: tag values are compile-time data — string, fixed-width integer, or Bool", name, fieldName)
			return
		}
	}
	if tc.tagSchemas == nil {
		tc.tagSchemas = make(map[string]*RecordType)
	}
	tc.tagSchemas[name] = schema
}

// TagSchema exposes a declared schema to projections (serializers, schema
// generators) consuming checked metadata.
func (tc *TypeChecker) TagSchema(name string) (*RecordType, bool) {
	schema, ok := tc.tagSchemas[name]
	return schema, ok
}

// checkFieldTags validates every tag on one record field against the
// declared schemas: unknown namespaces are errors (the anti-Go rule), a
// bare literal binds to the schema's first declared field, and a record
// literal provides any subset of schema fields (tags are sparse), each
// value checked against its declared type.
func (tc *TypeChecker) checkFieldTags(typeName string, field ast.RecordField) {
	for _, tag := range field.Tags {
		schema, declared := tc.tagSchemas[tag.Name]
		if !declared {
			tc.addError(tag.Value, "record type %s field %s: unknown tag namespace %q — tag schemas must be declared (%s: tag = { ... }) so a typo can never become silent metadata", typeName, field.Name, tag.Name, tag.Name)
			continue
		}
		if literal, isRecord := tag.Value.(*ast.RecordLiteral); isRecord {
			for _, entry := range literal.FieldOrder {
				expected, known := schema.Fields[entry.Name]
				if !known {
					tc.addError(entry.Value, "record type %s field %s: tag %s has no field %s", typeName, field.Name, tag.Name, entry.Name)
					continue
				}
				tc.checkTagValue(typeName, field.Name, tag.Name, entry.Name, entry.Value, expected)
			}
			continue
		}
		// Bare value: the schema's first declared field (declaration order
		// is authoritative — the F# positional-argument precedent).
		primary := schema.Order[0]
		tc.checkTagValue(typeName, field.Name, tag.Name, primary, tag.Value, schema.Fields[primary])
	}
}

func (tc *TypeChecker) checkTagValue(typeName, fieldName, tagName, schemaField string, value ast.Expression, expected Type) {
	got := tc.checkExpression(value, expected)
	if got == nil {
		return
	}
	if !tc.isAssignable(got, expected) {
		tc.addError(value, "record type %s field %s: tag %s.%s expects %s, got %s", typeName, fieldName, tagName, schemaField, expected, got)
	}
}
