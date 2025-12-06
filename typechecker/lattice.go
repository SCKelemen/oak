package typechecker

import (
	"github.com/SCKelemen/oak/ast"
)

// TypeLattice implements the type lattice operations
// For MCU-friendly design: minimal lattice with never (bottom) and any (top)
// Only relationships: never ≤ T ≤ any for all T, plus reflexivity
// No other subtyping relationships in v1

// IsSubtype checks if T1 ≤ T2 in the lattice
// Returns true if T1 is a subtype of T2
// Implements the subtyping partial order from the type universe spec
func IsSubtype(t1, t2 Type) bool {
	// Reflexivity: T ≤ T
	if t1.Equals(t2) {
		return true
	}

	// Bottom: never ≤ T for all T
	if _, ok := t1.(*NeverType); ok {
		return true
	}

	// Top: T ≤ any for all T
	if _, ok := t2.(*AnyType); ok {
		return true
	}

	// Union types: A ≤ A | B and B ≤ A | B
	if unionType, ok := t2.(*UnionType); ok {
		for _, memberType := range unionType.Types {
			if IsSubtype(t1, memberType) {
				return true
			}
		}
	}

	// Intersection types: A & B ≤ A and A & B ≤ B
	if intersectionType, ok := t1.(*IntersectionType); ok {
		// A & B ≤ T if A ≤ T and B ≤ T
		for _, memberType := range intersectionType.Types {
			if !IsSubtype(memberType, t2) {
				return false
			}
		}
		return true
	}

	// No other relationships in v1 (nominal types remain distinct)
	return false
}

// Join computes the least upper bound (join) of types
// For union types: join(A, B) = A | B (when defined)
// For our minimal lattice:
// - join(T, T) = T
// - join(T, any) = any
// - join(T, never) = T
// - join(A, B) = A | B for union types
// - join(T1, T2) where T1 ≠ T2 and neither is any/never/union = any (incomparable)
func Join(types ...Type) Type {
	if len(types) == 0 {
		return &NeverType{} // Empty join is bottom
	}

	if len(types) == 1 {
		return types[0]
	}

	// Filter out never types (they don't affect the join)
	nonNeverTypes := []Type{}
	for _, t := range types {
		if _, ok := t.(*NeverType); !ok {
			nonNeverTypes = append(nonNeverTypes, t)
		}
	}

	// If all were never, result is never
	if len(nonNeverTypes) == 0 {
		return &NeverType{}
	}

	// If any is any, result is any
	for _, t := range nonNeverTypes {
		if _, ok := t.(*AnyType); ok {
			return &AnyType{}
		}
	}

	// Check if all types are equal
	firstType := nonNeverTypes[0]
	allEqual := true
	for i := 1; i < len(nonNeverTypes); i++ {
		if !nonNeverTypes[i].Equals(firstType) {
			allEqual = false
			break
		}
	}

	if allEqual {
		return firstType
	}

	// For two types, create a union type A | B
	if len(nonNeverTypes) == 2 {
		return &UnionType{Types: nonNeverTypes}
	}

	// For multiple types, create a union type
	// Flatten any existing union types
	flattened := []Type{}
	for _, t := range nonNeverTypes {
		if union, ok := t.(*UnionType); ok {
			flattened = append(flattened, union.Types...)
		} else {
			flattened = append(flattened, t)
		}
	}
	return &UnionType{Types: flattened}
}

// Meet computes the greatest lower bound (meet) of types
// For intersection types: meet(A, B) = A & B (when defined)
// For our minimal lattice:
// - meet(T, T) = T
// - meet(T, never) = never
// - meet(T, any) = T
// - meet(A, B) = A & B for intersection types
// - meet(T1, T2) where T1 ≠ T2 and neither is never/any/intersection = never (incomparable)
func Meet(types ...Type) Type {
	if len(types) == 0 {
		return &AnyType{} // Empty meet is top
	}

	if len(types) == 1 {
		return types[0]
	}

	// If any is never, result is never
	for _, t := range types {
		if _, ok := t.(*NeverType); ok {
			return &NeverType{}
		}
	}

	// If any is any, filter it out (any doesn't affect meet)
	nonAnyTypes := []Type{}
	for _, t := range types {
		if _, ok := t.(*AnyType); !ok {
			nonAnyTypes = append(nonAnyTypes, t)
		}
	}

	// If all were any, result is any
	if len(nonAnyTypes) == 0 {
		return &AnyType{}
	}

	// Check if all types are equal
	firstType := nonAnyTypes[0]
	allEqual := true
	for i := 1; i < len(nonAnyTypes); i++ {
		if !nonAnyTypes[i].Equals(firstType) {
			allEqual = false
			break
		}
	}

	if allEqual {
		return firstType
	}

	// For two types, create an intersection type A & B
	if len(nonAnyTypes) == 2 {
		return &IntersectionType{Types: nonAnyTypes}
	}

	// For multiple types, create an intersection type
	// Flatten any existing intersection types
	flattened := []Type{}
	for _, t := range nonAnyTypes {
		if intersection, ok := t.(*IntersectionType); ok {
			flattened = append(flattened, intersection.Types...)
		} else {
			flattened = append(flattened, t)
		}
	}
	return &IntersectionType{Types: flattened}
}

// NarrowType narrows a type based on pattern matching
// For ADT variants, returns a narrowed variant type
// For literal patterns, returns the literal's type if it matches
// Otherwise returns the original type
func NarrowType(originalType Type, pattern ast.Pattern) Type {
	// For variant patterns, narrow to that specific variant
	if variantPattern, ok := pattern.(*ast.VariantPattern); ok {
		if adtType, ok := originalType.(*ADTType); ok {
			return &NarrowedADTVariantType{
				ADTName:     adtType.Name,
				VariantName: variantPattern.Variant.Value,
			}
		}
	}

	// For literal patterns, if the literal type matches, we can narrow
	// (This is more advanced and can be expanded later)

	// For wildcard or binding patterns, no narrowing
	return originalType
}

// JoinNarrowedTypes joins narrowed types back to the original type
// Used to verify that pattern matching branches cover all cases
func JoinNarrowedTypes(narrowedTypes []Type) Type {
	// Convert narrowed variant types back to their ADT types
	adtTypes := []Type{}
	for _, nt := range narrowedTypes {
		if narrowed, ok := nt.(*NarrowedADTVariantType); ok {
			adtTypes = append(adtTypes, &ADTType{Name: narrowed.ADTName})
		} else {
			adtTypes = append(adtTypes, nt)
		}
	}

	// Join them
	return Join(adtTypes...)
}
