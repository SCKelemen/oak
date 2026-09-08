package typechecker

import (
	"testing"

	"github.com/SCKelemen/oak/object"
)

func TestBorrowStorageRecursivePayloads(t *testing.T) {
	tc := New(object.NewEnvironment())
	byteType := &PrimitiveType{Name: "u8"}
	view := &ArrayType{IsSlice: true, Length: -1, ElementType: byteType}
	parameter := &ADTType{Name: "T"}
	generic := func(name string, argument Type) Type {
		return &GenericType{Name: name, TypeArgs: []Type{argument}}
	}
	define := func(name string, payload Type) {
		tc.adtTypes[name] = &object.ADTType{
			Name: name, TypeParams: []string{"T"},
			Variants: []*object.ADTVariantDef{{Name: "Value", Payload: "checked"}},
		}
		tc.adtPayloadTypes[name] = map[string]Type{"Value": payload}
	}
	define("Box", parameter)
	define("Phantom", byteType)
	define("Loop", generic("Loop", generic("Box", parameter)))
	define("Changes", &RecordType{Fields: map[string]Type{
		"next": generic("Changes", view),
		"value": parameter,
	}})
	define("Nested", generic("Box", generic("Phantom", parameter)))
	for _, fixture := range []struct {
		name string
		typ Type
		want bool
	}{
		{"stored argument", generic("Box", view), true},
		{"phantom argument", generic("Phantom", view), false},
		{"nested phantom", generic("Nested", view), false},
		{"expanding recursion", generic("Loop", byteType), false},
		{"changing recursion", generic("Changes", byteType), true},
		{"owned instantiation", generic("Box", byteType), false},
	} {
		t.Run(fixture.name, func(t *testing.T) {
			if got := tc.Env().ContainsBorrowStorage(fixture.typ); got != fixture.want {
				t.Fatalf("got %v, want %v", got, fixture.want)
			}
		})
	}
}
