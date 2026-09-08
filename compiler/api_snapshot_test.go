package compiler

import (
	"strings"
	"testing"
)

func TestAPISnapshotSeparatesRecordMeaningFromStructABI(t *testing.T) {
	snapshot, err := New().
		WithPackageName("example/layout").
		WithSource("layout.oak", `
AB: type = struct { a: u8, b: u32 }
BA: type = struct { b: u32, a: u8 }
ShapeAB: type = { a: u8, b: u32 }
ShapeBA: type = { b: u32, a: u8 }

getA: (value: { r | a: u8 }): u8 = value.a
`).
		APISnapshot("1.2.3").
		Get()
	if err != nil {
		t.Fatal(err)
	}

	if snapshot.Package != "example/layout" || snapshot.Version != "1.2.3" {
		t.Fatalf("snapshot identity = (%q, %q)", snapshot.Package, snapshot.Version)
	}
	if snapshot.Exports["AB"].Type != snapshot.Exports["BA"].Type {
		t.Fatalf("same struct fields must have one semantic record identity: %q vs %q", snapshot.Exports["AB"].Type, snapshot.Exports["BA"].Type)
	}
	if snapshot.Exports["AB"].ABI == snapshot.Exports["BA"].ABI {
		t.Fatalf("different struct orders must have different ABI: %q", snapshot.Exports["AB"].ABI)
	}
	if got := snapshot.Exports["AB"].ABI; got != "size=8;align=4;packed=false;declared-align=0;a@0:1;b@4:4" {
		t.Fatalf("AB ABI = %q", got)
	}
	if got := snapshot.Exports["BA"].ABI; got != "size=8;align=4;packed=false;declared-align=0;b@0:4;a@4:1" {
		t.Fatalf("BA ABI = %q", got)
	}
	if snapshot.Exports["ShapeAB"].Type != snapshot.Exports["ShapeBA"].Type {
		t.Fatalf("record source order leaked into semantic identity: %q vs %q", snapshot.Exports["ShapeAB"].Type, snapshot.Exports["ShapeBA"].Type)
	}
	if snapshot.Exports["ShapeAB"].ABI != "" || snapshot.Exports["ShapeBA"].ABI != "" {
		t.Fatalf("semantic records acquired an ABI: %#v %#v", snapshot.Exports["ShapeAB"], snapshot.Exports["ShapeBA"])
	}
	if got := snapshot.Exports["getA"]; got.Kind != "function" || !strings.Contains(got.Type, "record{a:u8|r}") {
		t.Fatalf("checked extensible-record function missing from snapshot: %#v", got)
	}
}

func TestAPISnapshotIsDeterministic(t *testing.T) {
	compilation := New().WithPackageName("example/deterministic").WithSource("api.oak", `
Shape: type = { z: u16, a: u8, middle: u32 }
Stored: type = struct(align: 16) { z: u16, a: u8, middle: u32 }
identity[T]: (value: T): T = value
`)
	first, err := compilation.APISnapshot("0.1.0").Get()
	if err != nil {
		t.Fatal(err)
	}
	for i := 0; i < 3; i++ {
		next, err := compilation.APISnapshot("0.1.0").Get()
		if err != nil {
			t.Fatal(err)
		}
		for name, export := range first.Exports {
			if next.Exports[name] != export {
				t.Fatalf("run %d export %q changed: %#v vs %#v", i, name, export, next.Exports[name])
			}
		}
	}
}

func TestAPISnapshotRejectsInvalidVersionBeforePublication(t *testing.T) {
	_, err := New().WithSource("api.oak", `main: (): i32 = 0`).APISnapshot("1.2.+3").Get()
	if err == nil {
		t.Fatal("invalid publication version was accepted")
	}
}

func TestAPISnapshotPreservesGenericStructLayoutContract(t *testing.T) {
	snapshot, err := New().WithSource("generic.oak", `
Slot[T]: type = struct(align: 16) { value: T, tag: u8 }
`).APISnapshot("0.1.0").Get()
	if err != nil {
		t.Fatal(err)
	}
	got := snapshot.Exports["Slot"]
	if got.Type != "record[T]{tag:u8,value:T}" {
		t.Fatalf("generic struct semantic identity = %q", got.Type)
	}
	if got.ABI != "generic=true;packed=false;declared-align=16;value:T:align=0;tag:u8:align=0" {
		t.Fatalf("generic struct ABI = %q", got.ABI)
	}
}

func TestAPISnapshotIncludesMethodsGenericFieldsAndLiteralADTs(t *testing.T) {
	methodSnapshot, err := New().WithSource("method.oak", `
Uart: type = { port: u32 }
fn (u: *Uart) read() -> i32 = 0
`).APISnapshot("1.0.0").Get()
	if err != nil {
		t.Fatal(err)
	}
	method, ok := methodSnapshot.Exports["*Uart::read"]
	if !ok || method.Kind != "method" || !strings.Contains(method.Type, "receiver[*Uart]") {
		t.Fatalf("receiver method missing from API: %#v", method)
	}

	genericSnapshot, err := New().WithSource("generic-field.oak", `
Slot[T]: type = struct { value: T }
Holder: type = struct { slot: Slot[u8], tail: u32 }
`).APISnapshot("1.0.0").Get()
	if err != nil {
		t.Fatal(err)
	}
	if got := genericSnapshot.Exports["Holder"].ABI; got != "size=8;align=4;packed=false;declared-align=0;slot@0:1;tail@4:4" {
		t.Fatalf("generic field layout was not resolved: %q", got)
	}

	adtSnapshot, err := New().WithSource("literal-adt.oak", `
Status: type = | Ready: u8 = 1
`).APISnapshot("1.0.0").Get()
	if err != nil {
		t.Fatal(err)
	}
	if got := adtSnapshot.Exports["Status"].Type; got != "sum{Ready(u8)=1}" {
		t.Fatalf("literal ADT identity = %q", got)
	}
}
