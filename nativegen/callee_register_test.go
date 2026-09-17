package nativegen

import (
	"reflect"
	"testing"
)

func TestTakeCalleeRegisterSkipsCallerHomesInMixedPool(t *testing.T) {
	g := &generator{freeCallee: []int{9, 19, 10, 21, 11}}
	r, ok := g.takeCalleeRegister()
	if !ok || r != 21 {
		t.Fatalf("register = %d, %v; want x21", r, ok)
	}
	if want := []int{9, 19, 10, 11}; !reflect.DeepEqual(g.freeCallee, want) {
		t.Fatalf("free pool = %v, want %v", g.freeCallee, want)
	}
}

func TestTakeCalleeRegisterLeavesCallerPoolForFreshHome(t *testing.T) {
	g := &generator{freeCallee: []int{2, 9, 15}}
	r, ok := g.takeCalleeRegister()
	if !ok || r != calleeLow {
		t.Fatalf("register = %d, %v; want x%d", r, ok, calleeLow)
	}
	if g.usedCallee != 1 {
		t.Fatalf("used callee registers = %d, want 1", g.usedCallee)
	}
	if want := []int{2, 9, 15}; !reflect.DeepEqual(g.freeCallee, want) {
		t.Fatalf("free pool = %v, want %v", g.freeCallee, want)
	}
}

func TestTakeCalleeRegisterLeavesCallerPoolForReserve(t *testing.T) {
	g := &generator{
		freeCallee:  []int{9, 15},
		usedCallee:  calleeHigh - calleeLow + 1 - fieldHomeReserve,
		licmReserve: []int{25, 26},
	}
	r, ok := g.takeCalleeRegister()
	if !ok || r != 26 {
		t.Fatalf("register = %d, %v; want reserved x26", r, ok)
	}
	if want := []int{9, 15}; !reflect.DeepEqual(g.freeCallee, want) {
		t.Fatalf("free pool = %v, want %v", g.freeCallee, want)
	}
	if want := []int{25}; !reflect.DeepEqual(g.licmReserve, want) {
		t.Fatalf("reserve = %v, want %v", g.licmReserve, want)
	}
}

func TestTakeCalleeRegisterRefusesWithoutConsumingCallerPool(t *testing.T) {
	g := &generator{
		freeCallee: []int{2, 9, 15},
		usedCallee: calleeHigh - calleeLow + 1 - fieldHomeReserve,
	}
	if r, ok := g.takeCalleeRegister(); ok || r != 0 {
		t.Fatalf("register = %d, %v; want refusal", r, ok)
	}
	if want := []int{2, 9, 15}; !reflect.DeepEqual(g.freeCallee, want) {
		t.Fatalf("free pool = %v, want %v", g.freeCallee, want)
	}
}
