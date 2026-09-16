package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

// sailFunctionBody returns the braced body of one top-level Sail function.
// The pinned model uses nested braces in match arms, so a balanced scan is
// less brittle than making a regular expression consume the whole function.
func sailFunctionBody(source, name string) (string, error) {
	header := regexp.MustCompile(`(?m)^function[ \t]+` + regexp.QuoteMeta(name) + `[ \t]*\(`)
	location := header.FindStringIndex(source)
	if location == nil {
		return "", fmt.Errorf("function %s not found", name)
	}
	start := location[0]
	open := strings.IndexByte(source[start:], '{')
	if open < 0 {
		return "", fmt.Errorf("function %s has no body", name)
	}
	open += start
	depth := 0
	for at := open; at < len(source); at++ {
		switch source[at] {
		case '{':
			depth++
		case '}':
			depth--
			if depth == 0 {
				return source[open+1 : at], nil
			}
		}
	}
	return "", fmt.Errorf("function %s has an unterminated body", name)
}

var sailBarrierDispatchArm = regexp.MustCompile(
	`MemBarrierOp_([A-Z]+)\s*=>\s*\{\s*([A-Za-z][A-Za-z0-9_]*)\s*\(`,
)

var sailBarrierTargetArm = regexp.MustCompile(
	`MemBarrierOp_([A-Z]+)\s*=>\s*BarrierExecutionTarget_([A-Za-z][A-Za-z0-9_]*)`,
)

// TestSailArmBarrierDispatchSource pins the execution-call projection copied
// into arm_primitives.sail to the official model fetched at SAIL_ARM_COMMIT.
// It also pins the model's erased context semantics: reaching the named ISB
// primitive is proved, but its unit stub cannot discharge ArmContextSync.
func TestSailArmBarrierDispatchSource(t *testing.T) {
	modelDir := filepath.Dir(sailArmModel)
	aarch64Path := filepath.Join(modelDir, "aarch64.sail")
	aarchMemPath := filepath.Join(modelDir, "aarch_mem.sail")
	aarch64Bytes, err := os.ReadFile(aarch64Path)
	if err != nil {
		requireOracle(t, "sail-arm aarch64 model not present: "+err.Error())
	}
	aarchMemBytes, err := os.ReadFile(aarchMemPath)
	if err != nil {
		requireOracle(t, "sail-arm memory model not present: "+err.Error())
	}
	aarch64 := string(aarch64Bytes)
	aarchMem := string(aarchMemBytes)

	body, err := sailFunctionBody(aarch64, "system_barriers")
	if err != nil {
		t.Fatal(err)
	}
	want := map[string]string{
		"DSB":   "DataSynchronizationBarrier",
		"DMB":   "DataMemoryBarrier",
		"ISB":   "InstructionSynchronizationBarrier",
		"SSBB":  "SpeculativeSynchronizationBarrierToVA",
		"PSSBB": "SpeculativeSynchronizationBarrierToPA",
		"SB":    "SpeculationBarrier",
	}
	matches := sailBarrierDispatchArm.FindAllStringSubmatch(body, -1)
	if len(matches) != len(want) {
		t.Fatalf("system_barriers has %d dispatch arms, want %d: %q", len(matches), len(want), body)
	}
	official := make(map[string]string, len(matches))
	for _, match := range matches {
		op, callee := match[1], match[2]
		if _, exists := official[op]; exists {
			t.Fatalf("system_barriers repeats %s", op)
		}
		official[op] = callee
		if callee != want[op] {
			t.Fatalf("system_barriers %s dispatches to %s, want %s", op, callee, want[op])
		}
	}
	for op := range want {
		if _, exists := official[op]; !exists {
			t.Errorf("system_barriers lacks %s dispatch", op)
		}
	}

	projectionBytes, err := os.ReadFile(filepath.Join("..", "spec", "sail", "arm_primitives.sail"))
	if err != nil {
		t.Fatal(err)
	}
	projectionBody, err := sailFunctionBody(string(projectionBytes), "system_barriers_target_pure")
	if err != nil {
		t.Fatal(err)
	}
	projectionMatches := sailBarrierTargetArm.FindAllStringSubmatch(projectionBody, -1)
	if len(projectionMatches) != len(want) {
		t.Fatalf("system_barriers_target_pure has %d arms, want %d: %q",
			len(projectionMatches), len(want), projectionBody)
	}
	projected := make(map[string]bool, len(projectionMatches))
	for _, match := range projectionMatches {
		op, target := match[1], match[2]
		if projected[op] {
			t.Fatalf("system_barriers_target_pure repeats %s", op)
		}
		projected[op] = true
		if target != official[op] {
			t.Fatalf("system_barriers_target_pure %s selects %s, official source selects %s",
				op, target, official[op])
		}
	}

	for _, check := range []struct {
		source string
		name   string
	}{
		{aarch64, "InstructionSynchronizationBarrier"},
		{aarchMem, "SynchronizeContext"},
	} {
		body, err := sailFunctionBody(check.source, check.name)
		if err != nil {
			t.Fatal(err)
		}
		if compact := strings.Join(strings.Fields(body), ""); compact != "return()" {
			t.Fatalf("%s is no longer the pinned unit stub: %q", check.name, body)
		}
	}
}
