package main

import (
	"crypto/sha256"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestOakRORRequiredTwinReceipt(t *testing.T) {
	fixture := []byte("exact serialized fixture bytes")
	source, run := strings.Repeat("a", 64), strings.Repeat("b", 64)
	path := filepath.Join(t.TempDir(), "twin.json")
	t.Setenv("OAK_REQUIRE_ROR_TWIN", "1")
	t.Setenv("OAK_ROR_TWIN_SOURCE", source)
	t.Setenv("OAK_ROR_TWIN_RUN", run)
	t.Setenv("OAK_ROR_TWIN_RECEIPT", path)
	valid := func() map[string]any {
		return map[string]any{"schema": 1, "source_sha256": source, "run": run,
			"fixture_sha256": fmt.Sprintf("%x", sha256.Sum256(fixture)), "cases": make([]oakRORTwinReceipt, 30)}
	}
	write := func(value any) {
		t.Helper()
		data, err := json.Marshal(value)
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, data, 0600); err != nil {
			t.Fatal(err)
		}
	}
	t.Run("missing path", func(t *testing.T) {
		t.Setenv("OAK_ROR_TWIN_RECEIPT", "")
		if _, err := oakRORLoadTwinReceipts(fixture); err == nil {
			t.Fatal("required lane accepted no receipt path")
		}
	})
	t.Run("missing file", func(t *testing.T) {
		if _, err := oakRORLoadTwinReceipts(fixture); err == nil {
			t.Fatal("required lane accepted no receipt file")
		}
	})
	for _, field := range []string{"schema", "source_sha256", "run", "fixture_sha256", "cases"} {
		t.Run("reject substituted "+field, func(t *testing.T) {
			document := valid()
			delete(document, field)
			write(document)
			if _, err := oakRORLoadTwinReceipts(fixture); err == nil {
				t.Fatalf("required lane accepted missing %s", field)
			}
		})
	}
	t.Run("reject legacy receipt", func(t *testing.T) {
		write(make([]oakRORTwinReceipt, 30))
		if _, err := oakRORLoadTwinReceipts(fixture); err == nil {
			t.Fatal("required lane accepted unbound legacy receipt")
		}
	})
	t.Run("accept matching receipt", func(t *testing.T) {
		write(valid())
		if got, err := oakRORLoadTwinReceipts(fixture); err != nil || len(got) != 30 {
			t.Fatalf("matching receipt: %d cases, %v", len(got), err)
		}
	})
	t.Run("developer compatibility", func(t *testing.T) {
		t.Setenv("OAK_REQUIRE_ROR_TWIN", "")
		write(make([]oakRORTwinReceipt, 30))
		if got, err := oakRORLoadTwinReceipts(fixture); err != nil || len(got) != 30 {
			t.Fatalf("legacy receipt: %d cases, %v", len(got), err)
		}
		t.Setenv("OAK_ROR_TWIN_RECEIPT", "")
		if got, err := oakRORLoadTwinReceipts(fixture); err != nil || got != nil {
			t.Fatalf("optional receipt: %v, %v", got, err)
		}
	})
}
