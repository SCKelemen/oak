package compiler

import (
	"hash/fnv"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
)

const (
	statusFeatureCount = 191
	statusFeatureStateFNV64 = uint64(0x6d53bd7592da19b7)
)

func TestStatusFeatureInventoryIsClosed(t *testing.T) {
	data, err := os.ReadFile(filepath.Join("..", "docs", "spec", "STATUS.md"))
	if err != nil {
		t.Fatal(err)
	}
	allowed := map[string]bool{"": true, "✓": true, "partial": true}
	seen := make(map[string]bool)
	var rows [][]string
	for _, line := range strings.Split(string(data), "\n") {
		if !strings.HasPrefix(line, "| ") || strings.HasPrefix(line, "| Feature ") || strings.HasPrefix(line, "| ---") {
			continue
		}
		parts := strings.Split(line, "|")
		if len(parts) < 10 {
			t.Fatalf("malformed STATUS row: %s", line)
		}
		cells := make([]string, 0, len(parts)-2)
		for _, part := range parts[1 : len(parts)-1] {
			cells = append(cells, strings.TrimSpace(part))
		}
		if len(cells) < 8 {
			t.Fatalf("STATUS row has %d cells, want at least 8: %s", len(cells), line)
		}
		feature := cells[0]
		if feature == "" {
			t.Fatal("STATUS contains an unnamed feature row")
		}
		if seen[feature] {
			t.Fatalf("STATUS contains duplicate feature row %q", feature)
		}
		seen[feature] = true
		if cells[1] != "✓" {
			t.Errorf("%s: source-of-truth specification column is %q, want ✓", feature, cells[1])
		}
		for i, state := range cells[1:7] {
			if !allowed[state] {
				t.Errorf("%s: invalid status %q in column %d", feature, state, i+1)
			}
		}
		if cells[7] == "" {
			t.Errorf("%s: notes/evidence column is empty", feature)
		}
		rows = append(rows, cells)
	}
	if len(rows) != statusFeatureCount {
		t.Fatalf("STATUS feature count = %d, want %d; review every added/removed feature and update the closure contract", len(rows), statusFeatureCount)
	}

	var payload strings.Builder
	for i, cells := range rows {
		if i != 0 {
			payload.WriteByte('\n')
		}
		payload.WriteString(strings.Join(cells[:7], "\t"))
	}
	hash := fnv.New64a()
	_, _ = hash.Write([]byte(payload.String()))
	if got := hash.Sum64(); got != statusFeatureStateFNV64 {
		t.Fatalf("STATUS feature/state inventory changed: got 0x%s, want 0x%s; review specification/implementation/test/proof/refinement evidence before updating the contract",
			strconv.FormatUint(got, 16), strconv.FormatUint(statusFeatureStateFNV64, 16))
	}
}
