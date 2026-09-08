package modules

import "sort"

// Order places packages in dependency order: every package appears after
// every package it imports. It is the compile order of the module graph.
//
// The procedure is Kahn's algorithm with deterministic tie-breaking (candidates
// are scanned in sorted order). It returns the placed order and, when the
// graph cannot be fully placed, the set of packages left unplaced. Every
// unplaced package imports some other unplaced package
// (Oak.Modules.Order.stuck_imports_stuck), which is exactly what it means for
// the remaining set to contain an import cycle; ImportCycle extracts one.
//
// Imports naming a package outside nodes are never satisfied, so a package
// with such an import stays unplaced; the loader guarantees closure before
// ordering.
func Order(nodes []string, imports map[string][]string) (order []string, stuck []string) {
	remaining := append([]string(nil), nodes...)
	sort.Strings(remaining)
	placed := map[string]bool{}
	for len(remaining) != 0 {
		var next []string
		progress := false
		for _, node := range remaining {
			if allPlaced(imports[node], placed) {
				order = append(order, node)
				placed[node] = true
				progress = true
			} else {
				next = append(next, node)
			}
		}
		if !progress {
			return order, next
		}
		remaining = next
	}
	return order, nil
}

func allPlaced(imports []string, placed map[string]bool) bool {
	for _, imported := range imports {
		if !placed[imported] {
			return false
		}
	}
	return true
}

// ImportCycle returns one concrete import cycle among the stuck packages
// reported by Order, as a path whose last element imports its first element.
// It walks from the smallest stuck package along stuck imports until a
// package repeats; because every stuck package has a stuck import, the walk
// always closes.
func ImportCycle(stuck []string, imports map[string][]string) []string {
	if len(stuck) == 0 {
		return nil
	}
	inStuck := map[string]bool{}
	for _, node := range stuck {
		inStuck[node] = true
	}
	sorted := append([]string(nil), stuck...)
	sort.Strings(sorted)
	visited := map[string]int{}
	var walk []string
	current := sorted[0]
	for {
		if index, seen := visited[current]; seen {
			return walk[index:]
		}
		visited[current] = len(walk)
		walk = append(walk, current)
		next := ""
		targets := append([]string(nil), imports[current]...)
		sort.Strings(targets)
		for _, imported := range targets {
			if inStuck[imported] {
				next = imported
				break
			}
		}
		if next == "" {
			// Unreachable for a stuck set produced by Order; fail closed by
			// reporting the walk so far rather than looping.
			return walk
		}
		current = next
	}
}
