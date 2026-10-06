package compiler

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

type surfaceEvidence struct {
	Lane   string
	Files  []string
	Reason string
}

const (
	surfaceNative    = "native"
	surfaceStatic    = "static"
	surfaceTooling   = "tooling"
	surfaceDirection = "direction"
)

var sourceSurfaceEvidence = map[string]surfaceEvidence{
	"Declaration shape `name: (params): T = body`, block bodies, `pub`, `pub(opaque)`": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_statement_ergonomics_test.go", "compiler/e2e_modules_test.go"},
	},
	"`?` conditionals and match expressions; no `if`/`else`": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_test.go"},
	},
	"Fixed-width integers: total wrapping `+ - * / %`, explicit narrowing (`_trunc_`, `_saturating_`, `_checked_`, `_bits_`), one-signedness comparisons": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_total_arithmetic_test.go", "compiler/e2e_checked_arithmetic_test.go"},
	},
	"Records and structs, layout introspection, `static_assert`": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_layout_test.go", "compiler/e2e_shape_test.go"},
	},
	"Sum types, generic ADTs, monomorphized generic functions": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_generic_functions_test.go", "compiler/e2e_qualified_generic_variant_test.go"},
	},
	"Views and spans, lexical v1 lifetimes, `view(&x)`/`span(&x)`, call-local exclusivity": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_test.go"},
	},
	"Region-indexed borrowed returns": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_region_returns_test.go"},
	},
	"Modules: `package`, `import`, `oak.mod`, semver at module granularity, per-module profiles": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_modules_test.go"},
	},
	"Strings and UTF-8 validity": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_stdlib_utf8_test.go", "compiler/e2e_string_equality_test.go"},
	},
	"Standard-library architecture: package layers, explicit storage/effects, public contract, proof-directed optimization": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_stdlib_test.go"},
	},
	"Qualified `bytes`: ranges, copying/movement, equality, ordering, and search": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_stdlib_bytes_package_test.go"},
	},
	"Qualified `bitset`: `storage_bytes`, `contains`, `set`, `count_ones`, `Error`": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_stdlib_bitset_package_test.go"},
	},
	"Qualified `endian`: concrete `u16`/`u32`/`u64` reads and writes in both byte orders": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_stdlib_endian_package_test.go"},
	},
	"Qualified `buffer`: contiguous byte queue cursor and value-state builder": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_stdlib_buffer_package_test.go"},
	},
	"Qualified `array_list`: bounded generic vectors over caller storage": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_stdlib_array_list_package_test.go"},
	},
	"Derived declarations (`derive.equal/hash/compare/format`)": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_derived_json_test.go", "compiler/e2e_modules_test.go"},
	},
	"Typed test commands (`derive.test_generate/encode/decode`), `oak test` flags, artifact and campaign formats": {
		Lane: surfaceTooling, Files: []string{"compiler/e2e_testing_samplers_test.go"},
		Reason: "this is a test-runner/tooling surface; its observable contract is generated campaigns/artifacts and runner behavior rather than the exit status of an ordinary Oak program",
	},
	"Simulated storage, crashes, scheduling adapters (`SimDisk`, `SimProcess`, `SimSched`)": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_iosim_read_flip_test.go", "compiler/e2e_testing_samplers_test.go"},
	},
	"Effect clauses `effects { }` / `forbids { }`, effect rows on function types and record fields": {
		Lane: surfaceStatic, Files: []string{"compiler/e2e_effect_rows_test.go", "compiler/e2e_effects_test.go"},
		Reason: "effect clauses are compile-time authority contracts; acceptance/rejection and inferred rows are the semantic observation, while the admitted program executes with ordinary runtime operations",
	},
	"Protocol declarations `Name: protocol = { ... }`, record payloads, array and record data, quantifier forms, `fair`/`eventually`, invariant theorems": {
		Lane: surfaceStatic, Files: []string{"compiler/e2e_protocol_test.go", "compiler/e2e_protocol_quantifier_predicate_test.go"},
		Reason: "the declaration surface primarily elaborates verification and monitor obligations; protocol-specific runtime projections have separate end-to-end tests",
	},
	"Discipline profiles (`default`/`strict`), safe recursion, bounded loops, located assertions": {
		Lane: surfaceStatic, Files: []string{"compiler/e2e_bounded_loops_test.go", "compiler/e2e_assert_source_file_test.go"},
		Reason: "the distinguishing contract is whether the compiler accepts, warns, or rejects a program under a profile; accepted loops and assertions are executed in adjacent end-to-end tests",
	},
	"C FFI: `c.extern`, scalar and span boundaries, generated headers": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_ffi_spans_test.go", "compiler/e2e_c_exports_test.go"},
	},
	"Portable SIMD (`simd.*` 128-bit unsigned, `F32x4`/`F64x2`), `arm64` library": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_simd_bytes_test.go", "compiler/e2e_float_simd_test.go"},
	},
	"Assembler units and the AArch64 surfaces": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_asm_test.go", "compiler/e2e_asm_verify_test.go"},
	},
	"Attributes other than the clauses above (layout `struct(packed)`, section names)": {
		Lane: surfaceStatic, Files: []string{"compiler/e2e_layout_test.go", "compiler/e2e_asm_package_test.go"},
		Reason: "layout and section attributes primarily select representation and placement; the strongest direct observation is emitted layout/object metadata, with ordinary users executed separately",
	},
	"Typestate-indexed handles, `via` parameter modes, `Buffer[T, S]` custody and Buffer fields in records": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_typestate_test.go", "compiler/e2e_protocol_via_modes_test.go"},
	},
	"Parameterized effects": {
		Lane: surfaceDirection,
		Reason: "STABILITY marks this surface direction-only; it is not yet a complete implementation contract that can honestly claim end-to-end execution",
	},
	"Kernels (`kernel` declarations, launch descriptors, `reduce.group_tree`), the `tensor` and `reduce` packages": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_kernels_test.go"},
	},
	"`order tree | left | bounded { }` blocks and `reduce.reduce`": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_reduce_order_test.go"},
	},
	"Measured constants (`(measured: lo, hi)`)": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_measured_test.go", "compiler/e2e_measured_imports_test.go"},
	},
	"`view_as[U]` / `span_as[U]` scalar views of record views": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_scalar_view_test.go"},
	},
	"`Launch` test targets and `test_launch`": {
		Lane: surfaceTooling, Files: []string{"testrunner/launches_test.go"},
		Reason: "Launch is a test-runner target surface; the strongest observation is runner launch expansion/execution rather than an ordinary compiled program",
	},
	"IO port: caller-owned completion rings, `open`/`close`/`pread`/`pwrite`/`fsync`/`fdatasync`/`fsyncdir`, `replace io => iosim|ionative`": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_io_port_test.go"},
	},
	"IO surface beyond the port (io_uring realization, registered buffers, sockets)": {
		Lane: surfaceDirection,
		Reason: "STABILITY explicitly says this increment is designed but has no realization yet; claiming native evidence would be false",
	},
	"Floating point beyond `f32`/`f64` arithmetic and the two float vectors": {
		Lane: surfaceNative, Files: []string{"compiler/e2e_floats_test.go", "compiler/e2e_float_simd_test.go"},
	},
}

func splitStabilityRow(line string) []string {
	if !strings.HasPrefix(line, "|") {
		return nil
	}
	var cells []string
	var cell strings.Builder
	for i := 1; i < len(line); i++ {
		if line[i] == '\\' && i+1 < len(line) && line[i+1] == '|' {
			cell.WriteByte('|')
			i++
			continue
		}
		if line[i] == '|' {
			cells = append(cells, strings.TrimSpace(cell.String()))
			cell.Reset()
			continue
		}
		cell.WriteByte(line[i])
	}
	if len(cells) > 0 && cells[len(cells)-1] == "" {
		cells = cells[:len(cells)-1]
	}
	return cells
}

func TestSourceSurfaceInventoryHasStrongestEvidenceLane(t *testing.T) {
	data, err := os.ReadFile(filepath.Join("..", "docs", "spec", "STABILITY.md"))
	if err != nil {
		t.Fatal(err)
	}
	text := string(data)
	start := strings.Index(text, "## Marks by surface")
	if start < 0 {
		t.Fatal("STABILITY.md has no Marks by surface section")
	}
	seen := make(map[string]bool)
	rows := 0
	for _, line := range strings.Split(text[start:], "\n") {
		if !strings.HasPrefix(line, "| ") || strings.HasPrefix(line, "| ---") || strings.HasPrefix(line, "| Surface ") {
			continue
		}
		cells := splitStabilityRow(line)
		if len(cells) < 4 {
			t.Errorf("malformed STABILITY surface row: %s", line)
			continue
		}
		surface, spec, mark := cells[0], cells[1], cells[2]
		if mark != "frozen" && mark != "stabilizing" && mark != "direction" {
			continue
		}
		rows++
		seen[surface] = true
		if spec == "" {
			t.Errorf("surface %q has no specification anchor", surface)
		}
		ev, ok := sourceSurfaceEvidence[surface]
		if !ok {
			t.Errorf("source surface %q (%s) has no verification disposition", surface, mark)
			continue
		}
		switch ev.Lane {
		case surfaceNative, surfaceStatic, surfaceTooling, surfaceDirection:
		default:
			t.Errorf("surface %q has invalid evidence lane %q", surface, ev.Lane)
		}
		if ev.Lane != surfaceNative && ev.Reason == "" {
			t.Errorf("non-native surface %q must explain why native execution is not the strongest meaningful lane", surface)
		}
		if mark != "direction" && ev.Lane == surfaceDirection {
			t.Errorf("%s surface %q cannot be classified direction-only", mark, surface)
		}
		if ev.Lane != surfaceDirection && len(ev.Files) == 0 {
			t.Errorf("surface %q has no concrete evidence files", surface)
		}
		for _, file := range ev.Files {
			path := filepath.Join("..", filepath.FromSlash(file))
			content, err := os.ReadFile(path)
			if err != nil {
				t.Errorf("surface %q evidence %s is missing: %v", surface, file, err)
				continue
			}
			if ev.Lane == surfaceNative {
				base := filepath.Base(file)
				if !strings.HasPrefix(base, "e2e_") {
					t.Errorf("native surface %q points at non-e2e evidence %s", surface, file)
				}
				body := string(content)
				if !strings.Contains(body, "buildAndRun(") &&
					!strings.Contains(body, "buildAndRunFrom(") &&
					!strings.Contains(body, "buildPackageAndRun(") {
					t.Errorf("native surface %q evidence %s contains no hosted execution call", surface, file)
				}
			}
		}
	}
	if rows == 0 {
		t.Fatal("no source-surface rows found in STABILITY.md")
	}
	for surface := range sourceSurfaceEvidence {
		if !seen[surface] {
			t.Errorf("stale source-surface evidence for %q: no matching STABILITY.md row", surface)
		}
	}
}
