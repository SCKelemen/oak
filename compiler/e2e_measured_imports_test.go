package compiler

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/object"
)

// F29: the hook sees the declaration's source spelling, including literal
// underscores, in both an imported package and the unmangled root package.
func importedMeasuredModule(t *testing.T) string {
	t.Helper()
	for _, name := range []string{"TILE_GROUPS", "RUN_uSIZE", "ROOT_uGROUPS", "TILE_uGROUPS", "RUN_uuSIZE", "ROOT_GROUPS"} {
		t.Setenv("OAK_MEASURED_"+name, "")
	}
	return writeModule(t, map[string]string{
		"oak.mod": "module example.com/measured\noak 0.1.0\n",
		"schedule/tile_config/config.oak": `package tile_config
pub TILE_GROUPS: u32 (measured: 1, 8) = 4
pub RUN_uSIZE: u32 (measured: 1, 8) = 2
`,
		"main.oak": `package main
cfg := import("example.com/measured/schedule/tile_config")
ROOT_uGROUPS: u32 (measured: 1, 8) = 3
main: (): i32 = i32_bits_u32(cfg.TILE_GROUPS * 10 + cfg.RUN_uSIZE + ROOT_uGROUPS)
`,
	})
}

func TestE2EImportedMeasuredConstants(t *testing.T) {
	root := importedMeasuredModule(t)
	for _, c := range []struct {
		name string
		env  map[string]string
		want int
	}{
		{"pinned", nil, 45},
		{"source names", map[string]string{"TILE_GROUPS": "6", "RUN_uSIZE": "5", "ROOT_uGROUPS": "7"}, 72},
		{"escaped aliases ignored", map[string]string{"TILE_uGROUPS": "9", "RUN_uuSIZE": "9", "ROOT_GROUPS": "9"}, 45},
	} {
		t.Run(c.name, func(t *testing.T) {
			for name, value := range c.env {
				t.Setenv("OAK_MEASURED_"+name, value)
			}
			t.Run("compiled", func(t *testing.T) {
				code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
				if abnormal || code != c.want {
					t.Fatalf("exit=(%d,%v), want %d", code, abnormal, c.want)
				}
			})
			t.Run("interpreted", func(t *testing.T) {
				if got := interpretModule(t, root); got != int64(c.want) {
					t.Fatalf("result=%d, want %d", got, c.want)
				}
			})
		})
	}
	emitted, err := New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for name, pinned := range map[string]int{"TILE_GROUPS": 4, "RUN_uSIZE": 2, "ROOT_uGROUPS": 3} {
		for _, want := range []string{
			fmt.Sprintf("oak_measured_value(%q, %dll)", name, pinned),
			fmt.Sprintf("oak_measured_out_of_range(%q, v, 1ll, 8ll)", name),
		} {
			if !strings.Contains(emitted, want) {
				t.Errorf("missing source spelling in %s", want)
			}
		}
	}
}

func TestImportedMeasuredConstantsRejectInvalidOverrides(t *testing.T) {
	root := importedMeasuredModule(t)
	model, err := New().WithPackageDir(root).Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, bad := range []string{"0", "9", "-1", "abc", "2x", "9223372036854775808"} {
		t.Run(bad, func(t *testing.T) {
			t.Setenv("OAK_MEASURED_TILE_GROUPS", bad)
			if code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root)); !abnormal {
				t.Errorf("invalid override reached main: exit %d", code)
			}
			env := object.NewEnvironment()
			env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
			result := evaluator.Eval(model.Tree.Root, env)
			failure, isError := result.(*object.Error)
			if !isError || !strings.Contains(failure.Message, "measured constant TILE_GROUPS:") {
				t.Fatalf("expected an initialization error naming TILE_GROUPS, got %v", result)
			}
		})
	}
}

func TestImportedMeasuredConstantsCustomHook(t *testing.T) {
	root := importedMeasuredModule(t)
	for _, supplied := range []int{6, 9} {
		t.Run(fmt.Sprint(supplied), func(t *testing.T) {
			helper := filepath.Join(t.TempDir(), "measured_hook.c")
			body := fmt.Sprintf(`#include <stdint.h>
#include <string.h>
int64_t oak_measured_value(const char *name, int64_t pinned) {
  return strcmp(name, "TILE_GROUPS") == 0 ? %d : pinned;
}
`, supplied)
			if err := os.WriteFile(helper, []byte(body), 0o644); err != nil {
				t.Fatal(err)
			}
			_, code, abnormal := buildAndRunFrom(t, "measured_hook", New().WithPackageDir(root), helper)
			if supplied == 6 && (abnormal || code != 65) {
				t.Fatalf("custom hook: exit=(%d,%v), want 65", code, abnormal)
			}
			if supplied == 9 && !abnormal {
				t.Fatalf("an out-of-range custom hook value reached main: exit %d", code)
			}
		})
	}
}
