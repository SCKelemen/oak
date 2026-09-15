package compiler

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"sort"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/nativegen"
)

// The verdict cache (docs/spec/94-assembler.md §9). A body's verdict is a
// function of what the verifier reads: the lowered assembly as the checker
// sees it, the Oak body, the bodies of the program functions the body can
// reach (the call summaries inline them), the program's type and global
// declarations, and the compiler itself. A build recomputes none of it
// when a verdict for the same key is on disk — an edit to one function
// re-verifies that function and its callers, not the program. The cache
// lives beside the solver caches under the temporary directory;
// OAK_VERIFY_CACHE=0 turns it off.

// verdictCacheDir is the directory of cached verdicts, "" when disabled.
func verdictCacheDir() string {
	if os.Getenv("OAK_VERIFY_CACHE") == "0" {
		return ""
	}
	return filepath.Join(os.TempDir(), "oak-verify-cache")
}

// verdictCacheKey hashes everything a verdict depends on.
func verdictCacheKey(asmFn *asm.Function, fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, declarations string) string {
	h := sha256.New()
	write := func(parts ...string) {
		for _, part := range parts {
			h.Write([]byte(part))
			h.Write([]byte{0})
		}
	}
	// The compiler: its executable's size and modification time, as the
	// solver caches key on it (a verifier change is a compiler change).
	if exe, err := os.Executable(); err == nil {
		if info, err := os.Stat(exe); err == nil {
			write(fmt.Sprintf("%d:%d", info.Size(), info.ModTime().UnixNano()))
		}
	}
	write("verdict-cache-1", asmFn.Arch, strconv.FormatBool(asmFn.PackedStackArgs), nativegen.Describe(asmFn), fn.String(), declarations)
	if asmFn.Body != nil {
		write("lowered-body", asmFn.Body.String()) // a verified rewrite: the body the verdict judged
	}
	globals := make([]string, 0, len(asmFn.Globals))
	for name, global := range asmFn.Globals {
		globals = append(globals, fmt.Sprintf("%s=%s/%d", name, global.Type, global.Bits))
	}
	sort.Strings(globals)
	write(globals...)
	composites := make([]string, 0, len(asmFn.Composites))
	for name, comp := range asmFn.Composites {
		composites = append(composites, fmt.Sprintf("%s=%+v", name, comp))
	}
	sort.Strings(composites)
	write(composites...)
	// The functions the body can reach through calls, transitively: every
	// identifier under the body that names a program function (an
	// over-approximation of the calls, the safe direction for a key).
	reached := map[string]bool{}
	var reach func(f *ast.FunctionStatement)
	reach = func(f *ast.FunctionStatement) {
		identifiersUnder(f.Body, func(name string) {
			callee, isFunction := functions[name]
			if !isFunction || reached[name] {
				return
			}
			reached[name] = true
			reach(callee)
		})
	}
	reach(fn)
	names := make([]string, 0, len(reached))
	for name := range reached {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		write(name, functions[name].String())
	}
	return hex.EncodeToString(h.Sum(nil))
}

// identifiersUnder visits every identifier under a node.
func identifiersUnder(node ast.Node, visit func(string)) {
	var walk func(v reflect.Value)
	walk = func(v reflect.Value) {
		switch v.Kind() {
		case reflect.Interface, reflect.Pointer:
			if v.IsNil() {
				return
			}
			if id, ok := v.Interface().(*ast.Identifier); ok {
				visit(id.Value)
				return
			}
			walk(v.Elem())
		case reflect.Struct:
			for i := 0; i < v.NumField(); i++ {
				if v.Type().Field(i).IsExported() {
					walk(v.Field(i))
				}
			}
		case reflect.Slice:
			for i := 0; i < v.Len(); i++ {
				walk(v.Index(i))
			}
		}
	}
	walk(reflect.ValueOf(node))
}

// programDeclarations is the text of the program's non-function
// statements (types, globals, constants), which every verdict may depend
// on through layouts and folded values.
func programDeclarations(root *ast.Program) string {
	var b strings.Builder
	for _, stmt := range root.Statements {
		if _, isFunction := stmt.(*ast.FunctionStatement); isFunction {
			continue
		}
		b.WriteString(stmt.String())
		b.WriteByte('\n')
	}
	return b.String()
}

// cachedVerdict reads a verdict for the key, if one is on disk.
func cachedVerdict(dir, key string) (asm.Verdict, bool) {
	if dir == "" {
		return asm.Verdict{}, false
	}
	data, err := os.ReadFile(filepath.Join(dir, key+".verdict"))
	if err != nil {
		return asm.Verdict{}, false
	}
	text := string(data)
	newline := strings.IndexByte(text, '\n')
	if newline < 0 {
		return asm.Verdict{}, false
	}
	kind, err := strconv.Atoi(text[:newline])
	if err != nil {
		return asm.Verdict{}, false
	}
	return asm.Verdict{Kind: asm.VerdictKind(kind), Message: text[newline+1:]}, true
}

// storeVerdict writes a verdict under the key (a temporary file renamed
// into place, so a concurrent build never reads a partial one).
func storeVerdict(dir, key string, verdict asm.Verdict) {
	if dir == "" {
		return
	}
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return
	}
	tmp, err := os.CreateTemp(dir, key+".*.tmp")
	if err != nil {
		return
	}
	_, writeErr := fmt.Fprintf(tmp, "%d\n%s", int(verdict.Kind), verdict.Message)
	closeErr := tmp.Close()
	if writeErr != nil || closeErr != nil {
		os.Remove(tmp.Name())
		return
	}
	if err := os.Rename(tmp.Name(), filepath.Join(dir, key+".verdict")); err != nil {
		os.Remove(tmp.Name())
	}
}
