package compiler

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
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

const (
	verdictCacheNamespace     = "verdict-cache-2"
	verdictCacheFormatVersion = 2
)

type storedVerdict struct {
	Version int             `json:"version"`
	Kind    asm.VerdictKind `json:"kind"`
	Message string          `json:"message"`
	Callees []string        `json:"callees"`
}

// decodedVerdict uses pointers so a missing or null field cannot silently
// become the zero value. In particular, every cache entry must state its
// callee dependency list even when that list is empty.
type decodedVerdict struct {
	Version *int             `json:"version"`
	Kind    *asm.VerdictKind `json:"kind"`
	Message *string          `json:"message"`
	Callees *[]string        `json:"callees"`
}

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
	if os.Getenv("OAK_VERIFY_CACHE") == "0" || os.Getenv("OAK_VERIFY_ONLY") != "" {
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
	write(verdictCacheNamespace, asmFn.Arch, strconv.FormatBool(asmFn.PackedStackArgs), nativegen.Describe(asmFn), fn.String(), declarations)
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
	// Candidate construction is untrusted. Include every known Oak function
	// named by a direct machine call even when the original source body did not
	// call it: asm.Verify may summarize that callee and make this verdict depend
	// on its semantic body. Unreachable calls are harmless over-approximation.
	for _, item := range asmFn.Items {
		instruction, ok := item.(asm.Instruction)
		if !ok || (instruction.Mnemonic != "bl" && instruction.Mnemonic != "call") || len(instruction.Operands) == 0 {
			continue
		}
		symbol, ok := instruction.Operands[0].(asm.Symbol)
		if !ok {
			continue
		}
		name := symbol.Name
		callee := functions[name]
		if callee == nil {
			if base, suffixed := strings.CutSuffix(name, asm.VectorEntrySuffix(asmFn.Arch)); suffixed {
				name, callee = base, functions[base]
			}
		}
		if callee == nil || reached[name] {
			continue
		}
		reached[name] = true
		reach(callee)
	}
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
func cachedVerdict(dir, key string, functions map[string]*ast.FunctionStatement) (asm.Verdict, bool) {
	if dir == "" || !validVerdictCacheKey(key) {
		return asm.Verdict{}, false
	}
	data, err := os.ReadFile(filepath.Join(dir, key+".verdict"))
	if err != nil {
		return asm.Verdict{}, false
	}
	var stored decodedVerdict
	decoder := json.NewDecoder(bytes.NewReader(data))
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(&stored); err != nil {
		return asm.Verdict{}, false
	}
	if err := decoder.Decode(&struct{}{}); err != io.EOF {
		return asm.Verdict{}, false
	}
	if stored.Version == nil || *stored.Version != verdictCacheFormatVersion ||
		stored.Kind == nil || !validVerdictKind(*stored.Kind) ||
		stored.Message == nil || stored.Callees == nil ||
		!validVerdictCallees(*stored.Callees, functions, true) {
		return asm.Verdict{}, false
	}
	return asm.Verdict{
		Kind:    *stored.Kind,
		Message: *stored.Message,
		Callees: append([]string(nil), (*stored.Callees)...),
	}, true
}

// storeVerdict writes a verdict under the key (a temporary file renamed
// into place, so a concurrent build never reads a partial one).
func storeVerdict(dir, key string, verdict asm.Verdict) {
	if dir == "" || !validVerdictCacheKey(key) || !validVerdictKind(verdict.Kind) ||
		!validVerdictCallees(verdict.Callees, nil, false) {
		return
	}
	data, err := json.Marshal(storedVerdict{
		Version: verdictCacheFormatVersion,
		Kind:    verdict.Kind,
		Message: verdict.Message,
		Callees: append([]string{}, verdict.Callees...),
	})
	if err != nil {
		return
	}
	if err := os.MkdirAll(dir, 0o700); err != nil {
		return
	}
	tmp, err := os.CreateTemp(dir, key+".*.tmp")
	if err != nil {
		return
	}
	_, writeErr := tmp.Write(data)
	closeErr := tmp.Close()
	if writeErr != nil || closeErr != nil {
		os.Remove(tmp.Name())
		return
	}
	if err := os.Rename(tmp.Name(), filepath.Join(dir, key+".verdict")); err != nil {
		os.Remove(tmp.Name())
	}
}

func validVerdictCacheKey(key string) bool {
	if len(key) != sha256.Size*2 {
		return false
	}
	_, err := hex.DecodeString(key)
	return err == nil
}

func validVerdictKind(kind asm.VerdictKind) bool {
	switch kind {
	case asm.VerdictTrusted, asm.VerdictProven, asm.VerdictWitnessed, asm.VerdictMismatch:
		return true
	default:
		return false
	}
}

func validVerdictCallees(callees []string, functions map[string]*ast.FunctionStatement, requireKnown bool) bool {
	seen := make(map[string]bool, len(callees))
	for _, name := range callees {
		if name == "" || seen[name] || (requireKnown && functions[name] == nil) {
			return false
		}
		seen[name] = true
	}
	return true
}
