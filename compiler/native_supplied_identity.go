package compiler

import (
	"crypto/sha256"
	"encoding/hex"
	"io"
	"math"
	"reflect"
	"sort"
	"strconv"

	"github.com/SCKelemen/oak/asm"
)

// nativeSuppliedBody is a bounded observation of the selected machine body and
// its physical ABI/encoding metadata. It is NOT a semantic proof-cache key.
// The checked declaration and complete source/compiler/target recipe bind the
// surrounding Oak types, globals and callees separately. Never serialize that
// whole-program AST context once per supplied unit here.
//
// TestNativeSuppliedIdentityClassifiesFunctionFields requires every Function
// field to be covered here or explicitly classified at that boundary.
type nativeSuppliedBody struct {
	Name            string
	Arch            string
	Inert           bool
	Items           []asm.Item
	Bindings        []asm.Binding
	Clobbers        []asm.Register
	Frame           int64
	System          bool
	Align           int64
	Compressed      bool
	CompressedSet   bool
	FloatFile       bool
	VectorFile      bool
	Fallback        bool
	Composites      map[string]asm.Composite
	StackArgs       int64
	PackedStackArgs bool
	TwoChunkResults map[string]bool
	FrameObjects    []asm.FrameObject
	ResultSlot      string
}

func nativeSuppliedBodyDigest(fn *asm.Function) string {
	if fn == nil {
		return ""
	}
	body := nativeSuppliedBody{
		Name: fn.Name, Arch: fn.Arch, Inert: fn.Inert, Items: fn.Items,
		Bindings: fn.Bindings, Clobbers: fn.Clobbers, Frame: fn.Frame,
		System: fn.System, Align: fn.Align, Compressed: fn.Compressed,
		CompressedSet: fn.CompressedSet, FloatFile: fn.FloatFile,
		VectorFile: fn.VectorFile, Fallback: fn.Fallback, Composites: fn.Composites,
		StackArgs: fn.StackArgs, PackedStackArgs: fn.PackedStackArgs,
		TwoChunkResults: fn.TwoChunkResults, FrameObjects: fn.FrameObjects,
		ResultSlot: fn.ResultSlot,
	}
	digest := sha256.New()
	writeNativeMaterializationPart(digest, "oak.native.supplied-body.v1")
	if !writeNativeSuppliedValue(digest, reflect.ValueOf(body)) {
		return "" // Unsupported future data cannot produce a valid receipt identity.
	}
	return hex.EncodeToString(digest.Sum(nil))
}

// Preserve concrete Item and Operand types as well as every typed field;
// diagnostic String/Describe methods intentionally omit encoding metadata.
// Length framing, explicit nils, deterministic maps and exact finite floating
// point bits avoid ambiguous spellings and pointer-dependent identities.
func writeNativeSuppliedValue(out io.Writer, value reflect.Value) bool {
	return writeNativeSuppliedValueAt(out, value, 0)
}

func writeNativeSuppliedValueAt(out io.Writer, value reflect.Value, depth int) bool {
	if !value.IsValid() || depth > 32 {
		return false
	}
	write := func(parts ...string) { writeNativeMaterializationPart(out, parts...) }
	write(value.Type().PkgPath(), value.Type().String())
	switch value.Kind() {
	case reflect.Interface, reflect.Pointer:
		if value.IsNil() {
			write("nil")
			return true
		}
		write("value")
		return writeNativeSuppliedValueAt(out, value.Elem(), depth+1)
	case reflect.Struct:
		write(strconv.Itoa(value.NumField()))
		for i := 0; i < value.NumField(); i++ {
			field := value.Type().Field(i)
			if field.PkgPath != "" {
				return false
			}
			write(field.Name)
			if !writeNativeSuppliedValueAt(out, value.Field(i), depth+1) {
				return false
			}
		}
	case reflect.Slice:
		if value.IsNil() {
			write("nil")
			return true
		}
		write(strconv.Itoa(value.Len()))
		for i := 0; i < value.Len(); i++ {
			if !writeNativeSuppliedValueAt(out, value.Index(i), depth+1) {
				return false
			}
		}
	case reflect.Map:
		if value.Type().Key().Kind() != reflect.String {
			return false
		}
		if value.IsNil() {
			write("nil")
			return true
		}
		keys := value.MapKeys()
		sort.Slice(keys, func(i, j int) bool { return keys[i].String() < keys[j].String() })
		write(strconv.Itoa(len(keys)))
		for _, key := range keys {
			write(key.String())
			if !writeNativeSuppliedValueAt(out, value.MapIndex(key), depth+1) {
				return false
			}
		}
	case reflect.String:
		write(value.String())
	case reflect.Bool:
		write(strconv.FormatBool(value.Bool()))
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		write(strconv.FormatInt(value.Int(), 10))
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
		write(strconv.FormatUint(value.Uint(), 10))
	case reflect.Float64:
		f := value.Float()
		if math.IsInf(f, 0) || math.IsNaN(f) {
			return false
		}
		write(strconv.FormatUint(math.Float64bits(f), 16))
	default:
		return false
	}
	return true
}
