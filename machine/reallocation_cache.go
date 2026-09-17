package machine

import (
	"encoding/binary"
	"fmt"
	"math"
	"os"
	"reflect"
	"sync"

	"github.com/SCKelemen/oak/asm"
)

// ReallocationSummary retains reporting counts, never allocation webs.
type ReallocationSummary struct{ Sites, Promoted int }

// ReallocationCacheStats counts requests, successful lookups and retained
// entries. PayloadBytes is canonical input plus output size, not Go heap size.
type ReallocationCacheStats struct{ Requests, Hits, Entries, PayloadBytes int }

const (
	reallocationCacheEntries = 32
	reallocationCacheBytes   = 16 << 20
)

// ReallocationCache is a bounded compilation-local memo of successful
// ReallocateWith results. Its zero value is ready to use. Keys include only
// the machine decision inputs; entries retain no function, AST, map, web,
// or allocation object. A hit attaches fresh payload copies to the current
// caller's metadata, so this cache supplies no semantic-verification authority.
type ReallocationCache struct {
	mu      sync.Mutex
	entries map[string]reallocationPayload
	stats   ReallocationCacheStats
}

type reallocationDecision struct {
	Arch     string
	Frame    int64
	Items    []asm.Item
	Clobbers []asm.Register
	Objects  []FrameObject
}

type reallocationPayload struct {
	Items    []asm.Item
	Clobbers []asm.Register
	Summary  ReallocationSummary
}

// Stats returns an independent snapshot; a nil receiver has no cache.
func (c *ReallocationCache) Stats() ReallocationCacheStats {
	if c == nil {
		return ReallocationCacheStats{}
	}
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.stats
}

// Apply reuses only an exact canonical machine-input match. Trace mode,
// unsupported key shapes and capacity exhaustion take the ordinary path;
// errors are returned unchanged and are never cached. A nil receiver is
// an explicit uncached path.
func (c *ReallocationCache) Apply(fn *asm.Function, objects []FrameObject) (*asm.Function, ReallocationSummary, error) {
	if c != nil {
		c.mu.Lock()
		c.stats.Requests++
		c.mu.Unlock()
	}
	if fn == nil {
		return nil, ReallocationSummary{}, fmt.Errorf("machine: no function")
	}
	if c == nil || os.Getenv("OAK_MACHINE_TRACE_SLOTS") != "" {
		return reallocateSummary(fn, objects)
	}
	input, encodable := encodeReallocation(reallocationDecision{
		Arch: fn.Arch, Frame: fn.Frame, Items: fn.Items, Clobbers: fn.Clobbers, Objects: objects,
	}, reallocationCacheBytes)
	if !encodable {
		return reallocateSummary(fn, objects)
	}
	// The entire canonical string is the key: no digest collision can
	// authorize reusing a different machine body.
	key := string(input)
	c.mu.Lock()
	if payload, found := c.entries[key]; found {
		c.stats.Hits++
		c.mu.Unlock()
		out := *fn
		out.Items, out.Clobbers = cloneReallocationPayload(payload.Items, payload.Clobbers)
		return &out, payload.Summary, nil
	}
	room := c.stats.Entries < reallocationCacheEntries && len(key) < reallocationCacheBytes-c.stats.PayloadBytes
	c.mu.Unlock()
	out, summary, err := reallocateSummary(fn, objects)
	if err != nil || !room {
		return out, summary, err
	}
	payload := reallocationPayload{Items: out.Items, Clobbers: out.Clobbers, Summary: summary}
	encoded, encodable := encodeReallocation(payload, reallocationCacheBytes-len(key))
	if !encodable {
		return out, summary, nil
	}
	size := len(key) + len(encoded)
	c.mu.Lock()
	defer c.mu.Unlock()
	if _, found := c.entries[key]; !found && c.stats.Entries < reallocationCacheEntries && size <= reallocationCacheBytes-c.stats.PayloadBytes {
		payload.Items, payload.Clobbers = cloneReallocationPayload(payload.Items, payload.Clobbers)
		if c.entries == nil {
			c.entries = make(map[string]reallocationPayload)
		}
		c.entries[key] = payload
		c.stats.Entries++
		c.stats.PayloadBytes += size
	}
	return out, summary, nil
}

func reallocateSummary(fn *asm.Function, objects []FrameObject) (*asm.Function, ReallocationSummary, error) {
	out, allocation, err := ReallocateWith(fn, objects)
	if err != nil {
		return out, ReallocationSummary{}, err
	}
	return out, ReallocationSummary{Sites: allocation.Sites(), Promoted: allocation.Promoted}, nil
}

// This copies every mutable descendant of the closed assembly payload.
// All other admitted item/operand values contain only scalar values.
func cloneReallocationPayload(items []asm.Item, clobbers []asm.Register) ([]asm.Item, []asm.Register) {
	var copiedItems []asm.Item
	if items != nil {
		copiedItems = make([]asm.Item, len(items))
		for i, item := range items {
			if instruction, ok := item.(asm.Instruction); ok {
				if instruction.Operands != nil {
					operands := make([]asm.Operand, len(instruction.Operands))
					for j, operand := range instruction.Operands {
						switch value := operand.(type) {
						case asm.Memory:
							if value.Index != nil {
								index := *value.Index
								value.Index = &index
							}
							operand = value
						case asm.RegisterList:
							value.Regs = cloneReallocationRegisters(value.Regs)
							operand = value
						}
						operands[j] = operand
					}
					instruction.Operands = operands
				}
				if instruction.CheckedFacts != nil {
					facts := make([]asm.CheckedFactRef, len(instruction.CheckedFacts))
					copy(facts, instruction.CheckedFacts)
					instruction.CheckedFacts = facts
				}
				item = instruction
			}
			copiedItems[i] = item
		}
	}
	return copiedItems, cloneReallocationRegisters(clobbers)
}

func cloneReallocationRegisters(registers []asm.Register) []asm.Register {
	if registers == nil {
		return nil
	}
	out := make([]asm.Register, len(registers))
	copy(out, registers)
	return out
}

// Closed traversal: not a generic object serializer. Each allowed dynamic
// type has a distinct tag, and all fields of admitted structs are visited.
// Any new pointer, map, slice or named type must be reviewed explicitly;
// the complete asm.Function (and therefore frontend syntax) is excluded.
var reallocationEncodingTypes = func() map[reflect.Type]uint64 {
	types := []reflect.Type{
		reflect.TypeOf(reallocationDecision{}), reflect.TypeOf(reallocationPayload{}), reflect.TypeOf(ReallocationSummary{}),
		reflect.TypeOf(asm.Instruction{}), reflect.TypeOf(asm.Label{}), reflect.TypeOf(asm.Align{}),
		reflect.TypeOf(asm.Register{}), reflect.TypeOf(asm.Memory{}), reflect.TypeOf(asm.RegisterList{}),
		reflect.TypeOf(asm.Immediate{}), reflect.TypeOf(asm.FloatImmediate{}), reflect.TypeOf(asm.Symbol{}),
		reflect.TypeOf(asm.Condition{}), reflect.TypeOf(asm.Option{}), reflect.TypeOf(asm.SysReg{}),
		reflect.TypeOf(asm.Shifted{}), reflect.TypeOf(asm.Extended{}), reflect.TypeOf(asm.TileSlice{}),
		reflect.TypeOf(asm.CheckedFactRef{}), reflect.TypeOf(asm.FrameObject{}),
		reflect.TypeOf(asm.RegClass(0)), reflect.TypeOf(asm.MemMode(0)),
		reflect.TypeOf((*asm.Item)(nil)).Elem(), reflect.TypeOf((*asm.Operand)(nil)).Elem(),
		reflect.TypeOf((*asm.Register)(nil)),
		reflect.TypeOf([]asm.Item(nil)), reflect.TypeOf([]asm.Operand(nil)), reflect.TypeOf([]asm.Register(nil)),
		reflect.TypeOf([]asm.CheckedFactRef(nil)), reflect.TypeOf([]FrameObject(nil)),
		reflect.TypeOf(false), reflect.TypeOf(""), reflect.TypeOf(float64(0)),
		reflect.TypeOf(int(0)), reflect.TypeOf(int8(0)), reflect.TypeOf(int16(0)), reflect.TypeOf(int32(0)), reflect.TypeOf(int64(0)),
		reflect.TypeOf(uint(0)), reflect.TypeOf(uint8(0)), reflect.TypeOf(uint16(0)), reflect.TypeOf(uint32(0)), reflect.TypeOf(uint64(0)),
	}
	out := make(map[reflect.Type]uint64, len(types))
	for i, typ := range types {
		out[typ] = uint64(i) + 1 // no narrowing or wrapping one-byte type tags
	}
	return out
}()

// Reject struct extensions until the key and payload copier are reviewed
// together, even if a new field happens to use an already allowed type.
var reallocationEncodingFields = map[reflect.Type]int{
	reflect.TypeOf(reallocationDecision{}): 5, reflect.TypeOf(reallocationPayload{}): 3, reflect.TypeOf(ReallocationSummary{}): 2,
	reflect.TypeOf(asm.Instruction{}): 6, reflect.TypeOf(asm.Label{}): 2, reflect.TypeOf(asm.Align{}): 2,
	reflect.TypeOf(asm.Register{}): 6, reflect.TypeOf(asm.Memory{}): 7, reflect.TypeOf(asm.RegisterList{}): 1,
	reflect.TypeOf(asm.Immediate{}): 3, reflect.TypeOf(asm.FloatImmediate{}): 1, reflect.TypeOf(asm.Symbol{}): 2,
	reflect.TypeOf(asm.Condition{}): 1, reflect.TypeOf(asm.Option{}): 2, reflect.TypeOf(asm.SysReg{}): 1,
	reflect.TypeOf(asm.Shifted{}): 3, reflect.TypeOf(asm.Extended{}): 3, reflect.TypeOf(asm.TileSlice{}): 9,
	reflect.TypeOf(asm.CheckedFactRef{}): 5, reflect.TypeOf(asm.FrameObject{}): 4,
}

type reallocationEncoder struct {
	bytes []byte
	limit int
}

func encodeReallocation(value any, limit int) ([]byte, bool) {
	encoder := reallocationEncoder{limit: limit}
	if limit < 0 || !encoder.value(reflect.ValueOf(value)) {
		return nil, false
	}
	return encoder.bytes, true
}

// reserve bounds capacity during traversal, including rejected oversized
// inputs. Ordinary append growth could otherwise exceed the payload cap.
func (e *reallocationEncoder) reserve(count int) bool {
	if count < 0 || count > e.limit-len(e.bytes) {
		return false
	}
	required := len(e.bytes) + count
	if required > cap(e.bytes) {
		capacity := cap(e.bytes) * 2
		if capacity < required {
			capacity = required
		}
		if capacity > e.limit {
			capacity = e.limit
		}
		grown := make([]byte, len(e.bytes), capacity)
		copy(grown, e.bytes)
		e.bytes = grown
	}
	return true
}

func (e *reallocationEncoder) number(value uint64) bool {
	var bytes [binary.MaxVarintLen64]byte
	count := binary.PutUvarint(bytes[:], value)
	if !e.reserve(count) {
		return false
	}
	e.bytes = append(e.bytes, bytes[:count]...)
	return true
}

func (e *reallocationEncoder) value(value reflect.Value) bool {
	if !value.IsValid() {
		return false
	}
	tag, allowed := reallocationEncodingTypes[value.Type()]
	if !allowed || !e.number(tag) {
		return false
	}
	switch value.Kind() {
	case reflect.Interface:
		if value.IsNil() {
			return e.number(0)
		}
		// Item and Operand implementations are the closed value structs,
		// never pointers (including a typed nil *Register operand).
		return value.Elem().Kind() == reflect.Struct && e.number(1) && e.value(value.Elem())
	case reflect.Pointer:
		if value.IsNil() {
			return e.number(0)
		}
		return e.number(1) && e.value(value.Elem())
	case reflect.Slice:
		if value.IsNil() {
			return e.number(0)
		}
		if !e.number(1) || !e.number(uint64(value.Len())) {
			return false
		}
		for i := 0; i < value.Len(); i++ {
			if !e.value(value.Index(i)) {
				return false
			}
		}
		return true
	case reflect.Struct:
		if fields, known := reallocationEncodingFields[value.Type()]; !known || fields != value.NumField() || !e.number(uint64(fields)) {
			return false
		}
		for i := 0; i < value.NumField(); i++ {
			if value.Type().Field(i).PkgPath != "" || !e.value(value.Field(i)) {
				return false
			}
		}
		return true
	case reflect.String:
		text := value.String()
		if !e.number(uint64(len(text))) || !e.reserve(len(text)) {
			return false
		}
		e.bytes = append(e.bytes, text...) // raw bytes, including invalid UTF-8
		return true
	case reflect.Bool:
		if value.Bool() {
			return e.number(1)
		}
		return e.number(0)
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		return e.number(uint64(value.Int()))
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
		return e.number(value.Uint())
	case reflect.Float64:
		return e.number(math.Float64bits(value.Float()))
	default:
		return false
	}
}
