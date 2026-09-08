package testrunner

import (
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
)

// A package may describe its semantic trace events in oak-trace.json so
// failures, artifacts and replay divergence read as named operations and
// fields instead of raw 64-bit payloads. The schema is documentation for
// tools: it never changes what is recorded, compared, or replayed.
const traceSchemaFile = "oak-trace.json"
const traceSchemaLimit = 1 << 20

type TraceField struct {
	Name string `json:"name"`
	// Shift and Bits select (payload >> Shift) & mask(Bits). Both zero means
	// the whole 64-bit payload.
	Shift uint              `json:"shift,omitempty"`
	Bits  uint              `json:"bits,omitempty"`
	Names map[string]string `json:"names,omitempty"`
}

type TraceEventSchema struct {
	Name string       `json:"name"`
	A    []TraceField `json:"a,omitempty"`
	B    []TraceField `json:"b,omitempty"`
}

type TraceSchema struct {
	Version int                         `json:"version"`
	Events  map[string]TraceEventSchema `json:"events"`
	byID    map[uint32]TraceEventSchema
}

// TraceDivergence names the first recorded event a strict replay did not
// reproduce. A nil side means that trace ended first.
type TraceDivergence struct {
	Index    int         `json:"index"`
	Recorded *TraceEvent `json:"recorded,omitempty"`
	Observed *TraceEvent `json:"observed,omitempty"`
}

var fieldName = regexp.MustCompile(`^[A-Za-z_][A-Za-z_0-9]*$`)

// loadTraceSchema returns nil without error when the package has no schema.
// A present schema must be valid: silently ignoring a broken one would make
// decoded output lie.
func loadTraceSchema(dir string) (*TraceSchema, error) {
	path := filepath.Join(dir, traceSchemaFile)
	f, err := os.Open(path)
	if os.IsNotExist(err) {
		return nil, nil
	}
	if err != nil {
		return nil, err
	}
	defer f.Close()
	data, err := io.ReadAll(io.LimitReader(f, traceSchemaLimit+1))
	if err != nil {
		return nil, err
	}
	if len(data) > traceSchemaLimit {
		return nil, fmt.Errorf("%s: schema exceeds %d bytes", path, traceSchemaLimit)
	}
	decoder := json.NewDecoder(strings.NewReader(string(data)))
	decoder.DisallowUnknownFields()
	var schema TraceSchema
	if err := decoder.Decode(&schema); err != nil {
		return nil, fmt.Errorf("%s: %w", path, err)
	}
	if schema.Version != 1 {
		return nil, fmt.Errorf("%s: unsupported trace schema version %d", path, schema.Version)
	}
	schema.byID = map[uint32]TraceEventSchema{}
	for key, event := range schema.Events {
		id, err := strconv.ParseUint(key, 10, 32)
		if err != nil {
			return nil, fmt.Errorf("%s: event key %q is not a u32", path, key)
		}
		if !fieldName.MatchString(event.Name) {
			return nil, fmt.Errorf("%s: event %s has an invalid name %q", path, key, event.Name)
		}
		for _, fields := range [][]TraceField{event.A, event.B} {
			for _, field := range fields {
				if !fieldName.MatchString(field.Name) {
					return nil, fmt.Errorf("%s: event %s has an invalid field name %q", path, key, field.Name)
				}
				if field.Bits > 64 || field.Shift > 63 || field.Shift+field.Bits > 64 || (field.Bits == 0 && field.Shift != 0) {
					return nil, fmt.Errorf("%s: event %s field %s selects bits outside a 64-bit payload", path, key, field.Name)
				}
				if len(field.Names) > 4096 {
					return nil, fmt.Errorf("%s: event %s field %s has too many names", path, key, field.Name)
				}
				for value := range field.Names {
					if _, err := strconv.ParseUint(value, 10, 64); err != nil {
						return nil, fmt.Errorf("%s: event %s field %s name key %q is not a u64", path, key, field.Name, value)
					}
				}
			}
		}
		schema.byID[uint32(id)] = event
	}
	return &schema, nil
}

func (f TraceField) extract(payload uint64) uint64 {
	if f.Bits == 0 {
		return payload
	}
	value := payload >> f.Shift
	if f.Bits < 64 {
		value &= (1 << f.Bits) - 1
	}
	return value
}

func describeFields(fields []TraceField, payload uint64) string {
	var parts []string
	for _, field := range fields {
		value := field.extract(payload)
		text := strconv.FormatUint(value, 10)
		if name, ok := field.Names[text]; ok {
			text = name
		}
		parts = append(parts, field.Name+"="+text)
	}
	return strings.Join(parts, " ")
}

// Describe renders one event. Unknown IDs, or a nil schema, keep the raw form
// so decoded and undecoded events are both unambiguous.
func (s *TraceSchema) Describe(e TraceEvent) string {
	raw := fmt.Sprintf("id=%d a=%d b=%d", e.ID, e.A, e.B)
	if s == nil {
		return raw
	}
	event, ok := s.byID[e.ID]
	if !ok {
		return raw
	}
	text := event.Name
	if a := describeFields(event.A, e.A); a != "" {
		text += " " + a
	} else if len(event.A) == 0 && e.A != 0 {
		text += fmt.Sprintf(" a=%d", e.A)
	}
	if b := describeFields(event.B, e.B); b != "" {
		text += " " + b
	} else if len(event.B) == 0 && e.B != 0 {
		text += fmt.Sprintf(" b=%d", e.B)
	}
	return text
}

func (s *TraceSchema) describeAll(events []TraceEvent) []string {
	if s == nil {
		return nil
	}
	out := make([]string, len(events))
	for i, e := range events {
		out[i] = s.Describe(e)
	}
	return out
}

// eventIDs lists the schema's event IDs in ascending order, for -list output.
func (s *TraceSchema) eventIDs() []uint32 {
	if s == nil {
		return nil
	}
	ids := make([]uint32, 0, len(s.byID))
	for id := range s.byID {
		ids = append(ids, id)
	}
	sort.Slice(ids, func(i, j int) bool { return ids[i] < ids[j] })
	return ids
}

// divergence finds the first position where the observed trace differs from
// the recorded one, including one trace ending early.
func divergence(recorded, observed []TraceEvent) *TraceDivergence {
	for i := 0; i < len(recorded) || i < len(observed); i++ {
		d := &TraceDivergence{Index: i}
		if i < len(recorded) {
			r := recorded[i]
			d.Recorded = &r
		}
		if i < len(observed) {
			o := observed[i]
			d.Observed = &o
		}
		if d.Recorded == nil || d.Observed == nil || *d.Recorded != *d.Observed {
			return d
		}
	}
	return nil
}
