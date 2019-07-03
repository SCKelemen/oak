package object

import (
	"fmt"
	"strconv"
)

type Integer struct {
	Value int64
}

func (i *Integer) Inspect() string {
	return fmt.Sprintf("%d", i.Value)
}
func (i *Integer) Kind() ObjectKind { return INTEGER }

type Boolean struct {
	Value bool
}

func (b *Boolean) Kind() ObjectKind { return BOOLEAN }
func (b *Boolean) Inspect() string {
	return fmt.Sprintf("%t", b.Value)
}

type Null struct{}

func (n *Null) Kind() ObjectKind { return NULL }
func (n *Null) Inspect() string  { return "null" }

type ObjectKind int

type Object interface {
	Kind() ObjectKind
	Inspect() string
}

const (
	ILLEGAL ObjectKind = iota
	INTEGER
	BOOLEAN
	NULL
)

var types = [...]string{
	ILLEGAL: "ILLEGAL",
	INTEGER: "INTEGER",
	BOOLEAN: "BOOLEAN",
	NULL:    "NULL",
}

func (kind ObjectKind) String() string {
	s := ""
	if 0 <= kind && kind < ObjectKind(len(types)) {
		s = types[kind]
	}
	if s == "" {
		s = "object(" + strconv.Itoa(int(kind)) + ")"
	}
	return s
}
