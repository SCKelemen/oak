package main

import (
    "os"
    "path/filepath"
    "strings"
    "testing"
)

func TestNativeFiniteExamples(t *testing.T) {
    for _, name := range []string{"enum", "enum-broken", "counter", "counter-broken", "wrap"} {
        t.Run(name, func(t *testing.T) {
            path := filepath.Join("..", "examples", "native", name+".oak")
            source, err := os.ReadFile(path)
            if err != nil { t.Fatal(err) }
            doc, err := export(path, source)
            if err != nil { t.Fatal(err) }
            if doc.State != "State" || len(doc.Fields) != 1 || len(doc.Functions) != 3 {
                t.Fatalf("unexpected frontend document: %+v", doc)
            }
            if len(doc.SourceHash) != 64 || len(doc.Functions["step"].Params) != 2 {
                t.Fatalf("missing source identity or role parameters: %+v", doc)
            }
        })
    }
}

func TestIllTypedSourceRejected(t *testing.T) {
    source := `State: type = { count: u8 }
initial: (s: State): Bool = s.count
`
    if _, err := export("ill-typed.oak", []byte(source)); err == nil {
        t.Fatal("accepted a numeric predicate as Bool")
    }
}

func TestUnsupportedMultiplicationRejected(t *testing.T) {
    source := `State: type = { count: u8 }
initial: (s: State): Bool = s.count * u8(2) == u8(0)
`
    if _, err := export("unsupported.oak", []byte(source)); err == nil || !strings.Contains(err.Error(), "unsupported infix") {
        t.Fatalf("expected fragment rejection, got %v", err)
    }
}
