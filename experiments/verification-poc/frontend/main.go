// The bridge reads Oak's checked AST. It does not modify or lower the program.
package main

import (
    "crypto/sha256"
    "encoding/hex"
    "encoding/json"
    "fmt"
    "os"

    "github.com/SCKelemen/oak/ast"
    "github.com/SCKelemen/oak/compiler"
    "github.com/SCKelemen/oak/typechecker"
)

type function struct {
    Params []string `json:"params"`
    Body any `json:"body"`
}
type document struct {
    Format string `json:"format"`
    SourceHash string `json:"source_sha256"`
    State string `json:"state"`
    Fields [][2]string `json:"fields"`
    Enums map[string][]string `json:"enums"`
    Functions map[string]function `json:"functions"`
}

func identifier(e ast.Expression) (string, error) {
    if i, ok := e.(*ast.Identifier); ok { return i.Value, nil }
    return "", fmt.Errorf("expected atomic type/name, got %T", e)
}

func expression(e ast.Expression) (any, error) {
    switch x := e.(type) {
    case *ast.Boolean:
        return []any{"bool", x.Value}, nil
    case *ast.IntegerLiteral:
        return []any{"integer", x.Value}, nil
    case *ast.Identifier:
        return []any{"ref", x.Value}, nil
    case *ast.IndexExpression:
        // Only dot access, never array indexing or type application.
        if x.Token.Literal != "." { return nil, fmt.Errorf("only dot member access is supported") }
        left, err := identifier(x.Left); if err != nil { return nil, err }
        right, err := identifier(x.Index); if err != nil { return nil, err }
        return []any{"member", left, right}, nil
    case *ast.VariantExpression:
        if x.TypeName == nil || x.Payload != nil { return nil, fmt.Errorf("only qualified nullary variants supported") }
        return []any{"member", x.TypeName.Value, x.Variant.Value}, nil
    case *ast.PrefixExpression:
        if x.Operator != "!" { return nil, fmt.Errorf("unsupported prefix %s", x.Operator) }
        right, err := expression(x.Right); if err != nil { return nil, err }
        return []any{"!", right}, nil
    case *ast.InfixExpression:
        switch x.Operator { case "+", "-", "==", "!=", "<", ">", "<=", ">=":
        default: return nil, fmt.Errorf("unsupported infix %s", x.Operator) }
        left, err := expression(x.Left); if err != nil { return nil, err }
        right, err := expression(x.Right); if err != nil { return nil, err }
        return []any{x.Operator, left, right}, nil
    case *ast.InvocationExpression:
        name, err := identifier(x.Function); if err != nil { return nil, err }
        args := make([]any, 0, len(x.Arguments))
        for _, a := range x.Arguments { v, err := expression(a); if err != nil { return nil, err }; args = append(args, v) }
        return []any{"call", name, args}, nil
    case *ast.MatchExpression:
        scrutinee, err := expression(x.Scrutinee); if err != nil { return nil, err }
        arms := make([]any, 0, len(x.Arms))
        for _, arm := range x.Arms {
            var pattern any
            switch p := arm.Pattern.(type) {
            case *ast.LiteralPattern:
                pattern, err = expression(p.Value)
            case *ast.VariantPattern:
                if p.TypeName == nil || p.Payload != nil { return nil, fmt.Errorf("qualified nullary pattern required") }
                pattern = []any{"member", p.TypeName.Value, p.Variant.Value}
            case *ast.WildcardPattern:
                pattern = []any{"wildcard"}
            case *ast.BindingPattern:
                if p.Name.Value != "_" { return nil, fmt.Errorf("pattern bindings unsupported") }
                pattern = []any{"wildcard"}
            default:
                return nil, fmt.Errorf("unsupported pattern %T", arm.Pattern)
            }
            if err != nil { return nil, err }
            body, err := expression(arm.Body); if err != nil { return nil, err }
            arms = append(arms, []any{pattern, body})
        }
        return []any{"match", scrutinee, arms}, nil
    case *ast.BlockExpression:
        if x.Block == nil || len(x.Block.Statements) != 1 { return nil, fmt.Errorf("only a single pure result expression is supported in a block") }
        if x.Result() == nil { return nil, fmt.Errorf("block must have a result") }
        return expression(x.Result())
    default:
        return nil, fmt.Errorf("unsupported expression %T", e)
    }
}

func export(path string, source []byte) (*document, error) {
    checked, err := compiler.New().WithSource(path, string(source)).Check().Get()
    if err != nil { return nil, err }
    hash := sha256.Sum256(source)
    d := &document{Format:"oak-finite-1", SourceHash:hex.EncodeToString(hash[:]), Fields:[][2]string{}, Enums:map[string][]string{}, Functions:map[string]function{}}
    names := map[string]bool{}
    for _, statement := range checked.Tree.Root.Statements {
        switch s := statement.(type) {
        case *ast.ADTType:
            if names[s.Name.Value] || len(s.TypeParams) != 0 { return nil, fmt.Errorf("duplicate or generic ADT") }
            names[s.Name.Value] = true
            // Oak represents record declarations as a single ADT variant
            // whose Literal is the ordered RecordLiteral (compiler convention).
            if len(s.Variants) == 1 {
                if record, ok := s.Variants[0].Literal.(*ast.RecordLiteral); ok {
                    if d.State != "" { return nil, fmt.Errorf("exactly one state record required") }
                    d.State = s.Name.Value
                    for _, field := range record.FieldOrder {
                        typ, err := identifier(field.Value); if err != nil { return nil, err }
                        if checked.TypeChecker.ParseTypeExpression(field.Value) == nil { return nil, fmt.Errorf("unresolved field type") }
                        d.Fields = append(d.Fields, [2]string{field.Name, typ})
                    }
                    continue
                }
            }
            cases := []string{}
            for _, v := range s.Variants {
                if v.Payload != nil || v.Literal != nil || v.Result != nil { return nil, fmt.Errorf("only nullary non-indexed ADTs supported") }
                cases = append(cases, v.Name.Value)
            }
            d.Enums[s.Name.Value] = cases
        case *ast.VariableDeclaration:
            typ, err := identifier(s.Type); if err != nil || typ != "type" { return nil, fmt.Errorf("only type declarations allowed at top level") }
            record, ok := s.Value.(*ast.RecordLiteral); if !ok || d.State != "" || names[s.Name.Value] { return nil, fmt.Errorf("exactly one record type required") }
            names[s.Name.Value] = true; d.State = s.Name.Value
            for _, field := range record.FieldOrder {
                typ, err := identifier(field.Value); if err != nil { return nil, err }
                resolved := checked.TypeChecker.ParseTypeExpression(field.Value)
                if resolved == nil { return nil, fmt.Errorf("unresolved field type") }
                // Keep the nominal source name; Oak's check has already resolved it.
                d.Fields = append(d.Fields, [2]string{field.Name, typ})
            }
        case *ast.FunctionStatement:
            if s.Receiver != nil || len(s.TypeParams) != 0 || s.ExternSymbol != "" || names[s.Name.Value] { return nil, fmt.Errorf("unsupported function declaration") }
            names[s.Name.Value] = true
            typ, ok := checked.TypeChecker.Env().GetType(s.Name.Value)
            ft, okFn := typ.(*typechecker.FunctionType)
            if !ok || !okFn || !ft.ReturnType.Equals(&typechecker.BoolType{}) { return nil, fmt.Errorf("predicate must have checked Bool result") }
            params := []string{}
            for _, p := range s.Parameters {
                t, err := identifier(p.Type); if err != nil || t != d.State || p.Variadic { return nil, fmt.Errorf("predicate parameters must be the state record") }
                params = append(params, p.Name.Value)
            }
            body, err := expression(s.Body); if err != nil { return nil, err }
            d.Functions[s.Name.Value] = function{params, body}
        default:
            return nil, fmt.Errorf("unsupported top-level statement %T", statement)
        }
    }
    if d.State == "" || len(d.Fields) == 0 { return nil, fmt.Errorf("missing state record") }
    return d, nil
}

func main() {
    if len(os.Args) != 2 { fmt.Fprintln(os.Stderr, "usage: frontend MODEL.oak"); os.Exit(2) }
    bytes, err := os.ReadFile(os.Args[1]); if err != nil { fmt.Fprintln(os.Stderr, err); os.Exit(2) }
    d, err := export(os.Args[1], bytes); if err != nil { fmt.Fprintln(os.Stderr, err); os.Exit(2) }
    if err := json.NewEncoder(os.Stdout).Encode(d); err != nil { fmt.Fprintln(os.Stderr, err); os.Exit(2) }
}
