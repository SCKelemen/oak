package serialize

import (
	"bufio"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// JSONLWriter writes JSON Lines format
type JSONLWriter struct {
	writer *bufio.Writer
	file   *os.File
}

// NewJSONLWriter creates a new JSONL writer
func NewJSONLWriter(filePath string) (*JSONLWriter, error) {
	// Create directory if it doesn't exist
	dir := filepath.Dir(filePath)
	if err := os.MkdirAll(dir, 0755); err != nil {
		return nil, fmt.Errorf("failed to create directory: %w", err)
	}

	file, err := os.Create(filePath)
	if err != nil {
		return nil, fmt.Errorf("failed to create file: %w", err)
	}

	return &JSONLWriter{
		writer: bufio.NewWriter(file),
		file:   file,
	}, nil
}

// WriteLine writes a single JSON object as a line
func (w *JSONLWriter) WriteLine(obj interface{}) error {
	data, err := json.Marshal(obj)
	if err != nil {
		return fmt.Errorf("failed to marshal JSON: %w", err)
	}

	if _, err := w.writer.Write(data); err != nil {
		return fmt.Errorf("failed to write data: %w", err)
	}

	if _, err := w.writer.WriteString("\n"); err != nil {
		return fmt.Errorf("failed to write newline: %w", err)
	}

	return nil
}

// Close closes the writer and flushes any buffered data
func (w *JSONLWriter) Close() error {
	if err := w.writer.Flush(); err != nil {
		return fmt.Errorf("failed to flush buffer: %w", err)
	}
	return w.file.Close()
}

// TokenJSON represents a token in JSON format
type TokenJSON struct {
	Kind      string `json:"kind"`
	Literal   string `json:"literal"`
	Line      int    `json:"line"`
	Column    int    `json:"column"`
	ByteStart int    `json:"byte_start"`
	ByteEnd   int    `json:"byte_end"`
}

// SerializeTokens writes tokens to a JSONL file
func SerializeTokens(tokens []token.Token, outputPath string) error {
	writer, err := NewJSONLWriter(outputPath)
	if err != nil {
		return err
	}
	defer writer.Close()

	for _, tok := range tokens {
		tokenJSON := TokenJSON{
			Kind:      tok.TokenKind.String(),
			Literal:   tok.Literal,
			Line:      tok.Line,
			Column:    tok.Column,
			ByteStart: tok.ByteStart,
			ByteEnd:   tok.ByteEnd,
		}

		if err := writer.WriteLine(tokenJSON); err != nil {
			return fmt.Errorf("failed to write token: %w", err)
		}
	}

	return nil
}

// ASTNodeJSON represents an AST node in JSON format
type ASTNodeJSON struct {
	Type     string                 `json:"type"`
	Data     map[string]interface{} `json:"data"`
	Position *PositionJSON          `json:"position,omitempty"`
}

// PositionJSON represents source position information
type PositionJSON struct {
	Line      int `json:"line,omitempty"`
	Column    int `json:"column,omitempty"`
	ByteStart int `json:"byte_start,omitempty"`
	ByteEnd   int `json:"byte_end,omitempty"`
}

// SerializeAST writes AST nodes to a JSONL file
func SerializeAST(program *ast.Program, outputPath string) error {
	writer, err := NewJSONLWriter(outputPath)
	if err != nil {
		return err
	}
	defer writer.Close()

	// Write program metadata
	programJSON := ASTNodeJSON{
		Type: "Program",
		Data: map[string]interface{}{
			"statement_count": len(program.Statements),
		},
	}
	if err := writer.WriteLine(programJSON); err != nil {
		return fmt.Errorf("failed to write program: %w", err)
	}

	// Serialize each statement
	for _, stmt := range program.Statements {
		nodeJSON, err := serializeNode(stmt)
		if err != nil {
			return fmt.Errorf("failed to serialize statement: %w", err)
		}
		if err := writer.WriteLine(nodeJSON); err != nil {
			return fmt.Errorf("failed to write statement: %w", err)
		}
	}

	return nil
}

// serializeNode converts an AST node to JSON format
func serializeNode(node ast.Node) (ASTNodeJSON, error) {
	if node == nil {
		return ASTNodeJSON{
			Type: "nil",
			Data: map[string]interface{}{"error": "nil node"},
		}, nil
	}

	nodeJSON := ASTNodeJSON{
		Type: getNodeType(node),
		Data: make(map[string]interface{}),
	}

	// Add position information if available
	if pos := getNodePosition(node); pos != nil {
		nodeJSON.Position = pos
	}

	// Serialize node-specific data
	switch n := node.(type) {
	case *ast.Program:
		nodeJSON.Data["statement_count"] = len(n.Statements)

	case *ast.Identifier:
		nodeJSON.Data["value"] = n.Value

	case *ast.IntegerLiteral:
		nodeJSON.Data["value"] = n.Value

	case *ast.StringLiteral:
		nodeJSON.Data["value"] = n.Value

	case *ast.Boolean:
		nodeJSON.Data["value"] = n.Value

	case *ast.VariableDeclaration:
		if n.Name != nil {
			nodeJSON.Data["name"] = n.Name.Value
		}
		if n.Type != nil {
			typeStr, err := serializeTypeExpression(n.Type)
			if err != nil {
				return ASTNodeJSON{}, err
			}
			nodeJSON.Data["type"] = typeStr
		}
		if n.Value != nil {
			valueJSON, err := serializeNode(n.Value)
			if err != nil {
				return ASTNodeJSON{}, err
			}
			nodeJSON.Data["value"] = valueJSON
		}

	case *ast.ExpressionStatement:
		exprJSON, err := serializeNode(n.Expression)
		if err != nil {
			return ASTNodeJSON{}, err
		}
		nodeJSON.Data["expression"] = exprJSON

	case *ast.PrefixExpression:
		nodeJSON.Data["operator"] = n.Operator
		rightJSON, err := serializeNode(n.Right)
		if err != nil {
			return ASTNodeJSON{}, err
		}
		nodeJSON.Data["right"] = rightJSON

	case *ast.InfixExpression:
		nodeJSON.Data["operator"] = n.Operator
		leftJSON, err := serializeNode(n.Left)
		if err != nil {
			return ASTNodeJSON{}, err
		}
		nodeJSON.Data["left"] = leftJSON
		rightJSON, err := serializeNode(n.Right)
		if err != nil {
			return ASTNodeJSON{}, err
		}
		nodeJSON.Data["right"] = rightJSON

	case *ast.IndexExpression:
		leftJSON, err := serializeNode(n.Left)
		if err != nil {
			return ASTNodeJSON{}, err
		}
		nodeJSON.Data["left"] = leftJSON
		indexJSON, err := serializeNode(n.Index)
		if err != nil {
			return ASTNodeJSON{}, err
		}
		nodeJSON.Data["index"] = indexJSON

	case *ast.SliceExpression:
		seqJSON, err := serializeNode(n.Seq)
		if err != nil {
			return ASTNodeJSON{}, err
		}
		nodeJSON.Data["seq"] = seqJSON
		if n.Low != nil {
			lowJSON, err := serializeNode(n.Low)
			if err != nil {
				return ASTNodeJSON{}, err
			}
			nodeJSON.Data["low"] = lowJSON
		}
		if n.High != nil {
			highJSON, err := serializeNode(n.High)
			if err != nil {
				return ASTNodeJSON{}, err
			}
			nodeJSON.Data["high"] = highJSON
		}

	case *ast.ArrayLiteral:
		elements := make([]ASTNodeJSON, 0, len(n.Elements))
		for _, elem := range n.Elements {
			elemJSON, err := serializeNode(elem)
			if err != nil {
				return ASTNodeJSON{}, err
			}
			elements = append(elements, elemJSON)
		}
		nodeJSON.Data["elements"] = elements
		if n.Type != nil {
			typeStr, err := serializeTypeExpression(n.Type)
			if err != nil {
				return ASTNodeJSON{}, err
			}
			nodeJSON.Data["type"] = typeStr
		}

	case *ast.RecordLiteral:
		fields := make(map[string]ASTNodeJSON)
		for name, expr := range n.Fields {
			exprJSON, err := serializeNode(expr)
			if err != nil {
				return ASTNodeJSON{}, err
			}
			fields[name] = exprJSON
		}
		nodeJSON.Data["fields"] = fields
		if n.TypeName != nil {
			nodeJSON.Data["type_name"] = n.TypeName.Value
		}

	case *ast.FunctionStatement:
		if n == nil {
			break
		}
		if n.Name != nil {
			nodeJSON.Data["name"] = n.Name.Value
		}
		if n.Receiver != nil && n.Receiver.Name != nil {
			receiverData := map[string]interface{}{
				"name": n.Receiver.Name.Value,
			}
			if n.Receiver.Type != nil {
				typeStr, err := serializeTypeExpression(n.Receiver.Type)
				if err != nil {
					return ASTNodeJSON{}, err
				}
				receiverData["type"] = typeStr
			}
			nodeJSON.Data["receiver"] = receiverData
		}
		if n.Parameters != nil {
			params := make([]map[string]interface{}, 0, len(n.Parameters))
			for _, param := range n.Parameters {
				if param == nil {
					continue
				}
				paramData := map[string]interface{}{}
				if param.Name != nil {
					paramData["name"] = param.Name.Value
				}
				if param.Type != nil {
					typeStr, err := serializeTypeExpression(param.Type)
					if err != nil {
						return ASTNodeJSON{}, err
					}
					paramData["type"] = typeStr
				}
				params = append(params, paramData)
			}
			nodeJSON.Data["parameters"] = params
		}
		if n.ReturnType != nil {
			returnTypeStr, err := serializeTypeExpression(n.ReturnType)
			if err != nil {
				return ASTNodeJSON{}, err
			}
			nodeJSON.Data["return_type"] = returnTypeStr
		}
		if n.Body != nil {
			bodyJSON, err := serializeNode(n.Body)
			if err != nil {
				return ASTNodeJSON{}, err
			}
			nodeJSON.Data["body"] = bodyJSON
		}

	case *ast.BlockStatement:
		statements := make([]ASTNodeJSON, 0, len(n.Statements))
		for _, stmt := range n.Statements {
			stmtJSON, err := serializeNode(stmt)
			if err != nil {
				return ASTNodeJSON{}, err
			}
			statements = append(statements, stmtJSON)
		}
		nodeJSON.Data["statements"] = statements

	case *ast.ADTType:
		if n.Name != nil {
			nodeJSON.Data["name"] = n.Name.Value
		}
		variants := make([]map[string]interface{}, 0, len(n.Variants))
		for _, variant := range n.Variants {
			variantData := map[string]interface{}{
				"name": variant.Name.Value,
			}
			if variant.Payload != nil {
				payloadJSON, err := serializeNode(variant.Payload)
				if err != nil {
					return ASTNodeJSON{}, err
				}
				variantData["payload"] = payloadJSON
			}
			if variant.Literal != nil {
				literalJSON, err := serializeNode(variant.Literal)
				if err != nil {
					return ASTNodeJSON{}, err
				}
				variantData["literal"] = literalJSON
			}
			variants = append(variants, variantData)
		}
		nodeJSON.Data["variants"] = variants

	case *ast.MatchExpression:
		scrutineeJSON, err := serializeNode(n.Scrutinee)
		if err != nil {
			return ASTNodeJSON{}, err
		}
		nodeJSON.Data["scrutinee"] = scrutineeJSON
		arms := make([]map[string]interface{}, 0, len(n.Arms))
		for _, arm := range n.Arms {
			armData := map[string]interface{}{}
			if arm.Pattern != nil {
				patternJSON, err := serializeNode(arm.Pattern)
				if err != nil {
					return ASTNodeJSON{}, err
				}
				armData["pattern"] = patternJSON
			}
			if arm.Body != nil {
				bodyJSON, err := serializeNode(arm.Body)
				if err != nil {
					return ASTNodeJSON{}, err
				}
				armData["body"] = bodyJSON
			}
			arms = append(arms, armData)
		}
		nodeJSON.Data["arms"] = arms

	case *ast.InvocationExpression:
		funcJSON, err := serializeNode(n.Function)
		if err != nil {
			return ASTNodeJSON{}, err
		}
		nodeJSON.Data["function"] = funcJSON
		args := make([]ASTNodeJSON, 0, len(n.Arguments))
		for _, arg := range n.Arguments {
			argJSON, err := serializeNode(arg)
			if err != nil {
				return ASTNodeJSON{}, err
			}
			args = append(args, argJSON)
		}
		nodeJSON.Data["arguments"] = args

	case *ast.WhileStatement:
		condJSON, err := serializeNode(n.Condition)
		if err != nil {
			return ASTNodeJSON{}, err
		}
		nodeJSON.Data["condition"] = condJSON
		bodyJSON, err := serializeNode(n.Body)
		if err != nil {
			return ASTNodeJSON{}, err
		}
		nodeJSON.Data["body"] = bodyJSON

	case *ast.AssignmentStatement:
		nameJSON, err := serializeNode(n.Name)
		if err != nil {
			return ASTNodeJSON{}, err
		}
		nodeJSON.Data["name"] = nameJSON
		valueJSON, err := serializeNode(n.Value)
		if err != nil {
			return ASTNodeJSON{}, err
		}
		nodeJSON.Data["value"] = valueJSON

	default:
		// For unknown node types, just serialize the string representation
		nodeJSON.Data["string"] = node.String()
	}

	return nodeJSON, nil
}

// getNodeType returns the type name of an AST node
func getNodeType(node ast.Node) string {
	switch node.(type) {
	case *ast.Program:
		return "Program"
	case *ast.Identifier:
		return "Identifier"
	case *ast.IntegerLiteral:
		return "IntegerLiteral"
	case *ast.StringLiteral:
		return "StringLiteral"
	case *ast.Boolean:
		return "Boolean"
	case *ast.VariableDeclaration:
		return "VariableDeclaration"
	case *ast.ExpressionStatement:
		return "ExpressionStatement"
	case *ast.PrefixExpression:
		return "PrefixExpression"
	case *ast.InfixExpression:
		return "InfixExpression"
	case *ast.IndexExpression:
		return "IndexExpression"
	case *ast.SliceExpression:
		return "SliceExpression"
	case *ast.ArrayLiteral:
		return "ArrayLiteral"
	case *ast.RecordLiteral:
		return "RecordLiteral"
	case *ast.FunctionStatement:
		return "FunctionStatement"
	case *ast.BlockStatement:
		return "BlockStatement"
	case *ast.ADTType:
		return "ADTType"
	case *ast.MatchExpression:
		return "MatchExpression"
	case *ast.InvocationExpression:
		return "InvocationExpression"
	case *ast.WhileStatement:
		return "WhileStatement"
	case *ast.AssignmentStatement:
		return "AssignmentStatement"
	default:
		return "Unknown"
	}
}

// getNodePosition extracts position information from a node
func getNodePosition(node ast.Node) *PositionJSON {
	if node == nil {
		return nil
	}
	// Try to get token information
	var tok token.Token
	switch n := node.(type) {
	case *ast.Identifier:
		if n != nil {
			tok = n.Token
		}
	case *ast.IntegerLiteral:
		if n != nil {
			tok = n.Token
		}
	case *ast.StringLiteral:
		if n != nil {
			tok = n.Token
		}
	case *ast.Boolean:
		if n != nil {
			tok = n.Token
		}
	case *ast.VariableDeclaration:
		if n != nil {
			tok = n.Token
		}
	case *ast.ExpressionStatement:
		if n != nil {
			tok = n.Token
		}
	case *ast.PrefixExpression:
		if n != nil {
			tok = n.Token
		}
	case *ast.InfixExpression:
		if n != nil {
			tok = n.Token
		}
	case *ast.IndexExpression:
		if n != nil {
			tok = n.Token
		}
	case *ast.SliceExpression:
		if n != nil {
			tok = n.Token
		}
	case *ast.ArrayLiteral:
		if n != nil {
			tok = n.Token
		}
	case *ast.RecordLiteral:
		if n != nil {
			tok = n.Token
		}
	case *ast.FunctionStatement:
		if n != nil {
			tok = n.Token
		}
	case *ast.BlockStatement:
		if n != nil {
			tok = n.Token
		}
	case *ast.ADTType:
		if n != nil {
			tok = n.Token
		}
	case *ast.MatchExpression:
		if n != nil {
			tok = n.Token
		}
	case *ast.InvocationExpression:
		if n != nil {
			tok = n.Token
		}
	case *ast.WhileStatement:
		if n != nil {
			tok = n.Token
		}
	case *ast.AssignmentStatement:
		if n != nil {
			tok = n.Token
		}
	}

	if tok.Line > 0 {
		return &PositionJSON{
			Line:      tok.Line,
			Column:    tok.Column,
			ByteStart: tok.ByteStart,
			ByteEnd:   tok.ByteEnd,
		}
	}

	return nil
}

// serializeTypeExpression serializes a type expression to a string
func serializeTypeExpression(expr ast.Expression) (string, error) {
	// For now, use the string representation
	// In the future, we might want a more structured representation
	return expr.String(), nil
}

// SerializeCodegen writes codegen output (C code) to a JSONL file
// Each line of C code becomes a JSON object
func SerializeCodegen(cCode string, outputPath string) error {
	writer, err := NewJSONLWriter(outputPath)
	if err != nil {
		return err
	}
	defer writer.Close()

	// Split C code into lines and write each as a JSON object
	lines := splitLines(cCode)
	for i, line := range lines {
		lineJSON := map[string]interface{}{
			"line_number": i + 1,
			"content":     line,
		}
		if err := writer.WriteLine(lineJSON); err != nil {
			return fmt.Errorf("failed to write codegen line: %w", err)
		}
	}

	return nil
}

// splitLines splits a string into lines, preserving empty lines
func splitLines(s string) []string {
	var lines []string
	var current strings.Builder
	for _, r := range s {
		if r == '\n' {
			lines = append(lines, current.String())
			current.Reset()
		} else {
			current.WriteRune(r)
		}
	}
	// Add the last line if it doesn't end with newline
	if current.Len() > 0 {
		lines = append(lines, current.String())
	}
	return lines
}
