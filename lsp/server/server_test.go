package server

import (
	"bufio"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/lsp"
)

// client drives a Server over in-memory pipes.
type client struct {
	t      *testing.T
	writer io.Writer
	reader *bufio.Reader
	done   chan error
	next   int
}

func startServer(t *testing.T) *client {
	t.Helper()
	clientToServer, serverIn := io.Pipe()
	serverOut, serverToClient := io.Pipe()
	c := &client{t: t, writer: serverIn, reader: bufio.NewReader(serverOut), done: make(chan error, 1)}
	go func() { c.done <- Serve(clientToServer, serverToClient, io.Discard) }()
	t.Cleanup(func() {
		c.notify("exit", nil)
		select {
		case <-c.done:
		case <-time.After(5 * time.Second):
			t.Error("server did not exit")
		}
	})
	return c
}

func (c *client) send(message map[string]interface{}) {
	message["jsonrpc"] = "2.0"
	body, err := json.Marshal(message)
	if err != nil {
		c.t.Fatal(err)
	}
	fmt.Fprintf(c.writer, "Content-Length: %d\r\n\r\n%s", len(body), body)
}

func (c *client) notify(method string, params interface{}) {
	c.send(map[string]interface{}{"method": method, "params": params})
}

func (c *client) request(method string, params interface{}) json.RawMessage {
	c.next++
	id := c.next
	c.send(map[string]interface{}{"id": id, "method": method, "params": params})
	for {
		message := c.read()
		var envelope struct {
			ID     *int            `json:"id"`
			Result json.RawMessage `json:"result"`
			Error  json.RawMessage `json:"error"`
		}
		if err := json.Unmarshal(message, &envelope); err != nil {
			c.t.Fatal(err)
		}
		if envelope.ID != nil && *envelope.ID == id {
			if envelope.Error != nil {
				c.t.Fatalf("%s: error %s", method, envelope.Error)
			}
			return envelope.Result
		}
	}
}

// read returns the next frame body.
func (c *client) read() []byte {
	length := -1
	for {
		line, err := c.reader.ReadString('\n')
		if err != nil {
			c.t.Fatal(err)
		}
		line = strings.TrimRight(line, "\r\n")
		if line == "" {
			break
		}
		if strings.HasPrefix(line, "Content-Length:") {
			fmt.Sscanf(strings.TrimSpace(strings.TrimPrefix(line, "Content-Length:")), "%d", &length)
		}
	}
	body := make([]byte, length)
	if _, err := io.ReadFull(c.reader, body); err != nil {
		c.t.Fatal(err)
	}
	return body
}

// awaitDiagnostics reads until a publishDiagnostics for uri arrives.
func (c *client) awaitDiagnostics(uri string) []map[string]interface{} {
	deadline := time.After(20 * time.Second)
	for {
		select {
		case <-deadline:
			c.t.Fatal("no diagnostics published")
		default:
		}
		message := c.read()
		var envelope struct {
			Method string `json:"method"`
			Params struct {
				URI         string                   `json:"uri"`
				Diagnostics []map[string]interface{} `json:"diagnostics"`
			} `json:"params"`
		}
		if err := json.Unmarshal(message, &envelope); err != nil {
			c.t.Fatal(err)
		}
		if envelope.Method == "textDocument/publishDiagnostics" && envelope.Params.URI == uri {
			return envelope.Params.Diagnostics
		}
	}
}

func writeFile(t *testing.T, path, text string) {
	t.Helper()
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(path, []byte(text), 0o644); err != nil {
		t.Fatal(err)
	}
}

func TestServerDiagnosticsHoverDefinitionSymbolsTokens(t *testing.T) {
	root := t.TempDir()
	writeFile(t, filepath.Join(root, "oak.mod"), "module example.com/app\n")
	writeFile(t, filepath.Join(root, "util.oak"), "package main\n\ntwice: (v: i32): i32 = v * 2\n")
	mainPath := filepath.Join(root, "main.oak")
	source := "package main\n\nP: type = struct { v: i32 }\n\nmain: (): i32 = {\n  k: i32 = twice(20)\n  k + 2\n}\n"
	writeFile(t, mainPath, source)
	uri := fileURI(mainPath)

	c := startServer(t)
	result := c.request("initialize", map[string]interface{}{"capabilities": map[string]interface{}{}})
	var init struct {
		Capabilities struct {
			Hover     bool `json:"hoverProvider"`
			Semantic  json.RawMessage
			Semantics struct {
				Legend struct {
					TokenTypes []string `json:"tokenTypes"`
				} `json:"legend"`
			} `json:"semanticTokensProvider"`
		} `json:"capabilities"`
	}
	if err := json.Unmarshal(result, &init); err != nil || !init.Capabilities.Hover || len(init.Capabilities.Semantics.Legend.TokenTypes) == 0 {
		t.Fatalf("initialize = %s (%v)", result, err)
	}
	c.notify("initialized", map[string]interface{}{})

	// A clean open publishes no diagnostics; an edit with a type error
	// publishes one at the right place; fixing it clears it.
	c.notify("textDocument/didOpen", map[string]interface{}{"textDocument": map[string]interface{}{"uri": uri, "languageId": "oak", "version": 1, "text": source}})
	if diags := c.awaitDiagnostics(uri); len(diags) != 0 {
		t.Fatalf("clean file must have no diagnostics: %v", diags)
	}
	broken := strings.Replace(source, "twice(20)", "twice(true)", 1)
	c.notify("textDocument/didChange", map[string]interface{}{"textDocument": map[string]interface{}{"uri": uri, "version": 2}, "contentChanges": []map[string]interface{}{{"text": broken}}})
	diags := c.awaitDiagnostics(uri)
	if len(diags) == 0 {
		t.Fatal("type error must be published")
	}
	if diags[0]["severity"].(float64) != 1 || !strings.Contains(fmt.Sprint(diags[0]["message"]), "twice") && !strings.Contains(fmt.Sprint(diags[0]["message"]), "type") {
		t.Fatalf("diagnostic = %v", diags[0])
	}
	if line := diags[0]["range"].(map[string]interface{})["start"].(map[string]interface{})["line"].(float64); line != 5 {
		t.Fatalf("diagnostic line = %v, want 5", line)
	}
	c.notify("textDocument/didChange", map[string]interface{}{"textDocument": map[string]interface{}{"uri": uri, "version": 3}, "contentChanges": []map[string]interface{}{{"text": source}}})
	if diags := c.awaitDiagnostics(uri); len(diags) != 0 {
		t.Fatalf("fixed file must clear diagnostics: %v", diags)
	}

	// Hover on `twice` (line 5, col 11) gives its checked type; on `k` its
	// local declaration.
	hover := c.request("textDocument/hover", map[string]interface{}{"textDocument": map[string]string{"uri": uri}, "position": lsp.Position{Line: 5, Character: 12}})
	if !strings.Contains(string(hover), "twice") || !strings.Contains(string(hover), "i32") {
		t.Fatalf("hover twice = %s", hover)
	}
	hover = c.request("textDocument/hover", map[string]interface{}{"textDocument": map[string]string{"uri": uri}, "position": lsp.Position{Line: 6, Character: 2}})
	if !strings.Contains(string(hover), "k: i32") {
		t.Fatalf("hover k = %s", hover)
	}
	if none := c.request("textDocument/hover", map[string]interface{}{"textDocument": map[string]string{"uri": uri}, "position": lsp.Position{Line: 1, Character: 0}}); string(none) != "null" {
		t.Fatalf("hover on nothing = %s", none)
	}
	// Hover still answers from the syntax when the package does not check.
	c.notify("textDocument/didChange", map[string]interface{}{"textDocument": map[string]interface{}{"uri": uri, "version": 4}, "contentChanges": []map[string]interface{}{{"text": broken}}})
	c.awaitDiagnostics(uri)
	hover = c.request("textDocument/hover", map[string]interface{}{"textDocument": map[string]string{"uri": uri}, "position": lsp.Position{Line: 4, Character: 1}})
	if !strings.Contains(string(hover), "main: (): i32") {
		t.Fatalf("hover on a broken package = %s", hover)
	}
	c.notify("textDocument/didChange", map[string]interface{}{"textDocument": map[string]interface{}{"uri": uri, "version": 5}, "contentChanges": []map[string]interface{}{{"text": source}}})
	c.awaitDiagnostics(uri)

	// Definition: `twice` lives in util.oak; `k` in this file.
	def := c.request("textDocument/definition", map[string]interface{}{"textDocument": map[string]string{"uri": uri}, "position": lsp.Position{Line: 5, Character: 12}})
	var location lsp.Location
	if err := json.Unmarshal(def, &location); err != nil || !strings.HasSuffix(location.URI, "util.oak") || location.Range.Start.Line != 2 {
		t.Fatalf("definition twice = %s (%v)", def, err)
	}
	def = c.request("textDocument/definition", map[string]interface{}{"textDocument": map[string]string{"uri": uri}, "position": lsp.Position{Line: 6, Character: 2}})
	if err := json.Unmarshal(def, &location); err != nil || location.URI != uri || location.Range.Start.Line != 5 || location.Range.Start.Character != 2 {
		t.Fatalf("definition k = %s (%v)", def, err)
	}

	// Document symbols: P (struct) and main (function).
	symbols := c.request("textDocument/documentSymbol", map[string]interface{}{"textDocument": map[string]string{"uri": uri}})
	var list []struct {
		Name string `json:"name"`
		Kind int    `json:"kind"`
	}
	if err := json.Unmarshal(symbols, &list); err != nil || len(list) != 2 || list[0].Name != "P" || list[0].Kind != 23 || list[1].Name != "main" || list[1].Kind != 12 {
		t.Fatalf("symbols = %s (%v)", symbols, err)
	}

	// Semantic tokens: decode the first token as the `package` keyword and
	// find `twice` classified as a function, `P` as a type.
	tokens := c.request("textDocument/semanticTokens/full", map[string]interface{}{"textDocument": map[string]string{"uri": uri}})
	var payload struct {
		Data []int `json:"data"`
	}
	if err := json.Unmarshal(tokens, &payload); err != nil || len(payload.Data)%5 != 0 || len(payload.Data) == 0 {
		t.Fatalf("tokens = %s (%v)", tokens, err)
	}
	if payload.Data[0] != 0 || payload.Data[1] != 0 || payload.Data[2] != len("package") || payload.Data[3] != tokKeyword {
		t.Fatalf("first token = %v", payload.Data[:5])
	}
	line, start := 0, 0
	kinds := map[string]int{}
	lines := strings.Split(source, "\n")
	for i := 0; i+4 < len(payload.Data); i += 5 {
		if payload.Data[i] != 0 {
			line += payload.Data[i]
			start = payload.Data[i+1]
		} else {
			start += payload.Data[i+1]
		}
		text := lines[line][start : start+payload.Data[i+2]]
		kinds[text] = payload.Data[i+3]
	}
	if kinds["twice"] != tokFunction || kinds["P"] != tokType || kinds["struct"] != tokKeyword || kinds["i32"] != tokType || kinds["k"] != tokVariable || kinds["20"] != tokNumber {
		t.Fatalf("token kinds = %v", kinds)
	}

	// Close clears diagnostics; shutdown answers.
	c.notify("textDocument/didClose", map[string]interface{}{"textDocument": map[string]string{"uri": uri}})
	if diags := c.awaitDiagnostics(uri); len(diags) != 0 {
		t.Fatal("close must clear diagnostics")
	}
	if result := c.request("shutdown", nil); string(result) != "null" {
		t.Fatalf("shutdown = %s", result)
	}
}

func TestServerRejectsBadFrames(t *testing.T) {
	in := strings.NewReader("Content-Length: 99999999999\r\n\r\n")
	if err := Serve(in, io.Discard, io.Discard); err == nil || !strings.Contains(err.Error(), "exceeds") {
		t.Fatalf("oversized frame must end the session: %v", err)
	}
	in = strings.NewReader("Content-Length: 5\r\n\r\n{bad}")
	if err := Serve(in, io.Discard, io.Discard); err == nil || !strings.Contains(err.Error(), "malformed") {
		t.Fatalf("malformed message must end the session: %v", err)
	}
	if _, err := uriPath("https://example.com/x.oak"); err == nil {
		t.Fatal("non-file URIs must be rejected")
	}
}
