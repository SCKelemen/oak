package repl

import (
	"bytes"
	"strings"
	"testing"
)

func TestStartWritesPromptToProvidedOutput(t *testing.T) {
	in := strings.NewReader("")
	var out bytes.Buffer

	Start(in, &out)

	if out.String() != PROMPT {
		t.Fatalf("unexpected output. expected %q, received %q", PROMPT, out.String())
	}
}
