package testrunner

import (
	"encoding/json"
	"io"
	"os/exec"
	"path/filepath"
	"sync"
)

// processContext describes the launch, before any application code runs.
// A resident fork inherits this context from its worker; its case index
// and input arrive over the worker protocol, not through a new argv.
type processContext struct {
	Executable string   `json:"executable"`
	Argv       []string `json:"argv"`
	CWD        string   `json:"cwd"`
	CWDError   string   `json:"cwd_error,omitempty"`
	Env        []string `json:"env"`
}

type processTraceEvent struct {
	Event      string `json:"event"`
	Phase      string `json:"phase"`
	Mode       string `json:"mode"`
	Package    string `json:"package"`
	Test       string `json:"test,omitempty"`
	Index      *int   `json:"index,omitempty"`
	Report     string `json:"report,omitempty"`
	InputBytes *int   `json:"input_bytes,omitempty"`
	WorkerPID  int    `json:"worker_pid,omitempty"`
	processContext
}

// Full environment values are available only through -trace-processes.
// Keep them out of result.Output and artifacts, and serialize complete
// records so concurrent cases cannot interleave their JSON on stderr.
type processTracer struct {
	mu  sync.Mutex
	out io.Writer
}

func (t *processTracer) context(cmd *exec.Cmd) processContext {
	if t == nil {
		return processContext{}
	}
	cwd, err := filepath.Abs(cmd.Dir)
	c := processContext{Executable: cmd.Path, Argv: append([]string{}, cmd.Args...), CWD: cwd, Env: cmd.Environ()}
	if err != nil {
		c.CWDError = err.Error()
	}
	return c
}

func (t *processTracer) emit(event processTraceEvent) {
	if t == nil {
		return
	}
	event.Event = "oak-test-process"
	t.mu.Lock()
	defer t.mu.Unlock()
	// A diagnostic writer failure must not change the test's verdict.
	_ = json.NewEncoder(t.out).Encode(event)
}

func (t *processTracer) command(phase, pkg string, cmd *exec.Cmd) processContext {
	c := t.context(cmd)
	t.emit(processTraceEvent{Phase: phase, Mode: "exec", Package: pkg, processContext: c})
	return c
}

func (p *nativeProgram) traceCase(mode string, c processContext, index int, report string, size, workerPID int) {
	if p.processTrace == nil {
		return
	}
	name := ""
	if index >= 0 && index < len(p.testNames) {
		name = p.testNames[index]
	}
	p.processTrace.emit(processTraceEvent{
		Phase: "case", Mode: mode, Package: p.packageDir, Test: name,
		Index: &index, Report: report, InputBytes: &size, WorkerPID: workerPID,
		processContext: c,
	})
}
