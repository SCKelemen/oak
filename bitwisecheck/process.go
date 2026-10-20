package bitwisecheck

import (
	"bytes"
	"context"
	"fmt"
	"os/exec"
	"time"
)

// The cap cancels the process instead of merely truncating its output. There is
// one writer per pipe, and fields are read only after Cmd.Wait has joined it.
type boundedOutput struct {
	buffer   bytes.Buffer
	cancel   context.CancelFunc
	overflow bool
}

func (b *boundedOutput) Len() int       { return b.buffer.Len() }
func (b *boundedOutput) Bytes() []byte  { return b.buffer.Bytes() }
func (b *boundedOutput) String() string { return b.buffer.String() }

func (b *boundedOutput) Write(p []byte) (int, error) {
	if b.Len()+len(p) > MaxOutputBytes {
		b.overflow = true
		b.cancel()
		return 0, ErrBounds
	}
	return b.buffer.Write(p)
}
func runProcess(ctx context.Context, dir string, env []string, program string, args ...string) ([]byte, error) {
	ctx, cancel := context.WithCancel(ctx)
	defer cancel()
	cmd := exec.CommandContext(ctx, program, args...)
	cmd.Dir = dir
	cmd.Env = env
	cmd.WaitDelay = 2 * time.Second
	configureProcess(cmd)
	out := &boundedOutput{cancel: cancel}
	diag := &boundedOutput{cancel: cancel}
	cmd.Stdout = out
	cmd.Stderr = diag
	err := cmd.Run() // Includes Wait: stdout never grants success before process exit.
	if out.overflow || diag.overflow {
		return nil, ErrBounds
	}
	if ctx.Err() != nil {
		return nil, ctx.Err()
	}
	if err != nil {
		return nil, fmt.Errorf("bitwisecheck: checker subprocess failed: %w: %s%s", err, out.String(), diag.String())
	}
	if diag.Len() != 0 {
		return nil, fmt.Errorf("bitwisecheck: unexpected checker stderr: %s", diag.String())
	}
	return append([]byte(nil), out.Bytes()...), nil
}

// All Lean processes in one Go process share a cancellation-aware gate, in
// addition to each installation's custody lock. This avoids multiplying the
// heavy request memory budget when callers prepare multiple installations.
var leanProcessGate = make(chan struct{}, 1)

func runLeanProcess(ctx context.Context, dir string, env []string, program string, args ...string) ([]byte, error) {
	select {
	case leanProcessGate <- struct{}{}:
		defer func() { <-leanProcessGate }()
	case <-ctx.Done():
		return nil, ctx.Err()
	}
	return runProcess(ctx, dir, env, program, args...)
}
