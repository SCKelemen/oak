package main

import (
	"bytes"
	"context"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/asm"
)

// The helper speaks the real child protocol and reads the inherited bitmap.
// Its second theorem cannot finish unless the first was cancelled promptly.
func TestSolverProcessHelper(t *testing.T) {
	mode := os.Getenv("OAK_TEST_SOLVER_HELPER")
	if mode == "" {
		return
	}
	_, _ = io.Copy(io.Discard, os.Stdin)
	slot, _ := strconv.Atoi(os.Getenv("OAK_SOLVER_VARIANT"))
	bitmap := os.NewFile(3, "cancellation")
	defer bitmap.Close()
	switch mode {
	case "cancel":
		if slot == 0 {
			fmt.Println("0 0 12 0 0")
			// This slot cannot solve the second theorem.
			fmt.Println("1 2 0 0 0")
		} else {
			var flag [1]byte
			deadline := time.Now().Add(15 * time.Second)
			for time.Now().Before(deadline) {
				if _, err := bitmap.ReadAt(flag[:], 0); err != nil {
					os.Exit(4)
				}
				if flag[0] == 1 {
					fmt.Println("1 0 34 0 0")
					os.Exit(0)
				}
				time.Sleep(time.Millisecond)
			}
			os.Exit(5)
		}
	case "preference", "duplicates":
		if slot == 3 {
			fmt.Println("0 0 99 0 0")
		} else {
			time.Sleep(25 * time.Millisecond)
			if mode == "duplicates" && slot == 1 {
				time.Sleep(50 * time.Millisecond)
			}
			var flag [1]byte
			_, _ = bitmap.ReadAt(flag[:], 0)
			if flag[0] != 0 {
				os.Exit(6)
			}
			if (mode == "preference" && slot == 0) || (mode == "duplicates" && slot == 1) {
				fmt.Println("0 1 17 1 0")
			} else {
				fmt.Println("0 2 0 1 0")
				if mode == "duplicates" {
					fmt.Println("0 2 0 1 0")
					fmt.Println("0 2 0 1 0")
				}
			}
		}
	case "wait":
		time.Sleep(30 * time.Second)
	}
	os.Exit(0)
}

func solverHelper(t *testing.T, mode string) string {
	t.Helper()
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	t.Setenv("OAK_TEST_SOLVER_HELPER", mode)
	script := filepath.Join(t.TempDir(), "solver")
	// exec keeps the helper as the direct child, so cancellation reaps it.
	body := "#!/bin/sh\nexec '" + strings.ReplaceAll(exe, "'", "'\\''") + "' -test.run=^TestSolverProcessHelper$\n"
	if err := os.WriteFile(script, []byte(body), 0700); err != nil {
		t.Fatal(err)
	}
	return script
}

func TestSolverCancelsSettledTheorem(t *testing.T) {
	solver := solverHelper(t, "cancel")
	th := oakTheorem{Problems: make([]asm.Problem, 2)}
	ctx, cancel := context.WithTimeout(context.Background(), 20*time.Second)
	defer cancel()
	vs, err := runOakSolverProcess(ctx, solver, []oakTheorem{th, th}, nil, 0, 100)
	if err != nil {
		t.Fatal(err)
	}
	if len(vs) != 2 || vs[0].Nodes != 12 || vs[1].Nodes != 34 {
		t.Fatalf("verdicts: %+v", vs)
	}
}

func TestSolverCancellationPreservesOakPreference(t *testing.T) {
	for _, mode := range []string{"preference", "duplicates"} {
		t.Run(mode, func(t *testing.T) {
			solver := solverHelper(t, mode)
			ctx, cancel := context.WithTimeout(context.Background(), 20*time.Second)
			defer cancel()
			vs, err := runOakSolverProcess(ctx, solver, []oakTheorem{{Problems: make([]asm.Problem, 1)}}, [][]byte{[]byte("source")}, 0, 100)
			if err != nil {
				t.Fatal(err)
			}
			if len(vs) != 1 || vs[0].Status != 1 || !vs[0].Lowered || vs[0].Nodes != 17 {
				t.Fatalf("verdicts: %+v", vs)
			}
		})
	}
}

func TestSolverContextCancellation(t *testing.T) {
	solver := solverHelper(t, "wait")
	ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
	defer cancel()
	start := time.Now()
	vs, err := runOakSolverProcess(ctx, solver, []oakTheorem{{Problems: make([]asm.Problem, 2)}}, nil, 0, 100)
	if err != context.DeadlineExceeded || vs != nil {
		t.Fatalf("got %v, %v", vs, err)
	}
	if time.Since(start) > 3*time.Second {
		t.Fatal("cancellation did not reap the children promptly")
	}
}

func TestOakCancellationBitmap(t *testing.T) {
	solver, err := oakSolverBinary()
	if err != nil {
		t.Fatal(err)
	}
	bitmap, err := os.CreateTemp(t.TempDir(), "cancel")
	if err != nil {
		t.Fatal(err)
	}
	defer bitmap.Close()
	if _, err := bitmap.Write([]byte{1, 0}); err != nil {
		t.Fatal(err)
	}
	reader, err := os.Open(bitmap.Name())
	if err != nil {
		t.Fatal(err)
	}
	defer reader.Close()
	// A one-bit constant true, one term and one root.
	words := []uint32{1, 0, 1, 64, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0}
	th := oakTheorem{Problems: []asm.Problem{{Words: words, Terms: 1}}}
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	cmd := exec.CommandContext(ctx, solver)
	cmd.ExtraFiles = []*os.File{reader}
	cmd.Env = append(os.Environ(), "OAK_SOLVER_CANCEL_FD=3", "OAK_SOLVER_VARIANT=0")
	cmd.Stdin = bytes.NewReader(encodeProblems([]oakTheorem{th, th}, nil, 0, 64))
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("%v: %s", err, out)
	}
	lines := strings.Split(strings.TrimSpace(string(out)), "\n")
	if len(lines) != 1 {
		t.Fatalf("expected only the uncancelled theorem: %s", out)
	}
	v, index, err := parseOakVerdict(lines[0])
	if err != nil || index != 1 || v.Status != 0 {
		t.Fatalf("verdict %v index %d: %v (%s)", v, index, err, out)
	}
}
