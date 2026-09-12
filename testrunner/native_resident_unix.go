//go:build unix

package testrunner

import (
	"os/exec"
	"syscall"
)

const residentSupported = true

// processGroupAttr puts a worker in its own process group, so killing the
// group ends the fork it is running too.
func processGroupAttr() *syscall.SysProcAttr { return &syscall.SysProcAttr{Setpgid: true} }

func killProcessGroup(cmd *exec.Cmd) {
	if cmd.Process != nil {
		_ = syscall.Kill(-cmd.Process.Pid, syscall.SIGKILL)
	}
}

func signalNumber(value int) syscall.Signal { return syscall.Signal(value) }
