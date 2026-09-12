//go:build windows

package testrunner

import (
	"os/exec"
	"syscall"
)

// Resident workers fork per case; Windows runs one process per case.
const residentSupported = false

func processGroupAttr() *syscall.SysProcAttr { return nil }

func killProcessGroup(cmd *exec.Cmd) {
	if cmd.Process != nil {
		_ = cmd.Process.Kill()
	}
}

func signalNumber(value int) syscall.Signal { return syscall.Signal(value) }
