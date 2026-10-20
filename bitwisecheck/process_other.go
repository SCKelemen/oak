//go:build !linux

package bitwisecheck

import (
	"os"
	"os/exec"
)

func configureProcess(cmd *exec.Cmd) {}

func openArchive(path string) (*os.File, error) { return os.Open(path) }
