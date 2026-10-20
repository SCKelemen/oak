//go:build linux

package bitwisecheck

import (
	"context"
	"os"
	"path/filepath"
	"syscall"
	"testing"
	"time"
)

func TestArchiveFIFORefusesWithoutBlocking(t *testing.T) {
	dir := t.TempDir()
	fifo := filepath.Join(dir, "fifo")
	if e := syscall.Mkfifo(fifo, 0600); e != nil {
		t.Fatal(e)
	}
	done := make(chan error, 1)
	go func() { done <- copyPinnedArchive(context.Background(), fifo, filepath.Join(dir, "copy")) }()
	select {
	case e := <-done:
		if e == nil {
			t.Fatal("FIFO accepted")
		}
	case <-time.After(time.Second):
		t.Fatal("FIFO blocked regular-file check")
	}
}

func TestArchiveDigestMismatch(t *testing.T) {
	dir := t.TempDir()
	source := filepath.Join(dir, "sparse-untrusted-release")
	f, e := os.Create(source)
	if e != nil {
		t.Fatal(e)
	}
	if e = f.Truncate(ArchiveSize); e != nil {
		f.Close()
		t.Fatal(e)
	}
	if e = f.Close(); e != nil {
		t.Fatal(e)
	}
	if e = copyPinnedArchive(context.Background(), source, filepath.Join(dir, "snapshot")); e == nil {
		t.Fatal("pinned-size archive with wrong digest accepted")
	}
}
