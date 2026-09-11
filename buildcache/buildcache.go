// Package buildcache stores compiled executables so `oak build`, `oak run`,
// `oak install`, and `oak test` skip the C compiler when nothing that
// determines the binary has changed (docs/spec/115-tooling.md section 3).
//
// The key is a SHA-256 over everything the binary depends on: the emitted C
// (which already captures the compiler's version through its output), the
// asm companion object, the C compiler's identity (resolved path, size, and
// modification time), the exact flag list, and the host OS and
// architecture. Entries live under $OAKCACHE (default: the user cache
// directory, `oak/`), written through a temporary file and rename; every
// cache failure is reported to the caller as a miss, never as a build
// failure. OAKCACHE=off disables the cache.
package buildcache

import (
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"runtime"
	"strconv"
)

// ErrDisabled reports that the cache is turned off.
var ErrDisabled = errors.New("build cache disabled")

// Dir returns the cache directory, or ErrDisabled.
func Dir() (string, error) {
	if explicit := os.Getenv("OAKCACHE"); explicit != "" {
		if explicit == "off" {
			return "", ErrDisabled
		}
		return filepath.Abs(explicit)
	}
	base, err := os.UserCacheDir()
	if err != nil {
		return "", err
	}
	return filepath.Join(base, "oak"), nil
}

// Key hashes the parts that determine a binary, with the host appended.
func Key(parts ...string) string {
	hash := sha256.New()
	for _, part := range parts {
		hash.Write([]byte(strconv.Itoa(len(part))))
		hash.Write([]byte{':'})
		hash.Write([]byte(part))
	}
	hash.Write([]byte(runtime.GOOS + "/" + runtime.GOARCH))
	return hex.EncodeToString(hash.Sum(nil))
}

// CompilerIdentity describes the C compiler cheaply and stably: its resolved
// path, size, and modification time. A toolchain upgrade changes at least
// one of them.
func CompilerIdentity(cc string) (string, error) {
	resolved, err := filepath.EvalSymlinks(cc)
	if err != nil {
		resolved = cc
	}
	info, err := os.Stat(resolved)
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("%s|%d|%d", resolved, info.Size(), info.ModTime().UnixNano()), nil
}

// entryPath is where a key's binary lives.
func entryPath(key string) (string, error) {
	if len(key) < 4 {
		return "", errors.New("malformed cache key")
	}
	dir, err := Dir()
	if err != nil {
		return "", err
	}
	return filepath.Join(dir, "build", key[:2], key), nil
}

// Lookup returns the cached binary for key, if present.
func Lookup(key string) (string, bool) {
	path, err := entryPath(key)
	if err != nil {
		return "", false
	}
	info, err := os.Stat(path)
	if err != nil || !info.Mode().IsRegular() {
		return "", false
	}
	return path, true
}

// Store copies the binary at source into the cache under key.
func Store(key, source string) error {
	path, err := entryPath(key)
	if err != nil {
		return err
	}
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	temp, err := os.CreateTemp(filepath.Dir(path), ".entry-")
	if err != nil {
		return err
	}
	tempPath := temp.Name()
	if err := copyInto(source, temp); err != nil {
		temp.Close()
		os.Remove(tempPath)
		return err
	}
	if err := temp.Close(); err != nil {
		os.Remove(tempPath)
		return err
	}
	if err := os.Chmod(tempPath, 0o755); err != nil {
		os.Remove(tempPath)
		return err
	}
	if err := os.Rename(tempPath, path); err != nil {
		os.Remove(tempPath)
		return err
	}
	return nil
}

// Copy copies an executable to destination (mode 0755), through a temporary
// file in the destination's directory.
func Copy(source, destination string) error {
	temp, err := os.CreateTemp(filepath.Dir(destination), "."+filepath.Base(destination)+".*")
	if err != nil {
		return err
	}
	tempPath := temp.Name()
	if err := copyInto(source, temp); err != nil {
		temp.Close()
		os.Remove(tempPath)
		return err
	}
	if err := temp.Close(); err != nil {
		os.Remove(tempPath)
		return err
	}
	if err := os.Chmod(tempPath, 0o755); err != nil {
		os.Remove(tempPath)
		return err
	}
	if err := os.Rename(tempPath, destination); err != nil {
		os.Remove(tempPath)
		return err
	}
	return nil
}

func copyInto(source string, destination *os.File) error {
	in, err := os.Open(source)
	if err != nil {
		return err
	}
	defer in.Close()
	_, err = io.Copy(destination, in)
	return err
}

// Clean removes the cache's build entries. It touches only the resolved
// cache directory's `build` subdirectory.
func Clean() (string, error) {
	dir, err := Dir()
	if err != nil {
		return "", err
	}
	build := filepath.Join(dir, "build")
	if info, err := os.Stat(build); err != nil || !info.IsDir() {
		return build, nil
	}
	return build, os.RemoveAll(build)
}
