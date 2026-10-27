// Package buildcache stores compiled executables so `oak build`, `oak run`,
// `oak install`, and `oak test` skip the C compiler when nothing that
// determines the binary has changed (docs/spec/115-tooling.md section 3).
//
// Keys cover emitted C, asm objects, compiler executable contents, flags and
// host identity. This is a development cache, not hermetic build provenance:
// system headers, libraries and subordinate compiler tools remain external.
// Entries live under $OAKCACHE (default: the user cache directory, `oak/`).
// Digest-verified artifacts are published before an atomic manifest update;
// invalid or legacy entries are misses. OAKCACHE=off disables the cache.
// Storage is assumed not to change between Lookup and the caller's use.
package buildcache

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
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

// CompilerIdentity binds the resolved compiler path to its executable contents.
// Replacements with unchanged size and timestamps still invalidate the cache.
func CompilerIdentity(cc string) (string, error) {
	resolved, err := filepath.EvalSymlinks(cc)
	if err != nil {
		return "", err
	}
	digest, err := fileDigest(resolved)
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("%s|sha256:%s", resolved, digest), nil
}

func validDigest(value string) bool {
	b, err := hex.DecodeString(value)
	return err == nil && len(b) == sha256.Size && hex.EncodeToString(b) == value
}

// entryPath is the base path for a key's manifest and content-named binary.
func entryPath(key string) (string, error) {
	if !validDigest(key) {
		return "", errors.New("malformed cache key")
	}
	dir, err := Dir()
	if err != nil {
		return "", err
	}
	return filepath.Join(dir, "build", key[:2], key), nil
}

type manifest struct {
	Key    string `json:"key"`
	Digest string `json:"sha256"`
}

func fileDigest(path string) (string, error) {
	file, err := os.Open(path)
	if err != nil {
		return "", err
	}
	defer file.Close()
	info, err := file.Stat()
	if err != nil {
		return "", err
	}
	if !info.Mode().IsRegular() {
		return "", errors.New("not a regular file")
	}
	hash := sha256.New()
	if _, err := io.Copy(hash, file); err != nil {
		return "", err
	}
	return hex.EncodeToString(hash.Sum(nil)), nil
}

// Lookup returns only an executable whose digest matches the key's manifest.
// Content names avoid mixed binary/manifest pairs during concurrent Store calls.
func Lookup(key string) (string, bool) {
	path, err := entryPath(key)
	if err != nil {
		return "", false
	}
	info, err := os.Lstat(path + ".json")
	if err != nil || !info.Mode().IsRegular() {
		return "", false
	}
	data, err := os.ReadFile(path + ".json")
	if err != nil {
		return "", false
	}
	var entry manifest
	if json.Unmarshal(data, &entry) != nil || entry.Key != key || !validDigest(entry.Digest) {
		return "", false
	}
	binary := path + "-" + entry.Digest
	info, err = os.Lstat(binary)
	if err != nil || !info.Mode().IsRegular() || info.Mode().Perm()&0o111 == 0 {
		return "", false
	}
	digest, err := fileDigest(binary)
	if err != nil || digest != entry.Digest {
		return "", false
	}
	return binary, true
}

// Store publishes a complete binary before atomically publishing its manifest.
// A failed or concurrent publication may cause a miss but cannot return a
// partially copied binary. Old content objects are retained until Clean.
func Store(key, source string) error {
	path, err := entryPath(key)
	if err != nil {
		return err
	}
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	work, err := os.MkdirTemp(filepath.Dir(path), ".entry-")
	if err != nil {
		return err
	}
	defer os.RemoveAll(work)
	staging := filepath.Join(work, "binary")
	if err := Copy(source, staging); err != nil {
		return err
	}
	digest, err := fileDigest(staging)
	if err != nil {
		return err
	}
	binary := path + "-" + digest
	if err := os.Rename(staging, binary); err != nil {
		return err
	}
	data, err := json.Marshal(manifest{Key: key, Digest: digest})
	if err != nil {
		return err
	}
	stagedManifest := filepath.Join(work, "manifest.json")
	if err := os.WriteFile(stagedManifest, data, 0o600); err != nil {
		return err
	}
	return os.Rename(stagedManifest, path+".json")
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
