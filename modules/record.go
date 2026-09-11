package modules

// Download records (docs/spec/115-tooling.md section 2): when the fetcher
// installs a module into the cache it writes a record beside the module's
// files — the archive digest that was verified and a hash of the extracted
// tree — so `oak mod verify` can later tell whether the cache entry still
// holds exactly what was downloaded.

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"
)

// RecordFile is the name of the download record inside a cache entry.
const RecordFile = ".oakdigest"

// Record is a download record.
type Record struct {
	// Archive is the `sha256:<hex>` digest of the archive that was extracted.
	Archive string
	// Tree is the hash of the extracted files (TreeHash).
	Tree string
}

// TreeHash hashes the regular files under dir: for each, in sorted
// slash-separated relative path order, the path, a NUL, the content, and a
// NUL, all fed to SHA-256. The record file itself and symbolic links are
// excluded, so the hash describes exactly the module's content.
func TreeHash(dir string) (string, error) {
	root, err := filepath.Abs(dir)
	if err != nil {
		return "", err
	}
	var files []string
	err = filepath.WalkDir(root, func(path string, entry fs.DirEntry, walkErr error) error {
		if walkErr != nil {
			return walkErr
		}
		if entry.IsDir() || !entry.Type().IsRegular() {
			return nil
		}
		rel, err := filepath.Rel(root, path)
		if err != nil {
			return err
		}
		if rel == RecordFile {
			return nil
		}
		files = append(files, filepath.ToSlash(rel))
		return nil
	})
	if err != nil {
		return "", err
	}
	sort.Strings(files)
	hash := sha256.New()
	for _, name := range files {
		data, err := os.ReadFile(filepath.Join(root, filepath.FromSlash(name)))
		if err != nil {
			return "", err
		}
		hash.Write([]byte(name))
		hash.Write([]byte{0})
		hash.Write(data)
		hash.Write([]byte{0})
	}
	return "sha256:" + hex.EncodeToString(hash.Sum(nil)), nil
}

// WriteRecord writes the download record for the module tree at dir.
func WriteRecord(dir, archiveDigest string) error {
	tree, err := TreeHash(dir)
	if err != nil {
		return err
	}
	text := fmt.Sprintf("archive %s\ntree %s\n", archiveDigest, tree)
	return os.WriteFile(filepath.Join(dir, RecordFile), []byte(text), 0o644)
}

// ReadRecord reads a cache entry's download record.
func ReadRecord(dir string) (Record, error) {
	text, err := os.ReadFile(filepath.Join(dir, RecordFile))
	if err != nil {
		return Record{}, err
	}
	var record Record
	for _, line := range strings.Split(string(text), "\n") {
		fields := strings.Fields(line)
		if len(fields) != 2 {
			continue
		}
		switch fields[0] {
		case "archive":
			record.Archive = fields[1]
		case "tree":
			record.Tree = fields[1]
		}
	}
	if record.Tree == "" {
		return Record{}, fmt.Errorf("%s: malformed download record", filepath.Join(dir, RecordFile))
	}
	return record, nil
}

// VerifyResult is one cached requirement's verification outcome.
type VerifyResult struct {
	Path    string
	Version string
	// State is "ok", "modified", "missing" (not in the cache), or
	// "unrecorded" (cached before records were written).
	State  string
	Detail string
}

// VerifyCache checks every requirement of a manifest that the cache holds
// against its download record.
func VerifyCache(cache string, manifest Manifest) []VerifyResult {
	var results []VerifyResult
	for _, requirement := range manifest.Requires {
		if _, replaced := manifest.Replaces[requirement.Path]; replaced {
			continue
		}
		result := VerifyResult{Path: requirement.Path, Version: requirement.Version.String()}
		dir := CacheDir(cache, requirement.Path, requirement.Version)
		if info, err := os.Stat(dir); err != nil || !info.IsDir() {
			result.State = "missing"
			results = append(results, result)
			continue
		}
		record, err := ReadRecord(dir)
		if err != nil {
			result.State, result.Detail = "unrecorded", "downloaded before records were kept; re-download to record it"
			results = append(results, result)
			continue
		}
		tree, err := TreeHash(dir)
		if err != nil {
			result.State, result.Detail = "modified", err.Error()
			results = append(results, result)
			continue
		}
		if tree != record.Tree {
			result.State, result.Detail = "modified", fmt.Sprintf("tree %s, recorded %s", tree, record.Tree)
		} else {
			result.State = "ok"
		}
		results = append(results, result)
	}
	return results
}
