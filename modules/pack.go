package modules

// Module archives (docs/spec/82-package-semver.md section 7, docs/spec/
// 83-modules.md section 4.4): `oak mod pack` produces the gzip-compressed tar
// that `oak mod download` consumes. The archive holds the module's files
// under one `<last-path-segment>-<version>/` wrapper directory plus the
// module's API snapshot as api.json, so the honesty check on download has
// something to check. The packer admits only what the extractor admits —
// regular files and directories, relative slash paths, no symlinks — and
// writes deterministic headers so the same tree yields the same digest.

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io/fs"
	"os"
	"path"
	"path/filepath"
	"sort"
	"strings"
)

// MaxPackedBytes bounds the total size of files a pack may include, matching
// the extractor's decompressed bound.
const MaxPackedBytes = MaxExtractedBytes

// Pack archives the module rooted at root. Hidden entries, vendor, and
// testdata directories are excluded, as are symbolic links and any other
// non-regular file; api contains the snapshot to carry as api.json (an
// existing api.json in the tree is replaced by it). The archive bytes and
// their `sha256:<hex>` digest are returned.
func Pack(root string, wrapper string, api []byte) (archive []byte, digest string, err error) {
	root, err = filepath.Abs(root)
	if err != nil {
		return nil, "", err
	}
	if err := validateMemberPath(wrapper); err != nil || strings.Contains(wrapper, "/") {
		return nil, "", fmt.Errorf("wrapper directory %q must be a single path segment", wrapper)
	}
	type member struct {
		name string
		mode int64
		data []byte
	}
	var members []member
	var total int64
	err = filepath.WalkDir(root, func(current string, entry fs.DirEntry, walkErr error) error {
		if walkErr != nil {
			return walkErr
		}
		rel, err := filepath.Rel(root, current)
		if err != nil {
			return err
		}
		name := filepath.ToSlash(rel)
		if entry.IsDir() {
			if current != root && (strings.HasPrefix(entry.Name(), ".") || entry.Name() == "vendor" || entry.Name() == "testdata") {
				return filepath.SkipDir
			}
			if current != root {
				members = append(members, member{name: name + "/", mode: 0o755})
			}
			return nil
		}
		if strings.HasPrefix(entry.Name(), ".") || name == APIFile {
			return nil
		}
		// DirEntry.Type comes from Lstat, so a symlink is reported as a
		// symlink and not followed: it is skipped rather than packed.
		if !entry.Type().IsRegular() {
			return nil
		}
		if err := validateMemberPath(name); err != nil {
			return err
		}
		data, err := os.ReadFile(current)
		if err != nil {
			return err
		}
		total += int64(len(data))
		if total > MaxPackedBytes {
			return fmt.Errorf("module exceeds %d bytes", MaxPackedBytes)
		}
		if len(members) >= MaxArchiveEntries {
			return fmt.Errorf("module has more than %d files", MaxArchiveEntries)
		}
		members = append(members, member{name: name, mode: 0o644, data: data})
		return nil
	})
	if err != nil {
		return nil, "", err
	}
	if len(api) != 0 {
		members = append(members, member{name: APIFile, mode: 0o644, data: api})
	}
	sort.Slice(members, func(i, j int) bool { return members[i].name < members[j].name })

	var buf bytes.Buffer
	gz, err := gzip.NewWriterLevel(&buf, gzip.BestCompression)
	if err != nil {
		return nil, "", err
	}
	tw := tar.NewWriter(gz)
	write := func(header *tar.Header, data []byte) error {
		header.Format = tar.FormatPAX
		if err := tw.WriteHeader(header); err != nil {
			return err
		}
		_, err := tw.Write(data)
		return err
	}
	if err := write(&tar.Header{Name: wrapper + "/", Typeflag: tar.TypeDir, Mode: 0o755}, nil); err != nil {
		return nil, "", err
	}
	for _, m := range members {
		header := &tar.Header{Name: path.Join(wrapper, m.name), Mode: m.mode, Typeflag: tar.TypeReg, Size: int64(len(m.data))}
		if strings.HasSuffix(m.name, "/") {
			header.Name += "/"
			header.Typeflag, header.Size = tar.TypeDir, 0
		}
		if err := write(header, m.data); err != nil {
			return nil, "", err
		}
	}
	if err := tw.Close(); err != nil {
		return nil, "", err
	}
	if err := gz.Close(); err != nil {
		return nil, "", err
	}
	sum := sha256.Sum256(buf.Bytes())
	return buf.Bytes(), "sha256:" + hex.EncodeToString(sum[:]), nil
}
