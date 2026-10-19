package bitwisecheck

import (
	"archive/tar"
	"context"
	"errors"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"strings"
	"time"
)

const archivePrefix = "lean-4.33.1-linux"
const maxExtractedBytes int64 = 4 << 30
const maxArchiveEntries = 20000

func extractArchive(ctx context.Context, root, archive string) error {
	in, err := os.Open(archive)
	if err != nil {
		return err
	}
	defer in.Close()
	ctx, cancel := context.WithCancel(ctx)
	defer cancel()
	cmd := exec.CommandContext(ctx, "/usr/bin/zstd", "--decompress", "--stdout", "--quiet")
	cmd.Dir = root
	cmd.Env = []string{"PATH=/nonexistent", "HOME=" + root, "LANG=C", "LC_ALL=C"}
	cmd.Stdin = in
	cmd.WaitDelay = 2 * time.Second
	configureProcess(cmd)
	out, err := cmd.StdoutPipe()
	if err != nil {
		return err
	}
	diag := &boundedOutput{cancel: cancel}
	cmd.Stderr = diag
	if err = cmd.Start(); err != nil {
		return err
	}
	extractionErr := extractTar(ctx, root, out)
	if extractionErr != nil {
		cancel()
	}
	// Wait even after extraction/refusal. Never leave a decompressor using files
	// that Install is about to remove. Drain normal tar padding before Wait.
	if extractionErr == nil {
		var tail int64
		tail, extractionErr = io.Copy(io.Discard, io.LimitReader(out, (1<<20)+1))
		if tail > 1<<20 {
			extractionErr = ErrBounds
		}
		if extractionErr != nil {
			cancel()
		}
	}
	waitErr := cmd.Wait()
	if extractionErr != nil {
		return extractionErr
	}
	if diag.overflow {
		return ErrBounds
	}
	if ctx.Err() != nil {
		return ctx.Err()
	}
	if waitErr != nil {
		return fmt.Errorf("bitwisecheck: archive decompressor failed: %w", waitErr)
	}
	if diag.Len() != 0 {
		return errors.New("bitwisecheck: unexpected decompressor diagnostics")
	}
	return nil
}
func safeArchiveName(name string) (string, error) {
	name = strings.TrimSuffix(name, "/")
	if name == "" || path.IsAbs(name) || strings.Contains(name, "\\") || path.Clean(name) != name || !(name == archivePrefix || strings.HasPrefix(name, archivePrefix+"/")) {
		return "", errors.New("bitwisecheck: unsafe archive path")
	}
	return name, nil
}
func rejectSymlinkParents(root, name string) error {
	parent := path.Dir(name)
	for parent != "." {
		stat, err := os.Lstat(filepath.Join(root, filepath.FromSlash(parent)))
		if err == nil && (!stat.IsDir() || stat.Mode()&os.ModeSymlink != 0) {
			return errors.New("bitwisecheck: archive has a non-directory ancestor")
		}
		if err != nil && !os.IsNotExist(err) {
			return err
		}
		parent = path.Dir(parent)
	}
	return nil
}
func extractTar(ctx context.Context, root string, r io.Reader) error {
	tr := tar.NewReader(snapshotReader{ctx, r})
	var total int64
	seen := make(map[string]bool)
	for count := 0; ; count++ {
		h, err := tr.Next()
		if err == io.EOF {
			return nil
		}
		if err != nil {
			return err
		}
		if count >= maxArchiveEntries {
			return ErrBounds
		}
		name, err := safeArchiveName(h.Name)
		if err != nil {
			return err
		}
		if seen[name] {
			return errors.New("bitwisecheck: duplicate archive entry")
		}
		seen[name] = true
		if err = rejectSymlinkParents(root, name); err != nil {
			return err
		}
		dest := filepath.Join(root, filepath.FromSlash(name))
		if fi, e := os.Lstat(dest); e == nil && (h.Typeflag != tar.TypeDir || !fi.IsDir() || fi.Mode()&os.ModeSymlink != 0) {
			return errors.New("bitwisecheck: archive path already exists")
		}
		switch h.Typeflag {
		case tar.TypeDir:
			if h.Size != 0 {
				return errors.New("bitwisecheck: directory has content")
			}
			if err = os.MkdirAll(dest, 0700); err != nil {
				return err
			}
		case tar.TypeReg, tar.TypeRegA:
			if h.Size < 0 || h.Size > maxExtractedBytes-total {
				return ErrBounds
			}
			total += h.Size
			if err = os.MkdirAll(filepath.Dir(dest), 0700); err != nil {
				return err
			}
			// Only owner permissions survive; ownership/setuid/setgid are never restored.
			mode := os.FileMode(0600)
			if h.Mode&0111 != 0 {
				mode = 0700
			}
			f, e := os.OpenFile(dest, os.O_WRONLY|os.O_CREATE|os.O_EXCL, mode)
			if e != nil {
				return e
			}
			n, e := io.Copy(f, tr)
			ce := f.Close()
			if e != nil {
				return e
			}
			if ce != nil {
				return ce
			}
			if n != h.Size {
				return io.ErrUnexpectedEOF
			}
		case tar.TypeSymlink:
			if h.Size != 0 || h.Linkname == "" || path.IsAbs(h.Linkname) || path.Base(h.Linkname) != h.Linkname || h.Linkname == "." || h.Linkname == ".." || strings.Contains(h.Linkname, "\\") {
				return errors.New("bitwisecheck: unsafe archive symlink")
			}
			target := path.Clean(path.Join(path.Dir(name), h.Linkname))
			if !(target == archivePrefix || strings.HasPrefix(target, archivePrefix+"/")) {
				return errors.New("bitwisecheck: escaping archive symlink")
			}
			if err = os.MkdirAll(filepath.Dir(dest), 0700); err != nil {
				return err
			}
			if err = os.Symlink(h.Linkname, dest); err != nil {
				return err
			}
		default:
			return errors.New("bitwisecheck: unsupported archive entry type")
		}
	}
}
