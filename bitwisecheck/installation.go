package bitwisecheck

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"sync"
	"time"

	leansources "github.com/SCKelemen/oak/spec/lean"
)

const installTimeout = 30 * time.Minute
const RequestTimeout = 240 * time.Second

var installationSeal = &seal{2}

// Installation owns a fresh, private, source-built proof environment. Install is
// deliberately heavyweight (about 544 MiB archive, 2.9 GiB extracted); reuse one
// installation for requests and Close it when done. No reusable cache is trusted.
type Installation struct{ state *installationState }
type installationState struct {
	authority                     *seal
	root, lean, proof, sourceHash string
	ctx                           context.Context
	cancel                        context.CancelFunc
	gate                          chan struct{}
	mu                            sync.Mutex
	closed                        bool
	once                          sync.Once
	closeErr                      error
}

// Install accepts only an offline copy of the exact reviewed official Linux
// amd64 archive. Archive bytes, not its name, manifest, or claimed version, are
// authority. No network downloads or caller-supplied imports/runners are used.
func Install(ctx context.Context, archivePath string) (_ *Installation, err error) {
	if ctx == nil {
		return nil, errors.New("bitwisecheck: nil context")
	}
	if runtime.GOOS != "linux" || runtime.GOARCH != "amd64" {
		return nil, errors.New("bitwisecheck: only Linux amd64 hosts are supported")
	}
	if err = ctx.Err(); err != nil {
		return nil, err
	}
	if fi, e := os.Stat("/usr/bin/zstd"); e != nil || !fi.Mode().IsRegular() || fi.Mode().Perm()&0111 == 0 {
		return nil, errors.New("bitwisecheck: trusted host /usr/bin/zstd is required")
	}
	ctx, cancel := context.WithTimeout(ctx, installTimeout)
	defer cancel()
	root, err := os.MkdirTemp("/tmp", "oak-bitwisecheck-")
	if err != nil {
		return nil, err
	}
	defer func() {
		if err != nil {
			_ = os.RemoveAll(root)
		}
	}()
	archive := filepath.Join(root, "release.tar.zst")
	if err = copyPinnedArchive(ctx, archivePath, archive); err != nil {
		return nil, err
	}
	if err = extractArchive(ctx, root, archive); err != nil {
		return nil, err
	}
	if err = os.Remove(archive); err != nil {
		return nil, err
	}
	proof := filepath.Join(root, "proof")
	if err = os.Mkdir(proof, 0700); err != nil {
		return nil, err
	}
	lean := filepath.Join(root, "lean-4.33.1-linux", "bin", "lean")
	st := &installationState{root: root, lean: lean, proof: proof, sourceHash: leansources.Identity(), gate: make(chan struct{}, 1)}
	version, e := runLeanProcess(ctx, root, st.environment(), lean, "--version")
	if e != nil {
		return nil, e
	}
	expected := "Lean (version " + LeanVersion + ", x86_64-unknown-linux-gnu, commit " + LeanCommit + ", Release)\n"
	if string(version) != expected {
		return nil, errors.New("bitwisecheck: unexpected pinned Lean version")
	}
	for _, source := range leansources.Sources() {
		if err = ctx.Err(); err != nil {
			return nil, err
		}
		file := filepath.Join(proof, filepath.FromSlash(source.Path))
		if err = os.MkdirAll(filepath.Dir(file), 0700); err != nil {
			return nil, err
		}
		if err = os.WriteFile(file, source.Bytes, 0600); err != nil {
			return nil, err
		}
		out := strings.TrimSuffix(file, ".lean") + ".olean"
		if _, err = runLeanProcess(ctx, proof, st.environment(), lean, "-j1", "-M4096", "--trust=0", "-o", out, file); err != nil {
			return nil, fmt.Errorf("bitwisecheck: build %s: %w", source.Path, err)
		}
	}
	if err = ctx.Err(); err != nil {
		return nil, err
	}
	st.ctx, st.cancel = context.WithCancel(context.Background())
	st.authority = installationSeal
	installation := &Installation{state: st}
	if err = installation.selfTest(ctx); err != nil {
		st.cancel()
		return nil, fmt.Errorf("bitwisecheck: installation self-test: %w", err)
	}
	return installation, nil
}
func (s *installationState) environment() []string {
	return []string{"HOME=" + s.root, "TMPDIR=" + s.root, "PATH=/nonexistent", "LANG=C.UTF-8", "LC_ALL=C.UTF-8", "LEAN_PATH=" + s.proof + ":" + filepath.Join(s.root, "lean-4.33.1-linux", "lib", "lean")}
}

// Close cancels an active request and waits for its subprocess to be killed and
// reaped before removing owned files. Concurrent Close calls share that result.
func (i *Installation) Close() error {
	if i == nil || i.state == nil || i.state.authority != installationSeal {
		return ErrInvalidInstallation
	}
	s := i.state
	s.once.Do(func() {
		s.mu.Lock()
		s.closed = true
		s.cancel()
		s.mu.Unlock()
		s.gate <- struct{}{}
		defer func() { <-s.gate }()
		s.closeErr = os.RemoveAll(s.root)
	})
	return s.closeErr
}

// snapshotReader makes archive-copy cancellation effective between bounded reads.
type snapshotReader struct {
	ctx context.Context
	r   io.Reader
}

func (r snapshotReader) Read(p []byte) (int, error) {
	if e := r.ctx.Err(); e != nil {
		return 0, e
	}
	return r.r.Read(p)
}
func copyPinnedArchive(ctx context.Context, from, to string) error {
	in, err := openArchive(from)
	if err != nil {
		return err
	}
	defer in.Close()
	stat, err := in.Stat()
	if err != nil {
		return err
	}
	if !stat.Mode().IsRegular() || stat.Size() != ArchiveSize {
		return errors.New("bitwisecheck: archive must be a regular file with the pinned size")
	}
	out, err := os.OpenFile(to, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0600)
	if err != nil {
		return err
	}
	h := sha256.New()
	n, e := io.Copy(io.MultiWriter(out, h), io.LimitReader(snapshotReader{ctx, in}, ArchiveSize+1))
	closeErr := out.Close()
	if e != nil {
		return e
	}
	if closeErr != nil {
		return closeErr
	}
	if err = ctx.Err(); err != nil {
		return err
	}
	if n != ArchiveSize || hex.EncodeToString(h.Sum(nil)) != ArchiveSHA256 {
		return errors.New("bitwisecheck: archive size or SHA-256 does not match the pinned official release")
	}
	return nil
}
