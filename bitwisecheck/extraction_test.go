package bitwisecheck

import (
	"archive/tar"
	"bytes"
	"context"
	"os"
	"path/filepath"
	"testing"
)

func tarBytes(t *testing.T, headers ...*tar.Header) []byte {
	t.Helper()
	var b bytes.Buffer
	w := tar.NewWriter(&b)
	for _, h := range headers {
		if e := w.WriteHeader(h); e != nil {
			t.Fatal(e)
		}
		if h.Size > 0 {
			if _, e := w.Write(bytes.Repeat([]byte{1}, int(h.Size))); e != nil {
				t.Fatal(e)
			}
		}
	}
	if e := w.Close(); e != nil {
		t.Fatal(e)
	}
	return b.Bytes()
}
func TestExtractionBoundaries(t *testing.T) {
	regular := func(name string) *tar.Header {
		return &tar.Header{Name: name, Mode: 04777, Size: 1, Typeflag: tar.TypeReg}
	}
	link := func(name, target string) *tar.Header {
		return &tar.Header{Name: name, Linkname: target, Typeflag: tar.TypeSymlink}
	}
	for name, headers := range map[string][]*tar.Header{
		"absolute": {regular("/tmp/escape")}, "traversal": {regular(archivePrefix + "/../escape")}, "wrong prefix": {regular("other/file")},
		"duplicate":       {regular(archivePrefix + "/file"), regular(archivePrefix + "/file")},
		"outside symlink": {link(archivePrefix+"/link", "../../outside")}, "absolute symlink": {link(archivePrefix+"/link", "/tmp")},
		"symlink ancestor": {link(archivePrefix+"/link", "other"), regular(archivePrefix + "/link/child")},
		"device":           {{Name: archivePrefix + "/device", Typeflag: tar.TypeChar}}, "hardlink": {{Name: archivePrefix + "/link", Typeflag: tar.TypeLink, Linkname: archivePrefix + "/file"}},
	} {
		t.Run(name, func(t *testing.T) {
			if e := extractTar(context.Background(), t.TempDir(), bytes.NewReader(tarBytes(t, headers...))); e == nil {
				t.Fatal("accepted unsafe tar")
			}
		})
	}
	root := t.TempDir()
	raw := tarBytes(t, regular(archivePrefix+"/lib/file"), link(archivePrefix+"/lib/link", "file"))
	if e := extractTar(context.Background(), root, bytes.NewReader(raw)); e != nil {
		t.Fatal(e)
	}
	fi, e := os.Stat(filepath.Join(root, archivePrefix, "lib/file"))
	if e != nil {
		t.Fatal(e)
	}
	if fi.Mode().Perm() != 0700 || fi.Mode()&(os.ModeSetuid|os.ModeSetgid) != 0 {
		t.Fatal("unsafe modes preserved")
	}
}
