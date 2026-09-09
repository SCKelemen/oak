package modules

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/packageapi"
)

type archiveEntry struct {
	name     string
	body     string
	typeflag byte
	link     string
}

func buildTarGz(t *testing.T, entries []archiveEntry) []byte {
	t.Helper()
	var buf bytes.Buffer
	gz := gzip.NewWriter(&buf)
	tw := tar.NewWriter(gz)
	for _, entry := range entries {
		flag := entry.typeflag
		if flag == 0 {
			flag = tar.TypeReg
		}
		header := &tar.Header{Name: entry.name, Mode: 0o644, Typeflag: flag, Linkname: entry.link}
		if flag == tar.TypeReg {
			header.Size = int64(len(entry.body))
		}
		if err := tw.WriteHeader(header); err != nil {
			t.Fatal(err)
		}
		if flag == tar.TypeReg {
			if _, err := tw.Write([]byte(entry.body)); err != nil {
				t.Fatal(err)
			}
		}
	}
	if err := tw.Close(); err != nil {
		t.Fatal(err)
	}
	if err := gz.Close(); err != nil {
		t.Fatal(err)
	}
	return buf.Bytes()
}

func digestOf(data []byte) string {
	sum := sha256.Sum256(data)
	return "sha256:" + hex.EncodeToString(sum[:])
}

func serve(t *testing.T, archive []byte) *httptest.Server {
	t.Helper()
	server := httptest.NewTLSServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch r.URL.Path {
		case "/dep.tar.gz":
			_, _ = w.Write(archive)
		case "/redirect-http":
			http.Redirect(w, r, "http://example.invalid/dep.tar.gz", http.StatusFound)
		default:
			http.NotFound(w, r)
		}
	}))
	t.Cleanup(server.Close)
	return server
}

func TestFetchDownloadsVerifiesAndExtracts(t *testing.T) {
	archive := buildTarGz(t, []archiveEntry{
		{name: "dep-1.0.0/", typeflag: tar.TypeDir},
		{name: "dep-1.0.0/oak.mod", body: "module example.com/dep\n"},
		{name: "dep-1.0.0/math/", typeflag: tar.TypeDir},
		{name: "dep-1.0.0/math/math.oak", body: "package math\n\npub square: (v: i32): i32 = v * v\n"},
	})
	server := serve(t, archive)
	cache := t.TempDir()
	fetcher := &Fetcher{Client: server.Client(), Cache: cache}
	manifest := Manifest{Path: "example.com/app", Requires: []Requirement{{
		Path: "example.com/dep", Version: packageapi.Version{Major: 1},
		Location: server.URL + "/dep.tar.gz", Digest: digestOf(archive),
	}}}
	if err := fetcher.Download(context.Background(), manifest); err != nil {
		t.Fatal(err)
	}
	target := CacheDir(cache, "example.com/dep", packageapi.Version{Major: 1})
	data, err := os.ReadFile(filepath.Join(target, "math", "math.oak"))
	if err != nil || !strings.Contains(string(data), "square") {
		t.Fatalf("extracted source missing: %v", err)
	}
	// Idempotent: a second download finds the cache.
	if err := fetcher.Download(context.Background(), manifest); err != nil {
		t.Fatal(err)
	}
}

// A failing Verify hook runs against the staged tree and keeps the module out
// of the cache; a passing one sees the extracted files.
func TestFetchVerifyHookGatesInstallation(t *testing.T) {
	archive := buildTarGz(t, []archiveEntry{
		{name: "oak.mod", body: "module example.com/dep\n"},
		{name: "api.json", body: "{}"},
	})
	server := serve(t, archive)
	cache := t.TempDir()
	manifest := Manifest{Path: "example.com/app", Requires: []Requirement{{
		Path: "example.com/dep", Version: packageapi.Version{Major: 1},
		Location: server.URL + "/dep.tar.gz", Digest: digestOf(archive),
	}}}
	seen := ""
	fetcher := &Fetcher{Client: server.Client(), Cache: cache, Verify: func(dir string, version packageapi.Version) error {
		data, err := os.ReadFile(filepath.Join(dir, APIFile))
		if err != nil {
			return err
		}
		seen = string(data)
		return errors.New("api.json rejected")
	}}
	err := fetcher.Download(context.Background(), manifest)
	if err == nil || !strings.Contains(err.Error(), "api.json rejected") {
		t.Fatalf("verify failure must abort the download: %v", err)
	}
	if seen != "{}" {
		t.Fatalf("verify hook did not see the staged tree: %q", seen)
	}
	target := CacheDir(cache, "example.com/dep", packageapi.Version{Major: 1})
	if _, err := os.Stat(target); !os.IsNotExist(err) {
		t.Fatal("a rejected module must not be installed")
	}
	fetcher.Verify = func(string, packageapi.Version) error { return nil }
	if err := fetcher.Download(context.Background(), manifest); err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(filepath.Join(target, "oak.mod")); err != nil {
		t.Fatal("accepted module must be installed")
	}
}

func TestFetchRefusesBadDigestBeforeExtracting(t *testing.T) {
	archive := buildTarGz(t, []archiveEntry{{name: "oak.mod", body: "module example.com/dep\n"}})
	server := serve(t, archive)
	cache := t.TempDir()
	fetcher := &Fetcher{Client: server.Client(), Cache: cache}
	manifest := Manifest{Requires: []Requirement{{
		Path: "example.com/dep", Version: packageapi.Version{Major: 1},
		Location: server.URL + "/dep.tar.gz", Digest: "sha256:" + strings.Repeat("00", 32),
	}}}
	err := fetcher.Download(context.Background(), manifest)
	if err == nil || !strings.Contains(err.Error(), "does not match") {
		t.Fatalf("expected digest mismatch, got %v", err)
	}
	entries, _ := os.ReadDir(cache)
	if len(entries) != 0 {
		t.Fatalf("nothing may be extracted on digest mismatch, found %v", entries)
	}
}

func TestFetchRefusesModulePathMismatchAndInsecureRedirect(t *testing.T) {
	archive := buildTarGz(t, []archiveEntry{{name: "oak.mod", body: "module example.com/other\n"}})
	server := serve(t, archive)
	cache := t.TempDir()
	fetcher := &Fetcher{Client: server.Client(), Cache: cache}
	err := fetcher.Download(context.Background(), Manifest{Requires: []Requirement{{
		Path: "example.com/dep", Version: packageapi.Version{Major: 1},
		Location: server.URL + "/dep.tar.gz", Digest: digestOf(archive),
	}}})
	if err == nil || !strings.Contains(err.Error(), "declares module") {
		t.Fatalf("expected module path mismatch, got %v", err)
	}
	if _, err := os.Stat(CacheDir(cache, "example.com/dep", packageapi.Version{Major: 1})); err == nil {
		t.Fatal("mismatching module must not land in the cache")
	}
	err = fetcher.Download(context.Background(), Manifest{Requires: []Requirement{{
		Path: "example.com/dep", Version: packageapi.Version{Major: 1},
		Location: server.URL + "/redirect-http", Digest: digestOf(archive),
	}}})
	if err == nil || !strings.Contains(err.Error(), "leaves https") {
		t.Fatalf("expected refused redirect, got %v", err)
	}
}

func TestExtractRejectsTraversalAndLinks(t *testing.T) {
	cases := map[string][]archiveEntry{
		"dotdot":   {{name: "../evil.oak", body: "x"}},
		"absolute": {{name: "/etc/evil", body: "x"}},
		"symlink":  {{name: "oak.mod", body: "module example.com/dep\n"}, {name: "link", typeflag: tar.TypeSymlink, link: "/etc/passwd"}},
		"hardlink": {{name: "oak.mod", body: "module example.com/dep\n"}, {name: "link", typeflag: tar.TypeLink, link: "oak.mod"}},
		"nested":   {{name: "a/../../evil", body: "x"}},
	}
	for name, entries := range cases {
		dir := t.TempDir()
		if err := ExtractTarGz(buildTarGz(t, entries), dir); err == nil {
			t.Fatalf("%s: extraction accepted", name)
		}
	}
	if err := ExtractTarGz([]byte("not gzip"), t.TempDir()); err == nil {
		t.Fatal("non-gzip accepted")
	}
}

func TestManifestPinnedRequire(t *testing.T) {
	manifest, err := ParseManifest("module example.com/app\nrequire example.com/dep 1.0.0 https://example.com/dep.tar.gz sha256:" + strings.Repeat("ab", 32) + "\n")
	if err != nil {
		t.Fatal(err)
	}
	if manifest.Requires[0].Location != "https://example.com/dep.tar.gz" || manifest.Requires[0].Digest != "sha256:"+strings.Repeat("ab", 32) {
		t.Fatalf("pinned requirement = %+v", manifest.Requires[0])
	}
	for name, text := range map[string]string{
		"http location": "module example.com/app\nrequire example.com/dep 1.0.0 http://example.com/d.tgz sha256:" + strings.Repeat("ab", 32) + "\n",
		"bad digest":    "module example.com/app\nrequire example.com/dep 1.0.0 https://example.com/d.tgz sha256:abc\n",
		"credentials":   "module example.com/app\nrequire example.com/dep 1.0.0 https://user:pw@example.com/d.tgz sha256:" + strings.Repeat("ab", 32) + "\n",
		"four fields":   "module example.com/app\nrequire example.com/dep 1.0.0 https://example.com/d.tgz\n",
	} {
		if _, err := ParseManifest(text); err == nil {
			t.Fatalf("%s: accepted", name)
		}
	}
}
