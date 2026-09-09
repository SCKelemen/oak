package modules

// Dependency fetching (docs/spec/83-modules.md section 4.4). The compiler
// never touches the network: `oak mod download` runs this code to populate
// the module cache from the locations and content hashes pinned in oak.mod,
// Zig-style. A requirement with a location reads
//
//	require example.com/dep 1.2.0 https://example.com/dep-1.2.0.tar.gz sha256:<64 hex>
//
// The archive is downloaded over HTTPS only (redirects may not leave HTTPS),
// bounded in size, hashed in full and compared with the pinned digest BEFORE
// any extraction, then extracted with the tar-slip rules below into a fresh
// directory that is renamed into place only after the extracted oak.mod
// declares the required module path. Identity is the module path; the URL is
// a location hint; the hash is the trust anchor.

import (
	"archive/tar"
	"compress/gzip"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/SCKelemen/oak/packageapi"
)

// APIFile is the module-level API snapshot an archive may carry at its
// root; `oak mod download` verifies it against the extracted sources.
const APIFile = "api.json"

// Fetch limits. They bound the work an oak.mod can make the tool do.
const (
	// MaxArchiveBytes caps the downloaded (compressed) archive.
	MaxArchiveBytes = 256 << 20
	// MaxExtractedBytes caps the total decompressed content.
	MaxExtractedBytes = 1 << 30
	// MaxArchiveEntries caps the number of archive members.
	MaxArchiveEntries = 100000
	// FetchTimeout bounds one download.
	FetchTimeout = 10 * time.Minute
)

// ParseDigest validates a pinned digest of the form `sha256:<64 hex>` and
// returns the lowercase hex.
func ParseDigest(text string) (string, error) {
	const prefix = "sha256:"
	if !strings.HasPrefix(text, prefix) {
		return "", fmt.Errorf("digest %q must have the form sha256:<64 hex digits>", text)
	}
	digest := strings.ToLower(text[len(prefix):])
	if len(digest) != 64 {
		return "", fmt.Errorf("digest %q must have 64 hex digits", text)
	}
	if _, err := hex.DecodeString(digest); err != nil {
		return "", fmt.Errorf("digest %q is not hexadecimal", text)
	}
	return digest, nil
}

// ValidateLocation checks a requirement's archive URL: absolute, https, with
// a host and no credentials.
func ValidateLocation(location string) error {
	parsed, err := url.Parse(location)
	if err != nil {
		return fmt.Errorf("location %q: %v", location, err)
	}
	if parsed.Scheme != "https" {
		return fmt.Errorf("location %q must use https", location)
	}
	if parsed.Host == "" {
		return fmt.Errorf("location %q has no host", location)
	}
	if parsed.User != nil {
		return fmt.Errorf("location %q must not carry credentials", location)
	}
	return nil
}

// CacheDir is the directory a module version occupies in the cache.
func CacheDir(cache, path string, version packageapi.Version) string {
	return filepath.Join(cache, filepath.FromSlash(path)+"@v"+version.String())
}

// Fetcher downloads pinned requirements into a module cache.
type Fetcher struct {
	// Client performs the HTTPS requests; nil means a default client with
	// FetchTimeout. Redirects that leave https are refused.
	Client *http.Client
	// Cache is the module cache directory.
	Cache string
	// Log receives one line per action; nil discards.
	Log func(format string, args ...interface{})
	// Verify, when set, checks an extracted module before it is installed:
	// it receives the staging directory and the required version and may
	// refuse (the API-honesty check of docs/spec/82-package-semver.md
	// section 7 compares the archive's carried api.json with the code).
	Verify func(dir string, version packageapi.Version) error
}

func (f *Fetcher) client() *http.Client {
	client := f.Client
	if client == nil {
		client = &http.Client{Timeout: FetchTimeout}
	}
	checkRedirect := client.CheckRedirect
	client.CheckRedirect = func(req *http.Request, via []*http.Request) error {
		if len(via) >= 10 {
			return errors.New("too many redirects")
		}
		if req.URL.Scheme != "https" {
			return fmt.Errorf("redirect to %s leaves https", req.URL)
		}
		if checkRedirect != nil {
			return checkRedirect(req, via)
		}
		return nil
	}
	return client
}

func (f *Fetcher) log(format string, args ...interface{}) {
	if f.Log != nil {
		f.Log(format, args...)
	}
}

// Download fetches every pinned requirement of a manifest that is not yet in
// the cache. Requirements without a location are skipped: they are expected
// from a replace directive or an already-populated cache.
func (f *Fetcher) Download(ctx context.Context, manifest Manifest) error {
	if f.Cache == "" {
		return errors.New("no module cache directory (set $OAKMODCACHE)")
	}
	for _, requirement := range manifest.Requires {
		if requirement.Location == "" {
			continue
		}
		target := CacheDir(f.Cache, requirement.Path, requirement.Version)
		if _, err := os.Stat(filepath.Join(target, ManifestFile)); err == nil {
			f.log("%s v%s: cached", requirement.Path, requirement.Version)
			continue
		}
		if err := f.fetchOne(ctx, requirement, target); err != nil {
			return fmt.Errorf("%s v%s: %w", requirement.Path, requirement.Version, err)
		}
		f.log("%s v%s: downloaded and verified", requirement.Path, requirement.Version)
	}
	return nil
}

func (f *Fetcher) fetchOne(ctx context.Context, requirement Requirement, target string) error {
	if err := ValidateLocation(requirement.Location); err != nil {
		return err
	}
	digest, err := ParseDigest(requirement.Digest)
	if err != nil {
		return err
	}
	request, err := http.NewRequestWithContext(ctx, http.MethodGet, requirement.Location, nil)
	if err != nil {
		return err
	}
	response, err := f.client().Do(request)
	if err != nil {
		return err
	}
	defer response.Body.Close()
	if response.StatusCode != http.StatusOK {
		return fmt.Errorf("%s: HTTP %d", requirement.Location, response.StatusCode)
	}
	archive, err := readBounded(response.Body, MaxArchiveBytes)
	if err != nil {
		return err
	}
	sum := sha256.Sum256(archive)
	if actual := hex.EncodeToString(sum[:]); actual != digest {
		return fmt.Errorf("archive digest sha256:%s does not match pinned sha256:%s; refusing to extract", actual, digest)
	}
	if err := os.MkdirAll(filepath.Dir(target), 0o755); err != nil {
		return err
	}
	staging, err := os.MkdirTemp(filepath.Dir(target), ".fetch-")
	if err != nil {
		return err
	}
	defer os.RemoveAll(staging)
	if err := ExtractTarGz(archive, staging); err != nil {
		return err
	}
	manifest, err := os.ReadFile(filepath.Join(staging, ManifestFile))
	if err != nil {
		return fmt.Errorf("archive has no %s at its root", ManifestFile)
	}
	parsed, err := ParseManifest(string(manifest))
	if err != nil {
		return fmt.Errorf("archive %s: %v", ManifestFile, err)
	}
	if parsed.Path != requirement.Path {
		return fmt.Errorf("archive declares module %q, required as %q", parsed.Path, requirement.Path)
	}
	if f.Verify != nil {
		if err := f.Verify(staging, requirement.Version); err != nil {
			return fmt.Errorf("archive verification failed: %w", err)
		}
	}
	if err := os.Rename(staging, target); err != nil {
		return err
	}
	return nil
}

func readBounded(reader io.Reader, limit int64) ([]byte, error) {
	data, err := io.ReadAll(io.LimitReader(reader, limit+1))
	if err != nil {
		return nil, err
	}
	if int64(len(data)) > limit {
		return nil, fmt.Errorf("archive exceeds %d bytes", limit)
	}
	return data, nil
}

// ExtractTarGz unpacks a gzip-compressed tar archive into dir. Only regular
// files and directories are admitted; every member path must be relative,
// free of `..` segments, and stay inside dir; symlinks, hard links, devices,
// and any other member kind are rejected. Entry count and total decompressed
// size are capped. An optional single top-level directory (the usual
// `name-version/` wrapper of source archives) is stripped when every member
// lies under it and it carries the manifest.
func ExtractTarGz(archive []byte, dir string) error {
	gz, err := gzip.NewReader(strings.NewReader(string(archive)))
	if err != nil {
		return fmt.Errorf("archive is not gzip: %v", err)
	}
	defer gz.Close()
	reader := tar.NewReader(gz)
	var members []tarMember
	var total int64
	for {
		header, err := reader.Next()
		if errors.Is(err, io.EOF) {
			break
		}
		if err != nil {
			return fmt.Errorf("archive: %v", err)
		}
		if len(members) >= MaxArchiveEntries {
			return fmt.Errorf("archive has more than %d members", MaxArchiveEntries)
		}
		switch header.Typeflag {
		case tar.TypeReg, tar.TypeDir:
		default:
			return fmt.Errorf("archive member %q has an unsupported kind (only regular files and directories are extracted)", header.Name)
		}
		if err := validateMemberPath(header.Name); err != nil {
			return err
		}
		var data []byte
		if header.Typeflag == tar.TypeReg {
			if header.Size < 0 || total+header.Size > MaxExtractedBytes {
				return fmt.Errorf("archive exceeds %d decompressed bytes", MaxExtractedBytes)
			}
			data, err = readBounded(reader, header.Size)
			if err != nil {
				return fmt.Errorf("archive member %q: %v", header.Name, err)
			}
			total += int64(len(data))
			if total > MaxExtractedBytes {
				return fmt.Errorf("archive exceeds %d decompressed bytes", MaxExtractedBytes)
			}
		}
		members = append(members, tarMember{header: header, data: data})
	}
	prefix := commonWrapper(members)
	for _, m := range members {
		name := strings.TrimPrefix(m.header.Name, prefix)
		name = strings.Trim(name, "/")
		if name == "" {
			continue
		}
		full := filepath.Join(dir, filepath.FromSlash(name))
		if rel, err := filepath.Rel(dir, full); err != nil || rel == ".." || strings.HasPrefix(rel, ".."+string(filepath.Separator)) {
			return fmt.Errorf("archive member %q escapes the extraction directory", m.header.Name)
		}
		if m.header.Typeflag == tar.TypeDir {
			if err := os.MkdirAll(full, 0o755); err != nil {
				return err
			}
			continue
		}
		if err := os.MkdirAll(filepath.Dir(full), 0o755); err != nil {
			return err
		}
		if err := os.WriteFile(full, m.data, 0o644); err != nil {
			return err
		}
	}
	return nil
}

func validateMemberPath(name string) error {
	if name == "" {
		return errors.New("archive member has an empty name")
	}
	if strings.HasPrefix(name, "/") || strings.Contains(name, "\\") {
		return fmt.Errorf("archive member %q is not a relative slash path", name)
	}
	for _, segment := range strings.Split(strings.Trim(name, "/"), "/") {
		if segment == "" || segment == ".." {
			return fmt.Errorf("archive member %q has an invalid path segment", name)
		}
	}
	return nil
}

type tarMember struct {
	header *tar.Header
	data   []byte
}

// commonWrapper returns "dir/" when every member lies under one top-level
// directory that carries the manifest (the `name-version/` wrapper of source
// archives); otherwise "".
func commonWrapper(members []tarMember) string {
	prefix := ""
	hasManifest := false
	for _, m := range members {
		name := strings.Trim(m.header.Name, "/")
		if name == "" {
			continue
		}
		top := name
		if index := strings.IndexByte(name, '/'); index >= 0 {
			top = name[:index]
		} else if m.header.Typeflag != tar.TypeDir {
			return ""
		}
		if prefix == "" {
			prefix = top
		} else if prefix != top {
			return ""
		}
		if name == prefix+"/"+ManifestFile {
			hasManifest = true
		}
	}
	if prefix == "" || !hasManifest {
		return ""
	}
	return prefix + "/"
}
