package testrunner

import (
	"context"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"sort"
	"strings"
)

// SplitMix64's transition is fixed by engineVersion, independent of Go's
// evolving math/rand implementations and of worker/test discovery ordering.
type random struct{ state uint64 }

func (r *random) next() uint64 {
	r.state += 0x9e3779b97f4a7c15
	z := r.state
	z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9
	z = (z ^ (z >> 27)) * 0x94d049bb133111eb
	return z ^ (z >> 31)
}
func randomFor(seed uint64, name string, attempt int) random {
	sum := sha256.Sum256([]byte(name))
	return random{state: seed ^ binary.LittleEndian.Uint64(sum[:8]) ^ uint64(attempt)*0x9e3779b97f4a7c15}
}
func generate(r *random, attempt, max int) []byte {
	if attempt == 0 || max == 0 {
		return nil
	}
	if attempt <= 3 {
		out := make([]byte, max)
		for i := range out {
			if attempt == 2 {
				out[i] = 255
			}
			if attempt == 3 {
				out[i] = byte(i)
			}
		}
		return out
	}
	out := make([]byte, int(r.next()%uint64(max+1)))
	for i := range out {
		out[i] = byte(r.next())
	}
	return out
}
func mutate(r *random, seeds [][]byte, max int) []byte {
	input := append([]byte(nil), seeds[int(r.next()%uint64(len(seeds)))]...)
	if max == 0 {
		return nil
	}
	switch r.next() % 5 {
	case 0:
		if len(input) < max {
			i := int(r.next() % uint64(len(input)+1))
			input = append(input, 0)
			copy(input[i+1:], input[i:])
			input[i] = byte(r.next())
		}
	case 1:
		if len(input) > 0 {
			i := int(r.next() % uint64(len(input)))
			input = append(input[:i], input[i+1:]...)
		}
	case 2:
		if len(input) > 0 {
			i := int(r.next() % uint64(len(input)))
			input[i] ^= 1 << (r.next() % 8)
		}
	case 3:
		if len(input) > 0 {
			input[int(r.next()%uint64(len(input)))] = byte(r.next())
		}
	case 4:
		return generate(r, 4, max)
	}
	return input
}

// Minimize accepts only candidates preserving the caller's failure signature.
// It first deletes chunks, then reduces bytes. Every accepted candidate is
// strictly smaller by (length, lexicographic bytes), so reduction terminates.
// It is budgeted minimization, not a promise of a globally minimal example.
func Minimize(ctx context.Context, input []byte, budget int, fails func([]byte) bool) []byte {
	best := append([]byte(nil), input...)
	try := func(candidate []byte) bool {
		if budget <= 0 || ctx.Err() != nil {
			return false
		}
		budget--
		if fails(candidate) {
			best = append([]byte(nil), candidate...)
			return true
		}
		return false
	}
	for chunk := len(best); chunk > 0 && budget > 0 && ctx.Err() == nil; chunk /= 2 {
		for start := 0; start+chunk <= len(best) && budget > 0 && ctx.Err() == nil; {
			candidate := append(append([]byte(nil), best[:start]...), best[start+chunk:]...)
			if !try(candidate) {
				start += chunk
			}
		}
	}
	for i := 0; i < len(best) && budget > 0 && ctx.Err() == nil; i++ {
		original := best[i]
		if original == 0 {
			continue
		}
		candidate := append([]byte(nil), best...)
		candidate[i] = 0
		if try(candidate) {
			continue
		}
		for step := int(original) / 2; step > 0 && budget > 0 && ctx.Err() == nil; step /= 2 {
			for int(best[i]) >= step && budget > 0 && ctx.Err() == nil {
				candidate = append([]byte(nil), best...)
				candidate[i] -= byte(step)
				if !try(candidate) {
					break
				}
			}
		}
	}
	return best
}

type Artifact struct {
	TimeoutNanos int64  `json:"timeout_nanos"`
	Version      int    `json:"version"`
	Engine       string `json:"engine"`
	Test         string `json:"test"`
	Kind         string `json:"kind"`
	Build        string `json:"build"`
	Seed         uint64 `json:"seed"`
	Attempt      int    `json:"attempt"`
	MaxBytes     int    `json:"max_bytes"`
	Sanitize     bool   `json:"sanitize"`
	Signature    string `json:"signature"`
	Input        []byte `json:"input"` // JSON base64, including arbitrary invalid UTF-8.
}

func readArtifact(path string, max int) (Artifact, error) {
	var a Artifact
	f, err := os.Open(path)
	if err != nil {
		return a, err
	}
	defer f.Close()
	data, err := io.ReadAll(io.LimitReader(f, int64(max)*2+65537))
	if err != nil {
		return a, err
	}
	if len(data) > max*2+65536 {
		return a, fmt.Errorf("oversized replay artifact %s", path)
	}
	decoder := json.NewDecoder(strings.NewReader(string(data)))
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(&a); err != nil {
		return a, fmt.Errorf("%s: %w", path, err)
	}
	var extra any
	if err := decoder.Decode(&extra); err != io.EOF {
		return a, fmt.Errorf("trailing data in %s", path)
	}
	if a.TimeoutNanos <= 0 || a.Version != 1 || a.Engine != engineVersion || !cIdentifier.MatchString(a.Test) || testKind(a.Test) == "" || a.Kind != testKind(a.Test) || len(a.Input) > a.MaxBytes || len(a.Input) > max || a.MaxBytes < 0 || a.MaxBytes > 1<<20 || len(a.Build) != 64 || a.Signature == "" {
		return a, fmt.Errorf("invalid or unsupported replay artifact %s", path)
	}
	if _, err := hex.DecodeString(a.Build); err != nil {
		return a, fmt.Errorf("invalid build fingerprint in %s", path)
	}
	return a, nil
}
func corpusDir(pkg Package, test Test) string {
	return filepath.Join(pkg.Dir, "testdata", "oak", test.Name)
}
func saveArtifact(pkg Package, test Test, a Artifact) (string, error) {
	data, err := json.MarshalIndent(a, "", "  ")
	if err != nil {
		return "", err
	}
	data = append(data, '\n')
	sum := sha256.Sum256(data)
	dir := corpusDir(pkg, test)
	if err := os.MkdirAll(dir, 0755); err != nil {
		return "", err
	}
	path := filepath.Join(dir, hex.EncodeToString(sum[:16])+".json")
	f, err := os.CreateTemp(dir, ".pending-*")
	if err != nil {
		return "", err
	}
	temp := f.Name()
	defer os.Remove(temp)
	if _, err := f.Write(data); err != nil {
		f.Close()
		return "", err
	}
	if err := f.Close(); err != nil {
		return "", err
	}
	if err := os.Rename(temp, path); err != nil {
		return "", err
	}
	return path, nil
}
func loadCorpus(pkg Package, test Test, max int) ([][]byte, error) {
	entries, err := os.ReadDir(corpusDir(pkg, test))
	if os.IsNotExist(err) {
		return nil, nil
	}
	if err != nil {
		return nil, err
	}
	var inputs [][]byte
	for _, entry := range entries {
		if entry.IsDir() || strings.HasPrefix(entry.Name(), ".") {
			continue
		}
		path := filepath.Join(corpusDir(pkg, test), entry.Name())
		switch filepath.Ext(entry.Name()) {
		case ".json":
			a, err := readArtifact(path, max)
			if err != nil {
				return nil, err
			}
			if a.Test != test.Name || a.Kind != test.Kind {
				return nil, fmt.Errorf("corpus identity mismatch: %s", path)
			}
			inputs = append(inputs, a.Input)
		case ".bin":
			f, err := os.Open(path)
			if err != nil {
				return nil, err
			}
			data, err := io.ReadAll(io.LimitReader(f, int64(max)+1))
			f.Close()
			if err != nil {
				return nil, err
			}
			if len(data) > max {
				return nil, fmt.Errorf("corpus input exceeds -max-bytes: %s", path)
			}
			inputs = append(inputs, data)
		}
	}
	// ReadDir already sorts names; explicitly deduplicate by bytes, not build ID.
	seen := map[string]bool{}
	var result [][]byte
	for _, input := range inputs {
		if !seen[string(input)] {
			result = append(result, input)
			seen[string(input)] = true
		}
	}
	sort.Slice(result, func(i, j int) bool { return string(result[i]) < string(result[j]) })
	return result, nil
}
