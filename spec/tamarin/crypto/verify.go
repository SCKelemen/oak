// Command crypto runs the crypto protocol models and checks every expected
// result. Missing tools, warnings, unknown/missing lemmas and timeouts fail.
// Run: go run ./spec/tamarin/crypto -out /tmp/oak-crypto-proofs
package main

import (
	"context"
	"crypto/sha256"
	"embed"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"time"
)

//go:embed *.spthy
var models embed.FS

var expected = map[string]map[string]string{
	"signed_dh.spthy":          {"executable": "verified", "server_authentication": "verified", "forward_secrecy": "verified", "single_accept": "verified"},
	"unauthenticated_dh.spthy": {"executable": "verified", "attacker_knows_session": "verified", "unauthenticated_secrecy": "falsified"},
	"acme_request.spthy":       {"executable": "verified", "request_authentication": "verified", "nonce_single_use": "verified"},
}

var summaryLine = regexp.MustCompile(`(?m)^\s*([A-Za-z_][A-Za-z_0-9]*) \((?:all-traces|exists-trace)\): ([^\r\n]+)$`)
var completedResult = regexp.MustCompile(`^(verified|falsified - found trace) \([0-9]+ steps\)\s*$`)

// Only parse the final summary, never proof bodies or echoed model comments.
func checkSummary(output string, want map[string]string) error {
	at := strings.LastIndex(output, "summary of summaries:")
	if at < 0 {
		return fmt.Errorf("missing Tamarin summary")
	}
	got := map[string]string{}
	for _, m := range summaryLine.FindAllStringSubmatch(output[at:], -1) {
		result := completedResult.FindStringSubmatch(m[2])
		if result == nil {
			return fmt.Errorf("%s: incomplete or unknown result %q", m[1], m[2])
		}
		if _, exists := got[m[1]]; exists {
			return fmt.Errorf("duplicate lemma %s", m[1])
		}
		got[m[1]] = strings.Fields(result[1])[0]
	}
	if len(got) != len(want) {
		return fmt.Errorf("expected %d completed lemmas, got %d", len(want), len(got))
	}
	for name, result := range want {
		if got[name] != result {
			return fmt.Errorf("%s: want %s, got %q", name, result, got[name])
		}
	}
	return nil
}

type modelReport struct {
	File     string            `json:"file"`
	SHA256   string            `json:"sha256"`
	Expected map[string]string `json:"expected"`
	Passed   bool              `json:"passed"`
	Error    string            `json:"error,omitempty"`
}

func run(binary, out string, timeout time.Duration) error {
	if timeout <= 0 {
		return fmt.Errorf("timeout must be positive")
	}
	if err := os.MkdirAll(out, 0755); err != nil {
		return err
	}
	// Remove an earlier aggregate report before starting so a failed tool
	// lookup cannot leave stale successful evidence at the requested path.
	if err := os.Remove(filepath.Join(out, "report.json")); err != nil && !os.IsNotExist(err) {
		return err
	}
	binary, err := exec.LookPath(binary)
	if err != nil {
		return err
	}
	ctx, cancel := context.WithTimeout(context.Background(), timeout)
	version, err := exec.CommandContext(ctx, binary, "--version").CombinedOutput()
	cancel()
	if err != nil {
		return fmt.Errorf("Tamarin version: %w: %s", err, version)
	}
	var reports []modelReport
	var failed bool
	for _, name := range []string{"signed_dh.spthy", "unauthenticated_dh.spthy", "acme_request.spthy"} {
		data, err := models.ReadFile(name)
		if err != nil {
			return err
		}
		path := filepath.Join(out, name)
		if err := os.WriteFile(path, data, 0644); err != nil {
			return err
		}
		ctx, cancel := context.WithTimeout(context.Background(), timeout)
		log, commandErr := exec.CommandContext(ctx, binary, "--quit-on-warning", "--prove", path).CombinedOutput()
		if ctx.Err() != nil {
			commandErr = ctx.Err()
		}
		cancel()
		if err := os.WriteFile(path+".log", log, 0644); err != nil {
			return err
		}
		if commandErr == nil {
			commandErr = checkSummary(string(log), expected[name])
		}
		r := modelReport{File: name, SHA256: fmt.Sprintf("%x", sha256.Sum256(data)), Expected: expected[name], Passed: commandErr == nil}
		if commandErr != nil {
			r.Error = commandErr.Error()
			failed = true
		}
		reports = append(reports, r)
		fmt.Printf("%s: passed=%v %s\n", name, r.Passed, r.Error)
	}
	report := struct {
		Scope       string        `json:"scope"`
		ToolVersion string        `json:"tool_version"`
		Models      []modelReport `json:"models"`
	}{"symbolic models only; no Oak implementation refinement or machine-code proof", string(version), reports}
	data, err := json.MarshalIndent(report, "", "  ")
	if err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(out, "report.json"), append(data, '\n'), 0644); err != nil {
		return err
	}
	if failed {
		return fmt.Errorf("crypto protocol verification failed; inspect %s", out)
	}
	return nil
}

func main() {
	binary := flag.String("tamarin", "tamarin-prover", "Tamarin executable")
	out := flag.String("out", "", "required evidence directory (models, full logs, JSON report)")
	timeout := flag.Duration("timeout", 2*time.Minute, "wall-clock limit per model")
	flag.Parse()
	if *out == "" {
		fmt.Fprintln(os.Stderr, "-out is required")
		os.Exit(2)
	}
	if err := run(*binary, *out, *timeout); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
