package semir

import (
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"runtime"
	"strings"
	"testing"
)

type aarch64HerdCase struct {
	file        string
	observation string
}

var (
	herdRevisionPattern = regexp.MustCompile(`^[0-9a-f]{40}$`)
	herdObservation     = regexp.MustCompile(`(?m)^Observation[ \t]+[^ \t\r\n]+[ \t]+(Never|Sometimes)[ \t]+[0-9]+[ \t]+[0-9]+[ \t]*$`)
)

func requireAArch64Herd(t *testing.T, message string) {
	t.Helper()
	if os.Getenv("OAK_REQUIRE_HERD7") == "1" {
		t.Fatalf("pinned AArch64 Herd oracle required by OAK_REQUIRE_HERD7: %s", message)
	}
	t.Skip(message)
}

func TestLitmusAArch64OfficialModel(t *testing.T) {
	_, source, _, ok := runtime.Caller(0)
	if !ok {
		t.Fatal("locate AArch64 Herd test source")
	}
	repository := filepath.Clean(filepath.Join(filepath.Dir(source), ".."))
	litmusDir := filepath.Join(repository, "spec", "litmus", "aarch64")

	revisionBytes, err := os.ReadFile(filepath.Join(litmusDir, "HERDTOOLS7_COMMIT"))
	if err != nil {
		t.Fatalf("read pinned Herdtools7 revision: %v", err)
	}
	revision := strings.TrimSpace(string(revisionBytes))
	if !herdRevisionPattern.MatchString(revision) {
		t.Fatalf("HERDTOOLS7_COMMIT must contain exactly one lowercase 40-hex commit, got %q", revision)
	}

	herd, err := exec.LookPath("herd7")
	if err != nil {
		requireAArch64Herd(t, "herd7 is not on PATH")
	}
	modelCheckout := os.Getenv("OAK_HERDTOOLS7_DIR")
	if modelCheckout == "" {
		requireAArch64Herd(t, "OAK_HERDTOOLS7_DIR does not name the official model checkout")
	}
	modelCheckout, err = filepath.Abs(modelCheckout)
	if err != nil {
		t.Fatalf("resolve OAK_HERDTOOLS7_DIR: %v", err)
	}

	git := exec.Command("git", "-C", modelCheckout, "rev-parse", "HEAD")
	actualBytes, err := git.CombinedOutput()
	if err != nil {
		requireAArch64Herd(t, "cannot identify the official model checkout: "+strings.TrimSpace(string(actualBytes)))
	}
	actual := strings.TrimSpace(string(actualBytes))
	if actual != revision {
		t.Fatalf("Herdtools7 checkout is %q, want pinned revision %q", actual, revision)
	}
	if err := verifyPinnedCATSourceBytes(modelCheckout, revision); err != nil {
		t.Fatalf("verify pinned CAT source bytes: %v", err)
	}

	model := filepath.Join(modelCheckout, "herd", "libdir", "aarch64.cat")
	if info, err := os.Stat(model); err != nil || !info.Mode().IsRegular() {
		requireAArch64Herd(t, "official aarch64.cat is absent from the pinned checkout")
	}
	cat2lisp := filepath.Join(filepath.Dir(herd), "cat2lisp")
	if info, err := os.Stat(cat2lisp); err != nil || !info.Mode().IsRegular() || info.Mode()&0o111 == 0 {
		requireAArch64Herd(t, "cat2lisp from the pinned Herdtools7 build is absent next to herd7")
	}
	if err := verifyPinnedAArch64CATProjection(cat2lisp, model, filepath.Dir(model)); err != nil {
		t.Fatalf("verify pinned AArch64 CAT projection: %v", err)
	}

	cases := []aarch64HerdCase{
		{file: "MP-release-acquire.litmus", observation: "Never"},
		{file: "SB-seq-cst.litmus", observation: "Never"},
		{file: "SB-full-dmb.litmus", observation: "Never"},
		{file: "SB-dmb-sy.litmus", observation: "Never"},
		{file: "LB-dmb-ishld.litmus", observation: "Never"},
		{file: "SB-dmb-ishld.litmus", observation: "Sometimes"},
		{file: "IRIW-seq-cst.litmus", observation: "Never"},
		{file: "LB-seq-cst.litmus", observation: "Sometimes"},
	}
	for _, test := range cases {
		t.Run(test.file, func(t *testing.T) {
			path := filepath.Join(litmusDir, test.file)
			cmd := exec.Command(herd, "-model", model, path)
			output, err := cmd.CombinedOutput()
			if err != nil {
				t.Fatalf("herd7 failed: %v\n%s", err, output)
			}
			matches := herdObservation.FindAllStringSubmatch(string(output), -1)
			if len(matches) != 1 {
				t.Fatalf("herd7 produced %d parseable Observation lines, want 1\n%s", len(matches), output)
			}
			if got := matches[0][1]; got != test.observation {
				t.Fatalf("official AArch64 model says %s, want %s\n%s", got, test.observation, output)
			}
		})
	}
}
