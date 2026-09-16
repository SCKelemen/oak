package semir

import (
	"bytes"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"runtime"
	"strings"
	"testing"
)

type aarch64HerdCase struct {
	file            string
	observation     string
	positive        string
	negative        string
	herdHash        string
	upstreamPath    string
	upstreamBlob    string
	checkBBMWarning bool
	bbmWarning      bool
}

var (
	herdRevisionPattern = regexp.MustCompile(`^[0-9a-f]{40}$`)
	herdObservation     = regexp.MustCompile(`(?m)^Observation[ \t]+[^ \t\r\n]+[ \t]+(Never|Sometimes)[ \t]+([0-9]+)[ \t]+([0-9]+)[ \t]*$`)
	herdHash            = regexp.MustCompile(`(?m)^Hash=([0-9a-f]{32})[ \t]*$`)
	herdBBMWarning      = regexp.MustCompile(`(?m)^Flag[ \t]+Warning-BBM-expected[ \t]*$`)
)

func requireAArch64Herd(t *testing.T, message string) {
	t.Helper()
	if os.Getenv("OAK_REQUIRE_HERD7") == "1" {
		t.Fatalf("pinned AArch64 Herd oracle required by OAK_REQUIRE_HERD7: %s", message)
	}
	t.Skip(message)
}

// requirePinnedHerdCatalogueSource compares a checked-in litmus test with the
// exact blob at the already validated Herdtools7 revision. Reading through
// `git show REV:path` prevents a dirty model checkout from becoming authority.
func requirePinnedHerdCatalogueSource(t *testing.T, modelCheckout, revision,
	upstreamPath, upstreamBlob, localPath string) {
	t.Helper()
	wantTreeEntry := "100644 blob " + upstreamBlob + "\t" + upstreamPath
	tree := exec.Command("git", "-C", modelCheckout, "ls-tree", revision, "--", upstreamPath)
	treeBytes, err := tree.CombinedOutput()
	if err != nil {
		t.Fatalf("identify official Herd catalogue source: %v\n%s", err, treeBytes)
	}
	if got := strings.TrimSpace(string(treeBytes)); got != wantTreeEntry {
		t.Fatalf("official Herd catalogue tree entry = %q, want %q", got, wantTreeEntry)
	}

	official := exec.Command("git", "-C", modelCheckout, "show", revision+":"+upstreamPath)
	officialBytes, err := official.Output()
	if err != nil {
		t.Fatalf("read official Herd catalogue source: %v", err)
	}
	localBytes, err := os.ReadFile(localPath)
	if err != nil {
		t.Fatalf("read checked-in Herd catalogue source: %v", err)
	}
	if !bytes.Equal(localBytes, officialBytes) {
		t.Fatalf("%s differs from pinned official source %s:%s",
			localPath, revision, upstreamPath)
	}
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
		{file: "SB-dsb-ish.litmus", observation: "Never"},
		{file: "SB-dsb-sy.litmus", observation: "Never"},
		{file: "SB-isb.litmus", observation: "Sometimes"},
		{file: "IRIW-seq-cst.litmus", observation: "Never"},
		{file: "LB-seq-cst.litmus", observation: "Sometimes"},
		{
			file:            "MP+tlbi-sync.ishsptev0pteoa.v1+pos.litmus",
			observation:     "Never",
			positive:        "0",
			negative:        "9",
			herdHash:        "3334f24571de5375d4587a1f8961673f",
			upstreamPath:    "catalogue/aarch64-BBM/tests/MP+tlbi-sync.ishsptev0pteoa.v1+pos.litmus",
			upstreamBlob:    "41a19bf1d8225d1f112da890d06484a42afa6ac4",
			checkBBMWarning: true,
		},
		{
			file:            "CoRR+PteOA.DB0.litmus",
			observation:     "Sometimes",
			positive:        "1",
			negative:        "3",
			herdHash:        "6be305e913d02515c5f0e3e4bc81ef26",
			upstreamPath:    "catalogue/aarch64-BBM/tests/CoRR+PteOA.DB0.litmus",
			upstreamBlob:    "931e24b91f7916f7296a037c546792da2fb721d0",
			checkBBMWarning: true,
			bbmWarning:      true,
		},
	}
	for _, test := range cases {
		t.Run(test.file, func(t *testing.T) {
			path := filepath.Join(litmusDir, test.file)
			if test.upstreamPath != "" {
				requirePinnedHerdCatalogueSource(t, modelCheckout, revision,
					test.upstreamPath, test.upstreamBlob, path)
			}
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
			if test.positive != "" &&
				(matches[0][2] != test.positive || matches[0][3] != test.negative) {
				t.Fatalf("official AArch64 model witnesses are %s/%s, want %s/%s\n%s",
					matches[0][2], matches[0][3], test.positive, test.negative, output)
			}
			if test.herdHash != "" {
				hashes := herdHash.FindAllStringSubmatch(string(output), -1)
				if len(hashes) != 1 || hashes[0][1] != test.herdHash {
					t.Fatalf("official AArch64 model hash changed, want %s\n%s",
						test.herdHash, output)
				}
			}
			if test.checkBBMWarning {
				warnings := herdBBMWarning.FindAllString(string(output), -1)
				wantWarnings := 0
				if test.bbmWarning {
					wantWarnings = 1
				}
				if len(warnings) != wantWarnings ||
					strings.Count(string(output), "Warning-BBM-expected") != wantWarnings {
					t.Fatalf("official AArch64 model has %d BBM warnings, want %d\n%s",
						len(warnings), wantWarnings, output)
				}
			}
		})
	}
}
