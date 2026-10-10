package main

import (
	"bytes"
	"crypto/sha256"
	"debug/elf"
	_ "embed"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"regexp"
	"runtime"
	"runtime/debug"
	"sort"
	"strings"
	"sync"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/internal/nativetiming"
	"github.com/SCKelemen/oak/stdlib"
	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/toolchain"
)

// This is deliberately a reviewed inventory, not an automatically shrinking
// count. Its names and ordered source identities must also match a fresh
// frontend pass before a prerequisite can be produced or consumed.
//
//go:embed .github/scripts/native_prover_inventory.json
var nativeProverInventoryJSON []byte

const nativeProverEligible = 1087

// Fourteen solver externs plus the imported host-write shim dependency.
const nativeProverExterns = 15
const nativeProverRecipeVersion = "hybrid-native-c-v1/fresh-verdicts/default-search/race"

type nativeProverContext struct {
	SourceSHA            string `json:"source_sha"`
	SourceTree           string `json:"source_tree"`
	SourceContentsSHA256 string `json:"source_contents_sha256"`
	RunID                string `json:"run_id"`
	RunAttempt           string `json:"run_attempt"`
	Shard                string `json:"shard"`
	InventorySHA256      string `json:"inventory_sha256"`
	PlanSHA256           string `json:"plan_sha256"`
}

type nativeProverGoBuild struct {
	Version      string            `json:"version"`
	Main         debug.Module      `json:"main"`
	Dependencies []*debug.Module   `json:"dependencies"`
	Settings     map[string]string `json:"settings"`
}

type nativeProverCC struct {
	Path    string   `json:"path"`
	SHA256  string   `json:"sha256"`
	Version string   `json:"version"`
	Args    []string `json:"args"`
}

type nativeProverRecipe struct {
	SchemaVersion  int                           `json:"schema_version"`
	RecipeVersion  string                        `json:"recipe_version"`
	Context        nativeProverContext           `json:"context"`
	HarnessSHA256  string                        `json:"harness_sha256"`
	GoBuild        nativeProverGoBuild           `json:"go_build"`
	Sources        map[string]string             `json:"sources"`
	SupportSources map[string]string             `json:"support_sources"`
	LinkInputs     []compiler.LinkInput          `json:"link_inputs"`
	Inventory      compiler.NativeBuildInventory `json:"inventory"`
	Platform       string                        `json:"platform"`
	Target         string                        `json:"target"`
	AsmMode        string                        `json:"asm_mode"`
	ObjectFormat   string                        `json:"object_format"`
	CPU            string                        `json:"cpu"`
	COptLevel      int                           `json:"c_opt_level"`
	CC             nativeProverCC                `json:"cc"`
	ToolchainFiles map[string]string             `json:"toolchain_files"`
}

type nativeProverSuccess struct {
	SchemaVersion int               `json:"schema_version"`
	RecipeSHA256  string            `json:"recipe_sha256"`
	ReportSHA256  string            `json:"report_sha256"`
	ProgramSHA256 string            `json:"program_sha256"`
	ObjectSHA256  string            `json:"object_sha256"`
	SolverSHA256  string            `json:"solver_sha256"`
	LinkCommand   []string          `json:"link_command"`
	RuntimeFiles  map[string]string `json:"runtime_files"`
}

func oakSolverSources() map[string]string {
	return map[string]string{"oak.mod": "module oak.prove.solver\noak 0.1.0\n", "bdd.oak": oakSolverSource, "lower.oak": oakLoweringSource, "syntax.oak": oakSyntaxSource, "tree.oak": oakTreeSource, "protocol.oak": oakProtocolSource, "shell.oak": oakShellSource, "lean.oak": oakLeanSource, "explore.oak": oakExploreSource, "witness.oak": oakWitnessSource, "driver.oak": oakDriverHelpersSource, "lrat.oak": oakLRATSource, "sat.oak": oakSATSource, "model.oak": oakModelSource, "cnf.oak": oakCNFSource, "certify.oak": oakCertifySource, "main.oak": oakSolverDriverSource}
}

func nativeDigest(data []byte) string { sum := sha256.Sum256(data); return hex.EncodeToString(sum[:]) }

// Evidence itself may not contain symlinks, including an ancestor directory.
// System toolchain symlinks are separately resolved and bound to actual bytes.
func nativeRegular(path string) ([]byte, error) {
	absolute, err := filepath.Abs(path)
	if err != nil {
		return nil, err
	}
	for part := absolute; ; part = filepath.Dir(part) {
		info, err := os.Lstat(part)
		if err != nil {
			return nil, err
		}
		if info.Mode()&os.ModeSymlink != 0 {
			return nil, fmt.Errorf("symlink evidence: %s", part)
		}
		if part == filepath.Dir(part) {
			break
		}
	}
	info, err := os.Stat(absolute)
	if err != nil {
		return nil, err
	}
	if !info.Mode().IsRegular() {
		return nil, fmt.Errorf("not a regular evidence file: %s", path)
	}
	return os.ReadFile(absolute)
}

func nativeFileDigest(path string) (string, error) {
	data, err := nativeRegular(path)
	if err != nil {
		return "", err
	}
	return nativeDigest(data), nil
}

// Reject duplicate keys, unknown/missing fields (at every struct level),
// trailing data, and truncated receipts instead of accepting JSON's last key.
func nativeDecode(data []byte, value any) error {
	decoder := json.NewDecoder(bytes.NewReader(data))
	var walk func() error
	walk = func() error {
		token, err := decoder.Token()
		if err != nil {
			return err
		}
		delimiter, ok := token.(json.Delim)
		if !ok {
			return nil
		}
		if delimiter == '{' {
			seen := map[string]bool{}
			for decoder.More() {
				key, err := decoder.Token()
				if err != nil {
					return err
				}
				name, ok := key.(string)
				if !ok || seen[name] {
					return errors.New("duplicate or invalid JSON key")
				}
				seen[name] = true
				if err := walk(); err != nil {
					return err
				}
			}
		} else if delimiter == '[' {
			for decoder.More() {
				if err := walk(); err != nil {
					return err
				}
			}
		} else {
			return errors.New("invalid JSON delimiter")
		}
		_, err = decoder.Token()
		return err
	}
	if err := walk(); err != nil {
		return err
	}
	if _, err := decoder.Token(); err != io.EOF {
		return errors.New("trailing JSON data")
	}
	decoder = json.NewDecoder(bytes.NewReader(data))
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(value); err != nil {
		return err
	}
	var original, canonical any
	if err := json.Unmarshal(data, &original); err != nil {
		return err
	}
	encoded, err := json.Marshal(value)
	if err != nil {
		return err
	}
	if err := json.Unmarshal(encoded, &canonical); err != nil {
		return err
	}
	if !reflect.DeepEqual(original, canonical) {
		return errors.New("missing or noncanonical JSON fields")
	}
	return nil
}

func nativeReadJSON(path string, value any) error {
	data, err := nativeRegular(path)
	if err != nil {
		return err
	}
	return nativeDecode(data, value)
}

func nativeWriteJSON(path string, value any) error {
	data, err := json.MarshalIndent(value, "", "  ")
	if err != nil {
		return err
	}
	return os.WriteFile(path, append(data, '\n'), 0o600)
}

func nativeWriteSources(directory string) error {
	if err := os.Mkdir(directory, 0o700); err != nil {
		return err
	}
	for name, text := range oakSolverSources() {
		if err := os.WriteFile(filepath.Join(directory, name), []byte(text), 0o600); err != nil {
			return err
		}
	}
	return nil
}

func nativeFrontendInventory(directory string) (compiler.NativeBuildInventory, error) {
	return compiler.New().WithPackageDir(directory).WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchArm64}).WithNativeAsm().NativeInventory()
}

// The immutable frontend may be expensive under -race. Reuse only its parsed
// inventory, within this process and under a full byte-derived recipe key.
// Every caller rehashes source, checkout, compiler and toolchain first; neither
// a failed derivation nor a verdict, executable, mtime or existence is cached.
type nativeInventoryMemo struct {
	mu    sync.Mutex
	key   string
	value compiler.NativeBuildInventory
	valid bool
}

func (memo *nativeInventoryMemo) get(key string, derive func() (compiler.NativeBuildInventory, error)) (compiler.NativeBuildInventory, error) {
	memo.mu.Lock()
	defer memo.mu.Unlock()
	clone := func(value compiler.NativeBuildInventory) compiler.NativeBuildInventory {
		return compiler.NativeBuildInventory{Eligible: append([]compiler.NativeBuildInput{}, value.Eligible...), Externs: append([]compiler.NativeBuildInput{}, value.Externs...)}
	}
	if memo.valid && memo.key == key {
		return clone(memo.value), nil
	}
	value, err := derive()
	if err != nil {
		return value, err
	}
	memo.key, memo.value, memo.valid = key, clone(value), true
	return clone(value), nil
}

var nativeFrontendMemo nativeInventoryMemo

func nativeInventoryRecipeKey(recipe nativeProverRecipe) (string, error) {
	recipe.Inventory = compiler.NativeBuildInventory{}
	data, err := json.Marshal(recipe)
	return nativeDigest(data), err
}

func nativeExpectedInventory(directory, key string) (compiler.NativeBuildInventory, error) {
	var expected compiler.NativeBuildInventory
	if err := nativeDecode(nativeProverInventoryJSON, &expected); err != nil {
		return expected, err
	}
	actual, err := nativeFrontendMemo.get(key, func() (compiler.NativeBuildInventory, error) {
		actual, err := nativeFrontendInventory(directory)
		if err != nil {
			return actual, err
		}
		if len(actual.Eligible) != nativeProverEligible || len(actual.Externs) != nativeProverExterns || !reflect.DeepEqual(actual, expected) {
			return actual, errors.New("native prover's reviewed eligible/extern inventory changed")
		}
		return actual, nil
	})
	if err != nil {
		return expected, err
	}
	if len(actual.Eligible) != nativeProverEligible || len(actual.Externs) != nativeProverExterns || !reflect.DeepEqual(actual, expected) {
		return expected, errors.New("native prover's reviewed eligible/extern inventory changed")
	}
	return actual, nil
}

func nativeCommand(name string, args ...string) (string, error) {
	output, err := exec.Command(name, args...).Output()
	if err != nil {
		return "", fmt.Errorf("%s %q: %w", name, args, err)
	}
	return strings.TrimSpace(string(output)), nil
}

func nativeContext(evidenceRoot string) (nativeProverContext, error) {
	var result nativeProverContext
	var err error
	result.SourceSHA, err = nativeCommand("git", "rev-parse", "HEAD")
	if err != nil {
		return result, err
	}
	result.SourceTree, err = nativeCommand("git", "rev-parse", "HEAD^{tree}")
	if err != nil {
		return result, err
	}
	if result.SourceSHA != os.Getenv("GITHUB_SHA") {
		return result, errors.New("native prerequisite checkout differs from GITHUB_SHA")
	}
	for _, command := range [][]string{{"diff", "--quiet", "HEAD", "--"}, {"diff", "--quiet", "--cached", "--"}} {
		if _, err = nativeCommand("git", command...); err != nil {
			return result, errors.New("native prerequisite requires an unchanged tracked checkout")
		}
	}
	untracked, err := exec.Command("git", "ls-files", "--others", "--exclude-standard", "-z").Output()
	if err != nil {
		return result, err
	}
	evidenceRoot, err = filepath.Abs(evidenceRoot)
	if err != nil {
		return result, err
	}
	for _, path := range strings.Split(string(untracked), "\x00") {
		if path == "" {
			continue
		}
		absolute, err := filepath.Abs(path)
		if err != nil {
			return result, err
		}
		relative, err := filepath.Rel(evidenceRoot, absolute)
		if err != nil || relative == ".." || strings.HasPrefix(relative, ".."+string(filepath.Separator)) {
			return result, fmt.Errorf("untracked compiler or embedded input: %s", path)
		}
	}
	files, err := exec.Command("git", "ls-files", "-z").Output()
	if err != nil {
		return result, err
	}
	hash := sha256.New()
	for _, path := range strings.Split(string(files), "\x00") {
		if path == "" {
			continue
		}
		data, err := nativeRegular(path)
		if err != nil {
			return result, err
		}
		fmt.Fprintf(hash, "%d:%s:%s\n", len(path), path, nativeDigest(data))
	}
	result.SourceContentsSHA256 = hex.EncodeToString(hash.Sum(nil))
	result.RunID, result.RunAttempt, result.Shard = os.Getenv("GITHUB_RUN_ID"), os.Getenv("GITHUB_RUN_ATTEMPT"), "support"
	decimal := regexp.MustCompile(`^[1-9][0-9]*$`)
	if !decimal.MatchString(result.RunID) || !decimal.MatchString(result.RunAttempt) {
		return result, errors.New("missing native prerequisite run/attempt identity")
	}
	result.InventorySHA256, err = nativeFileDigest(".github/scripts/native_arm64_inventory.json")
	if err != nil {
		return result, err
	}
	result.PlanSHA256, err = nativeFileDigest(".github/scripts/native_arm64_shards.json")
	return result, err
}

func nativeCheckEnvironment() error {
	if runtime.GOOS != "linux" || runtime.GOARCH != "arm64" {
		return errors.New("native prover prerequisite requires native Linux ARM64")
	}
	if cOptLevel != 1 {
		return errors.New("native prover prerequisite requires ordinary C optimization level 1")
	}
	return nativeCheckEnvironmentControls()
}

func nativeCheckEnvironmentControls() error {
	// Environment experiments may weaken or change the recipe. Diagnostics and
	// the prerequisite selector are the only accepted Oak overrides here.
	allowed := map[string]bool{"OAK_NATIVE_PREREQUISITE": true, "OAK_SOLVER_NATIVE": true, "OAK_NATIVE_TIMING": true}
	for _, entry := range os.Environ() {
		name, value, _ := strings.Cut(entry, "=")
		if value != "" && (strings.HasPrefix(name, "OAK_") || name == "OAKOPT" || name == "OAKCPU" || name == "OAKCACHE" || name == "OAKMODCACHE") && !allowed[name] {
			return fmt.Errorf("unreviewed native prerequisite environment: %s", name)
		}
	}
	for _, name := range []string{"CPATH", "C_INCLUDE_PATH", "CPLUS_INCLUDE_PATH", "LIBRARY_PATH", "COMPILER_PATH", "GCC_EXEC_PREFIX", "LD_PRELOAD", "LD_LIBRARY_PATH", "LD_RUN_PATH", "LDEMULATION", "GOFLAGS", "GOEXPERIMENT", "GORACE", "CGO_CFLAGS", "CGO_CPPFLAGS", "CGO_CXXFLAGS", "CGO_LDFLAGS"} {
		if os.Getenv(name) != "" {
			return fmt.Errorf("unreviewed toolchain environment: %s", name)
		}
	}
	return nil
}

func nativeSystemFile(files map[string]string, path string) error {
	resolved, err := filepath.EvalSymlinks(path)
	if err != nil {
		return err
	}
	resolved, err = filepath.Abs(resolved)
	if err != nil {
		return err
	}
	if _, ok := files[resolved]; ok {
		return nil
	}
	data, err := nativeRegular(resolved)
	if err != nil {
		return err
	}
	files[resolved] = nativeDigest(data)
	return nil
}

func nativeSystemTree(files map[string]string, root string) error {
	visited := map[string]bool{}
	var walk func(string) error
	walk = func(root string) error {
		root, err := filepath.EvalSymlinks(root)
		if err != nil {
			return err
		}
		if visited[root] {
			return nil
		}
		visited[root] = true
		return filepath.WalkDir(root, func(path string, entry fs.DirEntry, err error) error {
			if err != nil {
				return err
			}
			if entry.IsDir() {
				return nil
			}
			info, err := os.Stat(path)
			if err != nil {
				return err
			}
			if info.IsDir() {
				return walk(path)
			}
			return nativeSystemFile(files, path)
		})
	}
	return walk(root)
}

func nativeELF(path string, object bool) error {
	data, err := nativeRegular(path)
	if err != nil {
		return err
	}
	file, err := elf.NewFile(bytes.NewReader(data))
	if err != nil {
		return err
	}
	defer file.Close()
	if file.Machine != elf.EM_AARCH64 || file.Class != elf.ELFCLASS64 || file.Data != elf.ELFDATA2LSB {
		return errors.New("native prerequisite is not AArch64 ELF64")
	}
	if object && file.Type != elf.ET_REL || !object && file.Type != elf.ET_EXEC && file.Type != elf.ET_DYN {
		return errors.New("native prerequisite has the wrong ELF type")
	}
	return nil
}

func nativeRuntimeFiles(binary string) (map[string]string, error) {
	result := map[string]string{}
	output, err := nativeCommand("ldd", binary)
	if err != nil {
		return nil, err
	}
	for _, line := range strings.Split(output, "\n") {
		for _, word := range strings.Fields(line) {
			if strings.HasPrefix(word, "/") {
				if err := nativeSystemFile(result, word); err != nil {
					return nil, err
				}
			}
		}
		if strings.Contains(line, "not found") {
			return nil, fmt.Errorf("unresolved runtime dependency: %s", line)
		}
	}
	if len(result) == 0 {
		return nil, errors.New("no resolved runtime dependencies")
	}
	return result, nil
}

// Ubuntu's host GCC toolchain is the deliberately bounded supported recipe.
// Bind its actual programs, startup/link libraries, headers and shared runtime
// bytes. A driver that cannot enumerate these is an error, not weak identity.
func nativeToolchain(driver toolchain.Driver) (nativeProverCC, map[string]string, error) {
	var cc nativeProverCC
	files := map[string]string{}
	path, err := filepath.EvalSymlinks(driver.Path)
	if err != nil {
		return cc, nil, err
	}
	cc.Path, err = filepath.Abs(path)
	if err != nil {
		return cc, nil, err
	}
	if driver.Kind != "host" || driver.Static || driver.Object {
		return cc, nil, errors.New("native prerequisite requires the host C driver")
	}
	cc.Args = append(append([]string{}, driver.Args...), ccArgs()...)
	cc.Version, err = nativeCommand(cc.Path, "--version")
	if err != nil {
		return cc, nil, err
	}
	if !strings.Contains(cc.Version, "Free Software Foundation") {
		return cc, nil, errors.New("native prerequisite toolchain enumeration requires host GCC")
	}
	if err := nativeSystemFile(files, cc.Path); err != nil {
		return cc, nil, err
	}
	cc.SHA256 = files[cc.Path]
	for _, program := range []string{"cc1", "collect2", "as", "ld"} {
		path, err := nativeCommand(cc.Path, "-print-prog-name="+program)
		if err != nil {
			return cc, nil, err
		}
		if !filepath.IsAbs(path) {
			path, err = exec.LookPath(path)
			if err != nil {
				return cc, nil, err
			}
		}
		if err := nativeSystemFile(files, path); err != nil {
			return cc, nil, err
		}
		dependencies, err := nativeRuntimeFiles(path)
		if err != nil {
			return cc, nil, err
		}
		for name, digest := range dependencies {
			files[name] = digest
		}
	}
	for _, library := range []string{"crt1.o", "Scrt1.o", "crti.o", "crtn.o", "crtbegin.o", "crtbeginS.o", "crtend.o", "crtendS.o", "libgcc.a", "libgcc_s.so", "libgcc_s.so.1", "libc.so", "libc.so.6", "libc_nonshared.a", "libm.so", "libm.so.6"} {
		path, err := nativeCommand(cc.Path, "-print-file-name="+library)
		if err != nil {
			return cc, nil, err
		}
		if path == library {
			return cc, nil, fmt.Errorf("unresolved toolchain input: %s", library)
		}
		if err := nativeSystemFile(files, path); err != nil {
			return cc, nil, err
		}
		// GNU libc/libm may be linker scripts, with additional runtime or
		// archive inputs. Bind every absolute input those scripts name.
		data, err := os.ReadFile(path)
		if err != nil {
			return cc, nil, err
		}
		if !bytes.HasPrefix(data, []byte("\x7fELF")) && !bytes.HasPrefix(data, []byte("!<arch>")) {
			for _, token := range strings.FieldsFunc(string(data), func(r rune) bool { return r == '(' || r == ')' || r == '\n' || r == '\r' || r == '\t' || r == ' ' }) {
				if strings.HasPrefix(token, "/") && token != "/*" {
					if err := nativeSystemFile(files, token); err != nil {
						return cc, nil, err
					}
				}
			}
		}
	}
	include, err := nativeCommand(cc.Path, "-print-file-name=include")
	if err != nil {
		return cc, nil, err
	}
	for _, root := range []string{"/usr/include", filepath.Dir(include)} {
		if err := nativeSystemTree(files, root); err != nil {
			return cc, nil, err
		}
	}
	dependencies, err := nativeRuntimeFiles(cc.Path)
	if err != nil {
		return cc, nil, err
	}
	for name, digest := range dependencies {
		files[name] = digest
	}
	return cc, files, nil
}

func nativeRecipe(sourceDir string) (nativeProverRecipe, error) {
	var result nativeProverRecipe
	if err := nativeCheckEnvironment(); err != nil {
		return result, err
	}
	result.SchemaVersion, result.RecipeVersion = 1, nativeProverRecipeVersion
	var err error
	result.Context, err = nativeContext(filepath.Dir(filepath.Dir(sourceDir)))
	if err != nil {
		return result, err
	}
	executable, err := os.Executable()
	if err != nil {
		return result, err
	}
	result.HarnessSHA256, err = nativeFileDigest(executable)
	if err != nil {
		return result, err
	}
	info, ok := debug.ReadBuildInfo()
	if !ok {
		return result, errors.New("missing compiler Go build information")
	}
	result.GoBuild = nativeProverGoBuild{Version: info.GoVersion, Main: info.Main, Dependencies: info.Deps, Settings: map[string]string{}}
	for _, setting := range info.Settings {
		result.GoBuild.Settings[setting.Key] = setting.Value
	}
	if info.GoVersion != "go1.27.1" || result.GoBuild.Settings["-race"] != "true" || result.GoBuild.Settings["CGO_ENABLED"] != "1" || result.GoBuild.Settings["GOOS"] != "linux" || result.GoBuild.Settings["GOARCH"] != "arm64" {
		return result, errors.New("native prerequisite must use the recorded Go 1.27.1 race-enabled native harness")
	}
	result.Sources = map[string]string{}
	result.SupportSources = map[string]string{"stdlib/std.oak": nativeDigest([]byte(stdlib.Prelude)), "stdlib/host.oak": nativeDigest([]byte(stdlib.Packages["host"]))}
	for path, digest := range result.SupportSources {
		actual, err := nativeFileDigest(path)
		if err != nil {
			return result, err
		}
		if actual != digest {
			return result, fmt.Errorf("native support source differs from compiler: %s", path)
		}
	}
	for name, text := range oakSolverSources() {
		data, err := nativeRegular(filepath.Join(sourceDir, name))
		if err != nil {
			return result, err
		}
		if string(data) != text {
			return result, fmt.Errorf("native prover source differs: %s", name)
		}
		result.Sources[name] = nativeDigest(data)
	}
	entries, err := os.ReadDir(sourceDir)
	if err != nil || len(entries) != len(result.Sources) {
		return result, errors.New("unexpected native prover source entries")
	}
	result.Platform, result.Target, result.AsmMode, result.ObjectFormat = "linux/arm64", target.Host().String(), "native", "ELF"
	result.CPU, result.COptLevel = "", cOptLevel
	inputs, err := compiler.New().WithPackageDir(sourceDir).LinkInputs()
	if err != nil {
		return result, err
	}
	result.LinkInputs = append([]compiler.LinkInput{}, inputs...)
	// The reviewed host shim is generated inside program.c. Its declaration
	// comes from stdlib/host.oak and implementation from the bound codegen
	// sources. Additional external objects/shims need an intentional review.
	if len(result.LinkInputs) != 0 {
		return result, errors.New("native prover acquired unreviewed external link inputs")
	}
	driver, err := toolchain.Resolve(target.Host(), toolchain.Options{}, nil, nil)
	if err != nil {
		return result, err
	}
	result.CC, result.ToolchainFiles, err = nativeToolchain(driver)
	if err != nil {
		return result, err
	}
	key, err := nativeInventoryRecipeKey(result)
	if err != nil {
		return result, err
	}
	result.Inventory, err = nativeExpectedInventory(sourceDir, key)
	return result, err
}

func nativeValidateReport(report compiler.NativeBuildReport, expected compiler.NativeBuildInventory) error {
	if report.SchemaVersion != 1 || !reflect.DeepEqual(report.Inventory, expected) || len(report.Functions) != len(expected.Eligible) {
		return errors.New("native report inventory mismatch")
	}
	seen := map[string]bool{}
	declarations := map[string]bool{}
	for _, group := range [][]compiler.NativeBuildInput{expected.Eligible, expected.Externs} {
		for _, input := range group {
			if input.Name == "" || declarations[input.Name] {
				return errors.New("duplicate or empty expected native declaration")
			}
			declarations[input.Name] = true
		}
	}
	nativeCount := 0
	validDigest := regexp.MustCompile(`^[0-9a-f]{64}$`)
	for i, row := range report.Functions {
		if row.Input != expected.Eligible[i] || seen[row.Input.Name] {
			return errors.New("missing, duplicate or reordered native obligation")
		}
		seen[row.Input.Name] = true
		callees := map[string]bool{}
		for _, callee := range row.Callees {
			if !declarations[callee] || callees[callee] {
				return errors.New("unknown or duplicate native callee dependency")
			}
			callees[callee] = true
		}
		if row.Reason == "" || row.Considered < 0 || row.Materialized < 0 || row.Materialized > row.Considered {
			return fmt.Errorf("invalid completion for %s", row.Input.Name)
		}
		seenCandidates := map[compiler.NativeBuildCandidate]bool{}
		for _, candidate := range row.Validations {
			if seenCandidates[candidate] {
				return errors.New("duplicate native validation record")
			}
			seenCandidates[candidate] = true
			if candidate.Cached || !validDigest.MatchString(candidate.BodySHA256) || !validDigest.MatchString(candidate.RecipeSHA256) || candidate.Name == "" {
				return fmt.Errorf("invalid or cached candidate for %s", row.Input.Name)
			}
			switch candidate.Outcome {
			case "proven", "witnessed", "trusted", "mismatch", "refused":
			default:
				return errors.New("unknown candidate outcome")
			}
		}
		switch row.Status {
		case "c-fallback":
			if row.Selected != nil && row.Selected.Outcome == "refused" {
				return errors.New("refused final candidate")
			}
		case "proven", "witnessed", "trusted":
			nativeCount++
			if row.Selected == nil || row.Selected.Outcome != row.Status || len(row.Validations) == 0 {
				return errors.New("native terminal verdict does not match actual selection")
			}
		default:
			return fmt.Errorf("unfinished or failed native obligation %s: %s", row.Input.Name, row.Status)
		}
		if row.Selected != nil {
			if row.Selected.Outcome != "proven" && row.Selected.Outcome != "witnessed" && row.Selected.Outcome != "trusted" {
				return errors.New("refused or mismatched final candidate")
			}
			found := false
			for _, candidate := range row.Validations {
				if reflect.DeepEqual(*row.Selected, candidate) {
					found = true
				}
			}
			if !found {
				return errors.New("selected candidate was not actually validated")
			}
		}
	}
	if nativeCount == 0 {
		return errors.New("C-only substitution for native prover")
	}
	return nil
}

func buildNativeProverArtifact(directory string) error {
	if err := nativeCheckEnvironment(); err != nil {
		return err
	}
	// Never adopt or overwrite an existing directory or interrupted build.
	if err := os.Mkdir(directory, 0o700); err != nil {
		return err
	}
	sourceDir := filepath.Join(directory, "source")
	if err := nativeWriteSources(sourceDir); err != nil {
		return err
	}
	recipe, err := nativeRecipe(sourceDir)
	if err != nil {
		return err
	}
	if err := nativeWriteJSON(filepath.Join(directory, "recipe.json"), recipe); err != nil {
		return err
	}
	timing, err := nativetiming.Start(os.Stderr)
	if err != nil {
		return err
	}
	defer timing.Close()
	var report compiler.NativeBuildReport
	reportCount := 0
	comp := compiler.New().WithPackageDir(sourceDir).WithNativeBodies().WithVerifyFresh().WithNativeBuildReport(func(value compiler.NativeBuildReport) { report, reportCount = value, reportCount+1 })
	code, object, err := emitFor(comp, "native", target.Host(), "")
	// Failed lowering is diagnostic evidence, but never a completed prerequisite.
	if reportCount > 0 {
		if writeErr := nativeWriteJSON(filepath.Join(directory, "report.json"), report); writeErr != nil {
			return writeErr
		}
	}
	if err != nil {
		return err
	}
	if reportCount != 1 {
		return errors.New("missing/duplicate native build report")
	}
	if err := nativeValidateReport(report, recipe.Inventory); err != nil {
		return err
	}
	if len(object) == 0 {
		return errors.New("native prover emitted no native object")
	}
	if err := os.WriteFile(filepath.Join(directory, "program.c"), []byte(code), 0o600); err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(directory, "asm.o"), object, 0o600); err != nil {
		return err
	}
	inputs, err := comp.LinkInputs()
	if err != nil {
		return err
	}
	if !reflect.DeepEqual(append([]compiler.LinkInput{}, inputs...), recipe.LinkInputs) {
		return errors.New("native prover link inputs changed after preparation")
	}
	driver, err := toolchain.Resolve(target.Host(), toolchain.Options{}, nil, nil)
	if err != nil {
		return err
	}
	binary := filepath.Join(directory, "solver")
	var linkCommand []string
	if _, err := compileCWithEvidence(target.Host(), driver, code, object, inputs, binary, &linkCommand); err != nil {
		return err
	}
	if err := nativeELF(binary, false); err != nil {
		return err
	}
	if err := nativeELF(filepath.Join(directory, "asm.o"), true); err != nil {
		return err
	}
	runtimeFiles, err := nativeRuntimeFiles(binary)
	if err != nil {
		return err
	}
	for path, digest := range runtimeFiles {
		if recipe.ToolchainFiles[path] != digest {
			return fmt.Errorf("unbound solver runtime dependency: %s", path)
		}
	}
	// Detect source/compiler/toolchain changes during the long build before any
	// success can be published. This fresh pass never repeats native verification.
	after, err := nativeRecipe(sourceDir)
	if err != nil {
		return err
	}
	if !reflect.DeepEqual(recipe, after) {
		return errors.New("native prerequisite recipe changed during the build")
	}
	success := nativeProverSuccess{SchemaVersion: 1, LinkCommand: linkCommand, RuntimeFiles: runtimeFiles}
	for name, slot := range map[string]*string{"recipe.json": &success.RecipeSHA256, "report.json": &success.ReportSHA256, "program.c": &success.ProgramSHA256, "asm.o": &success.ObjectSHA256, "solver": &success.SolverSHA256} {
		*slot, err = nativeFileDigest(filepath.Join(directory, name))
		if err != nil {
			return err
		}
	}
	staging := filepath.Join(directory, "success.json.pending")
	if err := nativeWriteJSON(staging, success); err != nil {
		return err
	}
	file, err := os.OpenFile(staging, os.O_RDWR, 0)
	if err != nil {
		return err
	}
	err = file.Sync()
	closeErr := file.Close()
	if err != nil {
		return err
	}
	if closeErr != nil {
		return closeErr
	}
	return os.Rename(staging, filepath.Join(directory, "success.json"))
}

func validateNativeProverArtifact(directory string) (string, error) {
	names := []string{"asm.o", "program.c", "recipe.json", "report.json", "solver", "source", "success.json"}
	entries, err := os.ReadDir(directory)
	if err != nil {
		return "", err
	}
	actual := []string{}
	for _, entry := range entries {
		actual = append(actual, entry.Name())
	}
	sort.Strings(actual)
	if !reflect.DeepEqual(actual, names) {
		return "", errors.New("incomplete or unexpected native prerequisite artifact")
	}
	var success nativeProverSuccess
	if err := nativeReadJSON(filepath.Join(directory, "success.json"), &success); err != nil {
		return "", err
	}
	if success.SchemaVersion != 1 {
		return "", errors.New("unsupported native prerequisite receipt")
	}
	for name, expected := range map[string]string{"recipe.json": success.RecipeSHA256, "report.json": success.ReportSHA256, "program.c": success.ProgramSHA256, "asm.o": success.ObjectSHA256, "solver": success.SolverSHA256} {
		actual, err := nativeFileDigest(filepath.Join(directory, name))
		if err != nil {
			return "", err
		}
		if actual != expected {
			return "", fmt.Errorf("native prerequisite digest mismatch: %s", name)
		}
	}
	var recorded nativeProverRecipe
	if err := nativeReadJSON(filepath.Join(directory, "recipe.json"), &recorded); err != nil {
		return "", err
	}
	expected, err := nativeRecipe(filepath.Join(directory, "source"))
	if err != nil {
		return "", err
	}
	if !reflect.DeepEqual(recorded, expected) {
		return "", errors.New("native prerequisite source/compiler/toolchain/recipe/run mismatch")
	}
	var report compiler.NativeBuildReport
	if err := nativeReadJSON(filepath.Join(directory, "report.json"), &report); err != nil {
		return "", err
	}
	if err := nativeValidateReport(report, expected.Inventory); err != nil {
		return "", err
	}
	prefix := append([]string{recorded.CC.Path}, recorded.CC.Args...)
	command := success.LinkCommand
	if len(command) != len(prefix)+5 || !reflect.DeepEqual(command[:len(prefix)], prefix) || command[len(prefix)] != "-o" || command[len(prefix)+1] != filepath.Join(directory, "solver") || filepath.Base(command[len(prefix)+2]) != "program.c" || filepath.Base(command[len(prefix)+3]) != "asm.o" || filepath.Dir(command[len(prefix)+2]) != filepath.Dir(command[len(prefix)+3]) || command[len(prefix)+4] != "-lm" {
		return "", errors.New("native prerequisite linker identity mismatch")
	}
	binary := filepath.Join(directory, "solver")
	if err := nativeELF(binary, false); err != nil {
		return "", err
	}
	if err := nativeELF(filepath.Join(directory, "asm.o"), true); err != nil {
		return "", err
	}
	runtimeFiles, err := nativeRuntimeFiles(binary)
	if err != nil {
		return "", err
	}
	if !reflect.DeepEqual(runtimeFiles, success.RuntimeFiles) {
		return "", errors.New("native prerequisite runtime dependency mismatch")
	}
	for path, digest := range runtimeFiles {
		if recorded.ToolchainFiles[path] != digest {
			return "", errors.New("native prerequisite runtime dependency not in recipe")
		}
	}
	return binary, nil
}
