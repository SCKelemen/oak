package compiler

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"testing"
	"time"
)

// This regression binds the complete pinned official numeric source bytes to
// the reviewed restricted Core theorem on actual Oak source and emitted modules.
// It does not establish a general SpecTec importer, production-compiler
// refinement, or verified authority.
func TestWasmCoreSourceMatchesLean(t *testing.T) {
	lake := findLake()
	if lake == "" {
		if os.Getenv("OAK_REQUIRE_WASM_LEAN") == "1" {
			t.Fatal("required Wasm Core source correspondence needs lake")
		}
		t.Skip("lake unavailable")
	}
	official := loadWasmNumericSources(t)
	root, err := filepath.Abs(filepath.Join("..", "spec", "lean"))
	if err != nil {
		t.Fatal(err)
	}
	evidenceDirectory, err := filepath.Abs(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	leanPath := evidenceDirectory
	if inherited := os.Getenv("LEAN_PATH"); inherited != "" {
		leanPath += string(os.PathListSeparator) + inherited
	}
	run := func(args ...string) string {
		t.Helper()
		ctx, cancel := context.WithTimeout(t.Context(), 20*time.Minute)
		defer cancel()
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = root
		cmd.Env = append(os.Environ(), "LEAN_PATH="+leanPath)
		out := wasmNumericBoundedOutput{limit: wasmNumericMaxOutput, cancel: cancel}
		cmd.Stdout, cmd.Stderr = &out, &out
		err := cmd.Run()
		if out.exceeded {
			t.Fatalf("lake %v: output exceeds %d bytes", args, out.limit)
		}
		if err != nil {
			t.Fatalf("lake %v: %v\n%s", args, err, out.String())
		}
		return out.String()
	}
	run("build", "Oak.WasmCoreSource")
	certificate := loadWasmNumericCheckpoints(t, official, run)
	for i, entry := range wasmNumericInventory() {
		started := time.Now()
		var evidence strings.Builder
		writeWasmNumericEvidenceModule(&evidence, i, certificate[i], official[i])
		module := "NumericEvidence_" + entry.field
		path := filepath.Join(evidenceDirectory, module+".lean")
		object := filepath.Join(evidenceDirectory, module+".olean")
		if err := os.WriteFile(path, []byte(evidence.String()), 0600); err != nil {
			t.Fatal(err)
		}
		// Every evidence module is freshly generated and checked in this run.
		// There is deliberately no prebuilt-object or previous-run fallback.
		out := run("env", "lean", "-j1", "-R", evidenceDirectory, "-o", object, path)
		if err := auditWasmCoreAxioms(out, []string{"Numeric_" + entry.field + ".parsed"}); err != nil {
			t.Fatalf("%s: %v\n%s", module, err, out)
		}
		if info, err := os.Stat(object); err != nil || !info.Mode().IsRegular() || info.Size() == 0 {
			t.Fatalf("missing fresh evidence module %s: %v", object, err)
		}
		t.Logf("%s: kernel checked all %d original bytes and audited parsed theorem in %s", entry.file, len(official[i].bytes), time.Since(started).Round(time.Millisecond))
	}
	var proof strings.Builder
	writeWasmNumericCompositionHeader(&proof)
	writeWasmNumericBundle(&proof)
	writeWasmNumericAcceptance(&proof)
	names := []string{"actualOfficialChecked"}
	for _, tc := range bitwiseModuleCases(t) {
		fmt.Fprintf(&proof, "namespace ActualCore_%s\nnoncomputable def original : List UInt8 := %s\nnoncomputable def emitted : List UInt8 := %s\nnoncomputable def claim : BitwiseSource.Decl := BitwiseSource.fixture .%s\n", tc.name, wasmCoreLeanList([]byte(tc.source)), wasmCoreLeanList(tc.bytes), tc.name)
		proof.WriteString(`theorem source_to_core (s : Store) (a b : BitVec 32) (fuel : Nat) :
    WasmNumericSource.denote WasmNumericSource.bitVecPrimitives actualOfficial claim.op a b =
      some (eval claim.op a b) ∧
    BitwiseSource.Grammar original claim ∧
    LoweringRefinement.evalX (BitwiseSourceLowering.toExpr claim)
      (BitwiseSourceLowering.inputs a b) (fun _ => 0) fuel = some (eval claim.op a b) ∧
    WasmCoreBinary.BinaryModule emitted (module claim.name claim.op) ∧
    ModuleOk (module claim.name claim.op) [closedType] ∧
    Instantiation s (module claim.name claim.op) (allocate s claim.name claim.op)
      (allocatedInstance s claim.name) [] ∧
    exportAddress (allocatedInstance s claim.name) claim.name = some s.functions.length ∧
    Invoke (allocate s claim.name claim.op) s.functions.length [a,b]
      (.call [a,b] (.function s.functions.length) closedType) ∧
    CallSteps (allocate s claim.name claim.op)
      (.call [a,b] (.function s.functions.length) closedType)
      (.result [eval claim.op a b]) ∧
    WasmCoreBitwiseProjection.NumericResult (WasmCoreBitwiseProjection.binop claim.op)
      a b (eval claim.op a b) ∧
    BitwiseModule.invokeModule claim.name emitted a b = .ok (eval claim.op a b) :=
  WasmCoreSource.source_to_core_checked_numeric actualOfficialChecked
    (by decide +kernel : BitwiseSource.accepts original claim .wasm .wasmLocals emitted = true) s a b fuel
`)
		name := "ActualCore_" + tc.name + ".source_to_core"
		names = append(names, name)
		fmt.Fprintf(&proof, "end ActualCore_%s\n#print axioms %s\n", tc.name, name)
		t.Logf("%s: bound checked official numeric sources, %d original Oak source bytes, and %d emitted module bytes to all-input arbitrary-store Core derivation", tc.name, len(tc.source), len(tc.bytes))
	}
	path := filepath.Join(t.TempDir(), "ActualCoreSource.lean")
	if err := os.WriteFile(path, []byte(proof.String()), 0600); err != nil {
		t.Fatal(err)
	}
	dependencies := run("env", "lean", "-j1", "--deps", path)
	if err := auditWasmNumericDependencies(dependencies, evidenceDirectory); err != nil {
		t.Fatalf("final proof must import only this run's fresh numeric evidence: %v\n%s", err, dependencies)
	}
	t.Log("all five numeric evidence imports resolve to this run's freshly checked modules")
	out := run("env", "lean", "-j1", path)
	if err := auditWasmCoreAxioms(out, names); err != nil {
		t.Fatalf("%v\n%s", err, out)
	}
	t.Log("official numeric source acceptance and all three actual-source Core theorem closures passed the standard-logical-axiom allowlist")
}

type wasmNumericSource struct {
	field string
	file  string
	bytes []byte
}

func wasmNumericInventory() []wasmNumericSource {
	return []wasmNumericSource{
		{field: "variables", file: "0.1-aux.vars.spectec"},
		{field: "values", file: "1.1-syntax.values.spectec"},
		{field: "types", file: "1.2-syntax.types.spectec"},
		{field: "instructions", file: "1.3-syntax.instructions.spectec"},
		{field: "numerics", file: "3.1-numerics.scalar.spectec"},
	}
}

// Run the independent provenance verifier without fetching. Only absent sources
// may skip an optional local oracle; wrong bytes and malformed inventories fail.
func loadWasmNumericSources(t *testing.T) []wasmNumericSource {
	t.Helper()
	root := filepath.Join("..", "spec", "wasm-core")
	directory := os.Getenv("OAK_WASM_NUMERIC_SOURCES")
	if directory == "" {
		directory = filepath.Join(root, "upstream")
	}
	directory, err := filepath.Abs(directory)
	if err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), time.Minute)
	defer cancel()
	cmd := exec.CommandContext(ctx, "python3", "-B", filepath.Join(root, "numeric_sources.py"), "--source-dir", directory)
	out, err := cmd.CombinedOutput()
	if err != nil {
		if os.Getenv("OAK_REQUIRE_WASM_LEAN") != "1" &&
			strings.HasPrefix(string(out), "FAIL: Missing numeric source files in ") {
			t.Skipf("official Wasm numeric sources unavailable: %s", out)
		}
		t.Fatalf("verify official Wasm numeric sources: %v\n%s", err, out)
	}

	manifestBytes, err := os.ReadFile(filepath.Join(root, "numeric-sources.json"))
	if err != nil {
		t.Fatal(err)
	}
	var manifest struct {
		Sources []struct {
			File   string `json:"file"`
			Bytes  int    `json:"bytes"`
			SHA256 string `json:"sha256"`
		} `json:"sources"`
	}
	if err := json.Unmarshal(manifestBytes, &manifest); err != nil {
		t.Fatal(err)
	}
	sources := wasmNumericInventory()
	if len(manifest.Sources) != len(sources) {
		t.Fatalf("numeric source manifest has %d entries, want %d", len(manifest.Sources), len(sources))
	}
	for i, entry := range manifest.Sources {
		if entry.File != sources[i].file {
			t.Fatalf("numeric source manifest entry %d is %q, want %q", i, entry.File, sources[i].file)
		}
		data, err := os.ReadFile(filepath.Join(directory, entry.File))
		if err != nil {
			t.Fatal(err)
		}
		// Ensure the bytes embedded into the Lean proof still match the manifest
		// after verification; no text conversion, normalization, or extraction.
		if len(data) != entry.Bytes || fmt.Sprintf("%x", sha256.Sum256(data)) != entry.SHA256 {
			t.Fatalf("numeric source changed after provenance verification: %s", entry.File)
		}
		sources[i].bytes = data
		t.Logf("%s: verified and loaded all %d official source bytes", entry.File, len(data))
	}
	return sources
}

func wasmCoreLeanList(bytes []byte) string {
	return strings.Replace(wasmLeanArray(bytes), "#[", "[", 1)
}

func writeWasmNumericSourceBundle(proof *strings.Builder, sources []wasmNumericSource) {
	for i := range wasmNumericInventory() {
		writeWasmNumericOriginal(proof, i, sources[i].bytes)
	}
	writeWasmNumericBundle(proof)
}

func writeWasmNumericOriginal(proof *strings.Builder, index int, original []byte) {
	field := wasmNumericInventory()[index].field
	fmt.Fprintf(proof, "noncomputable def actualOfficial_%s : _root_.Oak.WasmNumericSource.Bytes := %s\n", field, wasmCoreLeanList(original))
}

func writeWasmNumericBundle(proof *strings.Builder) {
	proof.WriteString("noncomputable def actualOfficial : _root_.Oak.WasmNumericSource.Bundle := {\n")
	for _, entry := range wasmNumericInventory() {
		fmt.Fprintf(proof, "  %s := _root_.actualOfficial_%s\n", entry.field, entry.field)
	}
	proof.WriteString("}\n")
}

const wasmNumericProofOptions = "set_option maxRecDepth 262144\nset_option maxHeartbeats 0\nset_option Elab.async false\nnoncomputable section\n"

func writeWasmNumericCompositionHeader(proof *strings.Builder) {
	proof.WriteString("import Oak.WasmCoreSource\n")
	for _, entry := range wasmNumericInventory() {
		fmt.Fprintf(proof, "import NumericEvidence_%s\n", entry.field)
	}
	proof.WriteString("open Oak Oak.BitwiseFunction Oak.WasmCoreModule\n")
	proof.WriteString(wasmNumericProofOptions)
}

func writeWasmNumericEvidenceModule(proof *strings.Builder, index int, file wasmNumericFile, source wasmNumericSource) {
	proof.WriteString("import Oak.WasmNumericSource\n")
	proof.WriteString(wasmNumericProofOptions)
	writeWasmNumericOriginal(proof, index, source.bytes)
	writeWasmNumericFileCertificate(proof, index, file, source)
	fmt.Fprintf(proof, "#print axioms _root_.Numeric_%s.parsed\n", wasmNumericInventory()[index].field)
}

// Keep the acceptance certificate isolated from source loading and theorem
// instantiation so its proof construction can be optimized independently. The
// untrusted emitter reads a private snapshot of the exact bytes already loaded
// for the literal bundle. Lean subsequently checks every proposed checkpoint,
// reconstruction, and acceptance proof; emitter execution grants no authority.
func loadWasmNumericCheckpoints(t *testing.T, sources []wasmNumericSource, run func(...string) string) []wasmNumericFile {
	t.Helper()
	directory, err := filepath.Abs(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	for _, source := range sources {
		if err := os.WriteFile(filepath.Join(directory, source.file), source.bytes, 0600); err != nil {
			t.Fatal(err)
		}
	}
	data := run("env", "lean", "-j1", "--run", filepath.Join("..", "wasm-core", "NumericCertificate.lean"), directory)
	certificate, err := parseWasmNumericCertificate(data, sources)
	if err != nil {
		t.Fatalf("invalid untrusted numeric checkpoint data: %v", err)
	}
	return certificate
}

const (
	wasmNumericMaxOutput = 8 << 20
	wasmNumericMaxSource = 64 << 10
	wasmNumericMaxChunks = 512
	wasmNumericMaxChunk  = 1024
)

// Bound subprocess output while it is produced, rather than allocating an
// arbitrary output before validating it. The same limit covers stderr.
type wasmNumericBoundedOutput struct {
	buffer   bytes.Buffer
	limit    int
	cancel   context.CancelFunc
	exceeded bool
}

func (out *wasmNumericBoundedOutput) Write(data []byte) (int, error) {
	if len(data) > out.limit-out.buffer.Len() {
		out.exceeded = true
		out.cancel()
		return 0, fmt.Errorf("numeric gate subprocess output exceeds %d bytes", out.limit)
	}
	return out.buffer.Write(data)
}

func (out *wasmNumericBoundedOutput) String() string { return out.buffer.String() }

type wasmNumericToken struct {
	spelling          []byte
	start, stop, line int
}

type wasmNumericChunk struct {
	index, fuelUsed int
	bytes           []byte
	tokens          []wasmNumericToken
}

type wasmNumericFile struct {
	index  int
	chunks []wasmNumericChunk
}

// Streaming schema readers enforce exact required keys, reject duplicates,
// and bound every array before allocation. Only unsigned integral JSON numbers
// are admitted; strings, nulls, floats, exponents, and signed values fail closed.
type wasmNumericJSON struct{ decoder *json.Decoder }

func (r wasmNumericJSON) delimiter(want json.Delim) error {
	token, err := r.decoder.Token()
	if err != nil {
		return err
	}
	if token != want {
		return fmt.Errorf("expected JSON %q, got %v", want, token)
	}
	return nil
}

func (r wasmNumericJSON) object(keys []string, field func(string) error) error {
	if err := r.delimiter('{'); err != nil {
		return err
	}
	seen := make(map[string]bool, len(keys))
	for r.decoder.More() {
		token, err := r.decoder.Token()
		if err != nil {
			return err
		}
		key, ok := token.(string)
		if !ok {
			return fmt.Errorf("non-string JSON object key")
		}
		known := false
		for _, expected := range keys {
			known = known || key == expected
		}
		if !known || seen[key] {
			return fmt.Errorf("unknown or duplicate JSON key %q", key)
		}
		seen[key] = true
		if err := field(key); err != nil {
			return fmt.Errorf("%s: %w", key, err)
		}
	}
	if err := r.delimiter('}'); err != nil {
		return err
	}
	for _, key := range keys {
		if !seen[key] {
			return fmt.Errorf("missing JSON key %q", key)
		}
	}
	return nil
}

func (r wasmNumericJSON) array(limit int, item func() error) error {
	if err := r.delimiter('['); err != nil {
		return err
	}
	for count := 0; r.decoder.More(); count++ {
		if count >= limit {
			return fmt.Errorf("JSON array exceeds %d entries", limit)
		}
		if err := item(); err != nil {
			return err
		}
	}
	return r.delimiter(']')
}

func (r wasmNumericJSON) natural(max int) (int, error) {
	token, err := r.decoder.Token()
	if err != nil {
		return 0, err
	}
	number, ok := token.(json.Number)
	if !ok {
		return 0, fmt.Errorf("expected unsigned JSON integer, got %v", token)
	}
	value, err := strconv.ParseUint(string(number), 10, 64)
	if err != nil || value > uint64(max) {
		return 0, fmt.Errorf("JSON integer %q outside 0..%d", number, max)
	}
	return int(value), nil
}

func (r wasmNumericJSON) byteArray() ([]byte, error) {
	var data []byte
	err := r.array(wasmNumericMaxChunk, func() error {
		value, err := r.natural(255)
		if err == nil {
			data = append(data, byte(value))
		}
		return err
	})
	return data, err
}

func (r wasmNumericJSON) token() (wasmNumericToken, error) {
	var token wasmNumericToken
	err := r.object([]string{"spelling", "start", "stop", "line"}, func(key string) (err error) {
		switch key {
		case "spelling":
			token.spelling, err = r.byteArray()
		case "start":
			token.start, err = r.natural(wasmNumericMaxSource)
		case "stop":
			token.stop, err = r.natural(wasmNumericMaxSource)
		case "line":
			token.line, err = r.natural(wasmNumericMaxSource)
		}
		return err
	})
	return token, err
}

func (r wasmNumericJSON) chunk() (wasmNumericChunk, error) {
	var chunk wasmNumericChunk
	err := r.object([]string{"index", "bytes", "tokens", "fuel_used"}, func(key string) (err error) {
		switch key {
		case "index":
			chunk.index, err = r.natural(wasmNumericMaxChunks - 1)
		case "bytes":
			chunk.bytes, err = r.byteArray()
		case "fuel_used":
			chunk.fuelUsed, err = r.natural(wasmNumericMaxChunk)
		case "tokens":
			err = r.array(wasmNumericMaxChunk, func() error {
				token, err := r.token()
				if err == nil {
					chunk.tokens = append(chunk.tokens, token)
				}
				return err
			})
		}
		return err
	})
	return chunk, err
}

func (r wasmNumericJSON) file() (wasmNumericFile, error) {
	var file wasmNumericFile
	err := r.object([]string{"index", "chunks"}, func(key string) (err error) {
		switch key {
		case "index":
			file.index, err = r.natural(4)
		case "chunks":
			err = r.array(wasmNumericMaxChunks, func() error {
				chunk, err := r.chunk()
				if err == nil {
					file.chunks = append(file.chunks, chunk)
				}
				return err
			})
		}
		return err
	})
	return file, err
}

func parseWasmNumericCertificate(data string, sources []wasmNumericSource) ([]wasmNumericFile, error) {
	if len(data) == 0 || len(data) > wasmNumericMaxOutput {
		return nil, fmt.Errorf("numeric certificate output size outside 1..%d", wasmNumericMaxOutput)
	}
	decoder := json.NewDecoder(strings.NewReader(data))
	decoder.UseNumber()
	r := wasmNumericJSON{decoder: decoder}
	var files []wasmNumericFile
	err := r.object([]string{"version", "files"}, func(key string) error {
		if key == "version" {
			version, err := r.natural(1)
			if err != nil || version != 1 {
				return fmt.Errorf("unsupported numeric certificate version")
			}
			return nil
		}
		return r.array(5, func() error {
			file, err := r.file()
			if err == nil {
				files = append(files, file)
			}
			return err
		})
	})
	if err != nil {
		return nil, err
	}
	if _, err := decoder.Token(); err != io.EOF {
		return nil, fmt.Errorf("trailing numeric certificate data")
	}
	inventory := wasmNumericInventory()
	if len(files) != len(inventory) || len(sources) != len(inventory) {
		return nil, fmt.Errorf("certificate must cover exactly five original source files")
	}
	for i, file := range files {
		source := sources[i]
		if file.index != i || source.field != inventory[i].field || source.file != inventory[i].file {
			return nil, fmt.Errorf("duplicate, reordered, or unknown numeric source record %d", i)
		}
		if len(source.bytes) == 0 || len(source.bytes) > wasmNumericMaxSource || len(file.chunks) == 0 {
			return nil, fmt.Errorf("source or checkpoint count out of bounds for file %d", i)
		}
		offset, line, fuel := 0, 0, len(source.bytes)+1
		for j, chunk := range file.chunks {
			end := offset + len(chunk.bytes)
			if chunk.index != j || len(chunk.bytes) == 0 || chunk.bytes[len(chunk.bytes)-1] != 10 ||
				end > len(source.bytes) || !bytes.Equal(chunk.bytes, source.bytes[offset:end]) {
				return nil, fmt.Errorf("invalid or duplicate checkpoint bytes/index for file %d chunk %d", i, j)
			}
			if chunk.fuelUsed == 0 || chunk.fuelUsed > len(chunk.bytes) || chunk.fuelUsed > fuel {
				return nil, fmt.Errorf("invalid checkpoint fuel for file %d chunk %d", i, j)
			}
			previousStart := end
			for _, token := range chunk.tokens {
				if token.start < offset || token.stop <= token.start || token.stop > previousStart ||
					token.stop-token.start != len(token.spelling) || !bytes.Equal(token.spelling, source.bytes[token.start:token.stop]) ||
					token.line != line+bytes.Count(source.bytes[offset:token.start], []byte{10}) {
					return nil, fmt.Errorf("invalid, duplicate, or unordered token in file %d chunk %d", i, j)
				}
				previousStart = token.start
			}
			offset, line, fuel = end, line+bytes.Count(chunk.bytes, []byte{10}), fuel-chunk.fuelUsed
		}
		if offset != len(source.bytes) {
			return nil, fmt.Errorf("checkpoints omit original bytes in file %d", i)
		}
	}
	return files, nil
}

// This is the sole checkpoint-to-Lean boundary. All names and proof statements
// are fixed here; untrusted values reach only decimal natural/byte literals.
func writeWasmNumericCertificate(proof *strings.Builder, files []wasmNumericFile, sources []wasmNumericSource) {
	for i := range wasmNumericInventory() {
		writeWasmNumericFileCertificate(proof, i, files[i], sources[i])
	}
	writeWasmNumericAcceptance(proof)
}

func writeWasmNumericFileCertificate(proof *strings.Builder, index int, file wasmNumericFile, source wasmNumericSource) {
	const numeric = "_root_.Oak.WasmNumericSource."
	entry := wasmNumericInventory()[index]
	ns := "Numeric_" + entry.field
	name := "_root_." + ns + "."
	original := "_root_.actualOfficial_" + entry.field
	fmt.Fprintf(proof, "namespace %s\n", ns)
	fuel, offset, line := len(source.bytes)+1, 0, 0
	states := [][3]int{{fuel, offset, line}}
	for j, chunk := range file.chunks {
		fmt.Fprintf(proof, "noncomputable def bytes%d : %sBytes := %s\nnoncomputable def tokens%d : _root_.List %sToken := [", j, numeric, wasmCoreLeanList(chunk.bytes), j, numeric)
		for k, token := range chunk.tokens {
			if k > 0 {
				proof.WriteByte(',')
			}
			fmt.Fprintf(proof, "%sToken.mk %s %d %d %d", numeric, wasmCoreLeanList(token.spelling), token.start, token.stop, token.line)
		}
		proof.WriteString("]\n")
		nextFuel, nextOffset, nextLine := fuel-chunk.fuelUsed, offset+len(chunk.bytes), line+bytes.Count(chunk.bytes, []byte{10})
		fmt.Fprintf(proof, "theorem step%d (rest : %sBytes) (acc : _root_.List %sToken) :\n  %slexAux %d %d %d acc (_root_.List.append %sbytes%d rest) =\n  %slexAux %d %d %d (_root_.List.append %stokens%d acc) rest := by cbv\n", j, numeric, numeric, numeric, fuel, offset, line, name, j, numeric, nextFuel, nextOffset, nextLine, name, j)
		fuel, offset, line = nextFuel, nextOffset, nextLine
		states = append(states, [3]int{fuel, offset, line})
	}
	count := len(file.chunks)
	fmt.Fprintf(proof, "noncomputable def suffix%d : %sBytes := []\n", count, numeric)
	for j := count - 1; j >= 0; j-- {
		fmt.Fprintf(proof, "noncomputable def suffix%d : %sBytes := _root_.List.append %sbytes%d %ssuffix%d\n", j, numeric, name, j, name, j+1)
	}
	fmt.Fprintf(proof, "noncomputable def acc0 : _root_.List %sToken := []\n", numeric)
	for j := 0; j < count; j++ {
		fmt.Fprintf(proof, "noncomputable def acc%d : _root_.List %sToken := _root_.List.append %stokens%d %sacc%d\n", j+1, numeric, name, j, name, j)
	}
	fmt.Fprintf(proof, "attribute [local irreducible] %slexAux\n", numeric)
	fmt.Fprintf(proof, "theorem full_bytes : %s = %ssuffix0 := by rfl\n", original, name)
	fmt.Fprintf(proof, "theorem lexed : %slex %s = _root_.Option.some (_root_.List.reverse %sacc%d) := by\n  change %slexAux %d 0 0 [] %s = _\n  rw [%sfull_bytes]\n  calc\n", numeric, original, name, count, numeric, len(source.bytes)+1, original, name)
	for j := 0; j < count; j++ {
		lhs := "_"
		if j == 0 {
			lhs = fmt.Sprintf("%slexAux %d %d %d %sacc0 %ssuffix0", numeric, states[j][0], states[j][1], states[j][2], name, name)
		}
		s := states[j+1]
		fmt.Fprintf(proof, "    %s = %slexAux %d %d %d %sacc%d %ssuffix%d := %sstep%d %ssuffix%d %sacc%d\n", lhs, numeric, s[0], s[1], s[2], name, j+1, name, j+1, name, j, name, j+1, name, j)
	}
	proof.WriteString("    _ = _ := by unfold _root_.Oak.WasmNumericSource.lexAux; rfl\n")
	fmt.Fprintf(proof, "theorem parsed : %sparseFile %sFile.%s %s =\n  _root_.Option.some (_root_.List.filter (fun d => _root_.BEq.beq (%sOwned.file d) %sFile.%s) %sexpected) := by\n  unfold %sparseFile %sreadBlocks\n  rw [%slexed]\n  decide +kernel\nend %s\n", numeric, numeric, entry.field, original, numeric, numeric, entry.field, numeric, numeric, numeric, name, ns)
}

func writeWasmNumericAcceptance(proof *strings.Builder) {
	proof.WriteString(`theorem actualOfficialChecked : _root_.Oak.WasmNumericSource.accepts _root_.actualOfficial = _root_.Bool.true := by
  unfold _root_.Oak.WasmNumericSource.accepts _root_.Oak.WasmNumericSource.parse _root_.actualOfficial
  rw [_root_.Numeric_variables.parsed, _root_.Numeric_values.parsed, _root_.Numeric_types.parsed, _root_.Numeric_instructions.parsed, _root_.Numeric_numerics.parsed]
  decide +kernel
#print axioms _root_.actualOfficialChecked
`)
}

// Lake can prepend package build directories ahead of LEAN_PATH. Existence of
// our fresh objects alone is insufficient: audit Lean's actual import resolver
// immediately before final composition, rejecting every stale/foreign match.
func auditWasmNumericDependencies(out, evidenceDirectory string) error {
	if !filepath.IsAbs(evidenceDirectory) {
		return fmt.Errorf("fresh evidence directory must be absolute")
	}
	expected := make(map[string]string, 5)
	for _, entry := range wasmNumericInventory() {
		module := "NumericEvidence_" + entry.field + ".olean"
		expected[module] = filepath.Join(evidenceDirectory, module)
	}
	seen := make(map[string]bool, 5)
	for _, line := range strings.Split(out, "\n") {
		path := strings.TrimSpace(line)
		if path == "" {
			continue
		}
		module := filepath.Base(path)
		if !strings.HasPrefix(module, "NumericEvidence_") {
			continue
		}
		want, ok := expected[module]
		if !ok {
			return fmt.Errorf("unexpected numeric evidence dependency %q", path)
		}
		if seen[module] {
			return fmt.Errorf("duplicate numeric evidence dependency %q", module)
		}
		if !filepath.IsAbs(path) || filepath.Clean(path) != want {
			return fmt.Errorf("foreign numeric evidence dependency %q; want %q", path, want)
		}
		seen[module] = true
	}
	for _, entry := range wasmNumericInventory() {
		module := "NumericEvidence_" + entry.field + ".olean"
		if !seen[module] {
			return fmt.Errorf("missing fresh numeric evidence dependency %q", module)
		}
	}
	return nil
}

func auditWasmCoreAxioms(out string, names []string) error {
	if len(names) == 0 {
		return fmt.Errorf("empty expected axiom report list")
	}
	rows := regexp.MustCompile(`(?s)'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)`).FindAllStringSubmatch(out, -1)
	seen := map[string]bool{}
	wanted := map[string]bool{}
	for _, name := range names {
		if wanted[name] {
			return fmt.Errorf("duplicate expected axiom report: %s", name)
		}
		wanted[name] = true
	}
	allowed := map[string]bool{"propext": true, "Classical.choice": true, "Quot.sound": true}
	for _, row := range rows {
		if seen[row[1]] {
			return fmt.Errorf("duplicate axiom report: %s", row[1])
		}
		if !wanted[row[1]] {
			return fmt.Errorf("unexpected axiom report: %s", row[1])
		}
		seen[row[1]] = true
		for _, a := range strings.Split(row[2], ",") {
			a = strings.TrimSpace(a)
			if a != "" && !allowed[a] {
				return fmt.Errorf("unexpected axiom in %s: %s", row[1], a)
			}
		}
	}
	for _, name := range names {
		if !seen[name] {
			return fmt.Errorf("missing axiom report for %s", name)
		}
	}
	return nil
}

func TestWasmCoreAxiomAudit(t *testing.T) {
	const clean = "'official' does not depend on any axioms\n'core' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
	for _, tc := range []struct {
		name    string
		out     string
		names   []string
		wantErr bool
	}{
		{"kernel and standard logical axioms", clean, []string{"official", "core"}, false},
		{"explicit empty axioms", "'official' depends on axioms: []\n", []string{"official"}, false},
		{"missing report", clean, []string{"official", "core", "missing"}, true},
		{"extra report", clean, []string{"official"}, true},
		{"duplicate report", clean + clean, []string{"official", "core"}, true},
		{"duplicate query", clean, []string{"official", "core", "core"}, true},
		{"empty query", "", nil, true},
		{"sorry", strings.Replace(clean, "propext", "sorryAx", 1), []string{"official", "core"}, true},
		{"native decision", strings.Replace(clean, "propext", "Lean.ofReduceBool", 1), []string{"official", "core"}, true},
		{"custom axiom", strings.Replace(clean, "propext", "assumedNumericSemantics", 1), []string{"official", "core"}, true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			err := auditWasmCoreAxioms(tc.out, tc.names)
			if (err != nil) != tc.wantErr {
				t.Fatalf("audit error = %v, want error %v", err, tc.wantErr)
			}
		})
	}
}

func TestWasmCoreSourceBundleRendering(t *testing.T) {
	sources := []wasmNumericSource{
		{field: "variables", bytes: []byte{0, 10, 13, 34, 92, 127, 128, 255}},
		{field: "values", bytes: []byte{}},
		{field: "types", bytes: []byte{65}},
		{field: "instructions", bytes: []byte{66}},
		{field: "numerics", bytes: []byte{67, 10}},
	}
	var proof strings.Builder
	writeWasmNumericSourceBundle(&proof, sources)
	want := `noncomputable def actualOfficial_variables : _root_.Oak.WasmNumericSource.Bytes := [0,10,13,34,92,127,128,255]
noncomputable def actualOfficial_values : _root_.Oak.WasmNumericSource.Bytes := []
noncomputable def actualOfficial_types : _root_.Oak.WasmNumericSource.Bytes := [65]
noncomputable def actualOfficial_instructions : _root_.Oak.WasmNumericSource.Bytes := [66]
noncomputable def actualOfficial_numerics : _root_.Oak.WasmNumericSource.Bytes := [67,10]
noncomputable def actualOfficial : _root_.Oak.WasmNumericSource.Bundle := {
  variables := _root_.actualOfficial_variables
  values := _root_.actualOfficial_values
  types := _root_.actualOfficial_types
  instructions := _root_.actualOfficial_instructions
  numerics := _root_.actualOfficial_numerics
}
`
	if proof.String() != want {
		t.Fatalf("source bytes were not emitted directly and completely:\n%s", proof.String())
	}
}

func TestWasmCoreNumericCertificateInput(t *testing.T) {
	sources, certificate := wasmNumericCertificateFixture()
	calls := 0
	parsed := loadWasmNumericCheckpoints(t, sources, func(args ...string) string {
		calls++
		if len(args) != 6 || strings.Join(args[:5], " ") != "env lean -j1 --run "+filepath.Join("..", "wasm-core", "NumericCertificate.lean") {
			t.Fatalf("unexpected certificate command: %q", args)
		}
		if !filepath.IsAbs(args[5]) {
			t.Fatalf("certificate input directory is not absolute: %q", args[5])
		}
		entries, err := os.ReadDir(args[5])
		if err != nil {
			t.Fatal(err)
		}
		if len(entries) != len(sources) {
			t.Fatalf("snapshot contains %d files, want %d", len(entries), len(sources))
		}
		for _, source := range sources {
			data, err := os.ReadFile(filepath.Join(args[5], source.file))
			if err != nil {
				t.Fatal(err)
			}
			if string(data) != string(source.bytes) {
				t.Fatalf("certificate input differs from loaded original: %s", source.file)
			}
		}
		return certificate
	})
	if calls != 1 || len(parsed) != 5 {
		t.Fatalf("certificate was not parsed once from the independent snapshot: calls=%d files=%d", calls, len(parsed))
	}
}

func wasmNumericCertificateFixture() ([]wasmNumericSource, string) {
	sources := wasmNumericInventory()
	var files []string
	for i := range sources {
		sources[i].bytes = []byte{120, 10}
		files = append(files, fmt.Sprintf(`{"index":%d,"chunks":[{"index":0,"bytes":[120,10],"tokens":[{"spelling":[120],"start":0,"stop":1,"line":0}],"fuel_used":2}]}`, i))
	}
	return sources, `{"version":1,"files":[` + strings.Join(files, ",") + `]}`
}

func TestWasmCoreNumericCertificateSchema(t *testing.T) {
	sources, valid := wasmNumericCertificateFixture()
	change := func(old, new string) string { return strings.Replace(valid, old, new, 1) }
	const token = `{"spelling":[120],"start":0,"stop":1,"line":0}`
	const chunk = `{"index":0,"bytes":[120,10],"tokens":[` + token + `],"fuel_used":2}`
	const file = `{"index":0,"chunks":[` + chunk + `]}`
	for _, tc := range []struct {
		name string
		data string
	}{
		{"empty", ""},
		{"invalid JSON", valid[:len(valid)-1]},
		{"trailing data", valid + "{}"},
		{"trailing malformed data", valid + "!"},
		{"Lean injection", "import Evil\n" + valid},
		{"extra root key", change(`"version":1`, `"version":1,"command":0`)},
		{"extra file key", change(`"chunks":`, `"name":0,"chunks":`)},
		{"extra chunk key", change(`"bytes":`, `"statement":0,"bytes":`)},
		{"extra token key", change(`"spelling":`, `"trusted":0,"spelling":`)},
		{"missing root key", change(`"version":1,`, "")},
		{"missing chunk key", change(`,"fuel_used":2`, "")},
		{"missing token key", change(`,"line":0`, "")},
		{"duplicate root key", change(`"version":1`, `"version":1,"version":1`)},
		{"duplicate file key", change(`"index":0,"chunks"`, `"index":0,"index":0,"chunks"`)},
		{"duplicate token key", change(`"start":0`, `"start":0,"start":0`)},
		{"escaped duplicate key", change(`"version":1`, `"version":1,"\u0076ersion":1`)},
		{"negative byte", change(`[120,10]`, `[-1,10]`)},
		{"negative zero", change(`[120,10]`, `[-0,10]`)},
		{"out of range byte", change(`[120,10]`, `[256,10]`)},
		{"out of range token byte", change(`[120]`, `[256]`)},
		{"negative offset", change(`"start":0`, `"start":-1`)},
		{"oversized offset", change(`"stop":1`, `"stop":65537`)},
		{"oversized number", change(`"stop":1`, `"stop":18446744073709551616`)},
		{"fraction", change(`"fuel_used":2`, `"fuel_used":2.0`)},
		{"exponent", change(`"fuel_used":2`, `"fuel_used":2e0`)},
		{"string number", change(`"fuel_used":2`, `"fuel_used":"2"`)},
		{"null array", change(`[120,10]`, `null`)},
		{"string bytes", change(`[120,10]`, `"eAo="`)},
		{"wrong version", change(`"version":1`, `"version":0`)},
		{"missing file", change(file+",", "")},
		{"oversized file array", change(file, file+","+file)},
		{"duplicate file", change(`{"index":1,`, `{"index":0,`)},
		{"out of range file", change(`{"index":4,`, `{"index":5,`)},
		{"wrong chunk index", change(`"chunks":[{"index":0`, `"chunks":[{"index":1`)},
		{"duplicate chunk", change(chunk, chunk+","+chunk)},
		{"oversized chunk array", change(chunk, strings.Repeat(chunk+",", wasmNumericMaxChunks)+chunk)},
		{"duplicate token", change(token, token+","+token)},
		{"oversized token array", change(token, strings.Repeat(token+",", wasmNumericMaxChunk)+token)},
		{"bad source byte", change(`[120,10]`, `[121,10]`)},
		{"missing source bytes", change(`[120,10]`, `[10]`)},
		{"not complete line", change(`[120,10]`, `[120]`)},
		{"zero fuel", change(`"fuel_used":2`, `"fuel_used":0`)},
		{"too much fuel", change(`"fuel_used":2`, `"fuel_used":3`)},
		{"bad token spelling", change(`[120]`, `[121]`)},
		{"bad token span", change(`"stop":1`, `"stop":2`)},
		{"bad token line", change(`"line":0`, `"line":1`)},
		{"oversized byte array", change(`[120,10]`, `[`+strings.Repeat("120,", wasmNumericMaxChunk)+`10]`)},
		{"oversized output", strings.Repeat(" ", wasmNumericMaxOutput+1)},
	} {
		t.Run(tc.name, func(t *testing.T) {
			if _, err := parseWasmNumericCertificate(tc.data, sources); err == nil {
				t.Fatal("malformed or out-of-scope checkpoint data accepted")
			}
		})
	}
	if _, err := parseWasmNumericCertificate(" \n"+valid+" \n", sources); err != nil {
		t.Fatalf("valid checkpoint data rejected: %v", err)
	}
}

func TestWasmCoreNumericCertificateRendering(t *testing.T) {
	sources, data := wasmNumericCertificateFixture()
	files, err := parseWasmNumericCertificate(data, sources)
	if err != nil {
		t.Fatal(err)
	}
	var proof strings.Builder
	writeWasmNumericCertificate(&proof, files, sources)
	out := proof.String()
	for _, want := range []string{
		"theorem step0 (rest : _root_.Oak.WasmNumericSource.Bytes) (acc : _root_.List _root_.Oak.WasmNumericSource.Token)",
		"_root_.Oak.WasmNumericSource.lexAux 3 0 0 acc (_root_.List.append _root_.Numeric_variables.bytes0 rest)",
		"_root_.Oak.WasmNumericSource.lexAux 1 2 1 (_root_.List.append _root_.Numeric_variables.tokens0 acc) rest := by cbv",
		"attribute [local irreducible] _root_.Oak.WasmNumericSource.lexAux\ntheorem full_bytes",
		"_ = _ := by unfold _root_.Oak.WasmNumericSource.lexAux; rfl",
		"theorem full_bytes : _root_.actualOfficial_variables = _root_.Numeric_variables.suffix0 := by rfl",
		"theorem lexed : _root_.Oak.WasmNumericSource.lex _root_.actualOfficial_variables",
		"theorem parsed : _root_.Oak.WasmNumericSource.parseFile _root_.Oak.WasmNumericSource.File.variables _root_.actualOfficial_variables",
		"theorem actualOfficialChecked : _root_.Oak.WasmNumericSource.accepts _root_.actualOfficial = _root_.Bool.true",
		"#print axioms _root_.actualOfficialChecked",
	} {
		if !strings.Contains(out, want) {
			t.Errorf("fixed proof template is missing %q", want)
		}
	}
	for _, forbidden := range []string{"native_decide", "axiom ", "sorry", "import ", "open ", "set_option", "namespace x"} {
		if strings.Contains(out, forbidden) {
			t.Errorf("unexpected syntax in numeric certificate template: %q", forbidden)
		}
	}
	if strings.Count(out, "attribute [local irreducible] _root_.Oak.WasmNumericSource.lexAux") != 5 {
		t.Error("each fixed file namespace must locally freeze lexer reduction after its checkpoints")
	}
}

func TestWasmCoreNumericEvidenceRendering(t *testing.T) {
	sources, data := wasmNumericCertificateFixture()
	files, err := parseWasmNumericCertificate(data, sources)
	if err != nil {
		t.Fatal(err)
	}
	for i, entry := range wasmNumericInventory() {
		t.Run(entry.field, func(t *testing.T) {
			var proof strings.Builder
			writeWasmNumericEvidenceModule(&proof, i, files[i], sources[i])
			out := proof.String()
			if !strings.HasPrefix(out, "import Oak.WasmNumericSource\n"+wasmNumericProofOptions) ||
				strings.Count(out, "noncomputable def actualOfficial_") != 1 ||
				!strings.Contains(out, "noncomputable def actualOfficial_"+entry.field+" :") ||
				!strings.HasSuffix(out, "#print axioms _root_.Numeric_"+entry.field+".parsed\n") {
				t.Fatal("evidence module must contain exactly its independent original, fixed proof, and parsed theorem audit")
			}
			if strings.Contains(out, "def actualOfficial :") || strings.Contains(out, "actualOfficialChecked") ||
				regexp.MustCompile(`(?m)^def `).MatchString(out) {
				t.Fatal("evidence module must omit whole-bundle composition and explicitly mark every data definition noncomputable")
			}
			for j, other := range wasmNumericInventory() {
				if i != j && (strings.Contains(out, "actualOfficial_"+other.field) || strings.Contains(out, "Numeric_"+other.field)) {
					t.Fatalf("evidence module unexpectedly contains another file's data or proof: %s", other.field)
				}
			}
		})
	}
	var proof strings.Builder
	writeWasmNumericCompositionHeader(&proof)
	writeWasmNumericBundle(&proof)
	writeWasmNumericAcceptance(&proof)
	out := proof.String()
	if strings.Count(out, "import NumericEvidence_") != 5 ||
		strings.Count(out, "noncomputable def actualOfficial :") != 1 ||
		strings.Contains(out, "def actualOfficial_") || strings.Contains(out, "namespace Numeric_") {
		t.Fatal("final composition must import five fresh modules, define only their bundle, and reuse checked facts")
	}
	for _, entry := range wasmNumericInventory() {
		if !strings.Contains(out, "import NumericEvidence_"+entry.field+"\n") ||
			!strings.Contains(out, entry.field+" := _root_.actualOfficial_"+entry.field+"\n") ||
			!strings.Contains(out, "_root_.Numeric_"+entry.field+".parsed") {
			t.Fatalf("final composition omitted fixed evidence for %s", entry.field)
		}
	}
}

func TestWasmCoreNumericOutputBound(t *testing.T) {
	canceled := false
	out := wasmNumericBoundedOutput{limit: 4, cancel: func() { canceled = true }}
	if _, err := io.Copy(&out, strings.NewReader("1234")); err != nil {
		t.Fatal(err)
	}
	if _, err := io.Copy(&out, strings.NewReader("5")); err == nil || !canceled || !out.exceeded || out.String() != "1234" {
		t.Fatalf("output bound did not cancel without growth: canceled=%v exceeded=%v data=%q err=%v", canceled, out.exceeded, out.String(), err)
	}
}

func TestWasmCoreNumericDependencyResolution(t *testing.T) {
	directory := t.TempDir()
	var paths []string
	for _, entry := range wasmNumericInventory() {
		paths = append(paths, filepath.Join(directory, "NumericEvidence_"+entry.field+".olean"))
	}
	valid := strings.Join(paths, "\n") + "\n"
	for _, tc := range []struct {
		name    string
		out     string
		wantErr bool
	}{
		{"exact fresh modules", valid, false},
		{"additional library imports", filepath.Join(directory, "Oak", "WasmCoreSource.olean") + "\n" + valid, false},
		{"arbitrary dependency order", strings.Join([]string{paths[4], paths[2], paths[0], paths[3], paths[1]}, "\n"), false},
		{"missing all", "", true},
		{"missing one", strings.Join(paths[:4], "\n"), true},
		{"duplicate fresh module", valid + paths[0] + "\n", true},
		{"foreign package cache", strings.Replace(valid, paths[0], filepath.Join(directory, "stale", filepath.Base(paths[0])), 1), true},
		{"foreign and fresh duplicate", filepath.Join(directory, "stale", filepath.Base(paths[0])) + "\n" + valid, true},
		{"relative path", strings.Replace(valid, paths[0], filepath.Base(paths[0]), 1), true},
		{"unknown evidence module", valid + filepath.Join(directory, "NumericEvidence_unchecked.olean") + "\n", true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			err := auditWasmNumericDependencies(tc.out, directory)
			if (err != nil) != tc.wantErr {
				t.Fatalf("dependency audit error = %v, want error %v", err, tc.wantErr)
			}
		})
	}
	if err := auditWasmNumericDependencies(valid, "relative"); err == nil {
		t.Fatal("relative expected directory must be rejected")
	}
}
