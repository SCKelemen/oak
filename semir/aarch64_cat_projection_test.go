package semir

import (
	"bytes"
	"crypto/sha256"
	"errors"
	"fmt"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"testing"
	"unicode"
)

const (
	catLispMaxBytes = 8 << 20
	catLispMaxDepth = 256
	catLispMaxNodes = 250_000
)

var errCATLispTooLarge = errors.New("CAT parser output exceeds the configured limit")

// These hashes cover the normalized AST emitted by Herdtools7's own
// cat2lisp parser at the revision in spec/litmus/aarch64/HERDTOOLS7_COMMIT.
// They intentionally certify only the relation definitions used by Oak's
// restricted projection, not the complete semantics of the Arm CAT model.
var pinnedAArch64ProjectionHashes = map[string]string{
	"dmb.full":      "7f0e43f97632346b01cfb634eb6d58a9ceb4a51dabf60aa378f2a0b72ea76555",
	"bob":           "425be3474246aec01d5c37892e91a55d8d7b9ed18926e8591d87b365bb4bc3c6",
	"lob":           "ee18823f317c169ed24fb10a8f74cf64a74cc424c9c63c27cb2366378381a5d2",
	"local-hw-reqs": "f06d99cb47fa5b0c7d38139a5df0f26e6951925b29c9b79534aba9a98effd8d0",
	"hw-reqs":       "5de8d9ab52b47cbfd5541a6c3913ac466b7fb084a8fe65ccc4253fa10848ce97",
	"Exp-obs":       "52c8a651e8479a19c224dfe10577b96a3483e4775546d717e548543875252419",
	"obs":           "547031d91767ede427f6f42ba64fdd6dd6800d2cbb4e9eff5f072ff41371199d",
	"ob":            "60f3e529e30a548fa078a31c7feb2dc1d378b6283123ee3921434938413b5936",
}

var pinnedAArch64BobArmHashes = []string{
	"5139573a29ccf13fd38db712c7055764fc4701fe7aa9fac6ae23c6ea94c96dbe",
	"51f25b7f9f6a6abbe79fb1d24df6d6fc5449f0c99d60101a0b56a76f46cce625",
	"58ba1d284d6da0510ee087f3685bccaa88476a313e82cdf676b0b3e2b904401a",
	"c58e94dbab846a1996d298889dc3bb92a70fd002af324356c82fa4bfbc1883e7",
}

const pinnedAArch64ExternalIrreflexiveHash = "0d3935d123120064a5f8c4cb229df1eb5e8df41fe0bd0adb56d62d27a7c4a6cf"

type catLispNode struct {
	atom   string
	quoted bool
	list   []*catLispNode
}

func (n *catLispNode) isList() bool { return n != nil && n.list != nil }

func (n *catLispNode) canonical() string {
	if !n.isList() {
		if n.quoted {
			return strconv.Quote(n.atom)
		}
		return n.atom
	}
	var result strings.Builder
	result.WriteByte('(')
	for index, child := range n.list {
		if index != 0 {
			result.WriteByte(' ')
		}
		result.WriteString(child.canonical())
	}
	result.WriteByte(')')
	return result.String()
}

func (n *catLispNode) clone() *catLispNode {
	if n == nil {
		return nil
	}
	copyNode := &catLispNode{atom: n.atom, quoted: n.quoted}
	if n.isList() {
		copyNode.list = make([]*catLispNode, len(n.list))
		for index, child := range n.list {
			copyNode.list[index] = child.clone()
		}
	}
	return copyNode
}

type catLispParser struct {
	input []byte
	pos   int
	nodes int
}

func parseCATLisp(input []byte) (*catLispNode, error) {
	if len(input) > catLispMaxBytes {
		return nil, errCATLispTooLarge
	}
	parser := catLispParser{input: input}
	parser.skipSpace()
	if parser.pos == len(parser.input) {
		return nil, errors.New("empty CAT parser output")
	}
	root, err := parser.parseNode(0)
	if err != nil {
		return nil, err
	}
	parser.skipSpace()
	if parser.pos != len(parser.input) {
		return nil, fmt.Errorf("trailing CAT parser output at byte %d", parser.pos)
	}
	if !root.isList() {
		return nil, errors.New("CAT parser output root is not a list")
	}
	return root, nil
}

func (p *catLispParser) parseNode(depth int) (*catLispNode, error) {
	if depth > catLispMaxDepth {
		return nil, fmt.Errorf("CAT parser output exceeds depth %d", catLispMaxDepth)
	}
	if p.nodes >= catLispMaxNodes {
		return nil, fmt.Errorf("CAT parser output exceeds %d nodes", catLispMaxNodes)
	}
	p.nodes++
	if p.pos >= len(p.input) {
		return nil, errors.New("unexpected end of CAT parser output")
	}
	switch p.input[p.pos] {
	case '(':
		p.pos++
		node := &catLispNode{list: []*catLispNode{}}
		for {
			p.skipSpace()
			if p.pos >= len(p.input) {
				return nil, errors.New("unterminated list in CAT parser output")
			}
			if p.input[p.pos] == ')' {
				p.pos++
				return node, nil
			}
			child, err := p.parseNode(depth + 1)
			if err != nil {
				return nil, err
			}
			node.list = append(node.list, child)
		}
	case ')':
		return nil, fmt.Errorf("unexpected ')' at byte %d", p.pos)
	case '"':
		start := p.pos
		p.pos++
		escaped := false
		for p.pos < len(p.input) {
			current := p.input[p.pos]
			p.pos++
			if escaped {
				escaped = false
				continue
			}
			if current == '\\' {
				escaped = true
				continue
			}
			if current == '"' {
				decoded, err := strconv.Unquote(string(p.input[start:p.pos]))
				if err != nil {
					return nil, fmt.Errorf("decode CAT parser string at byte %d: %w", start, err)
				}
				return &catLispNode{atom: decoded, quoted: true}, nil
			}
		}
		return nil, fmt.Errorf("unterminated string at byte %d", start)
	default:
		start := p.pos
		for p.pos < len(p.input) {
			current := p.input[p.pos]
			if current == '(' || current == ')' || unicode.IsSpace(rune(current)) {
				break
			}
			p.pos++
		}
		if start == p.pos {
			return nil, fmt.Errorf("invalid CAT parser token at byte %d", start)
		}
		return &catLispNode{atom: string(p.input[start:p.pos])}, nil
	}
}

func (p *catLispParser) skipSpace() {
	for p.pos < len(p.input) && unicode.IsSpace(rune(p.input[p.pos])) {
		p.pos++
	}
}

type cappedCATBuffer struct {
	bytes.Buffer
	limit int
}

func (b *cappedCATBuffer) Write(data []byte) (int, error) {
	if len(data) > b.limit-b.Len() {
		return 0, errCATLispTooLarge
	}
	return b.Buffer.Write(data)
}

func parsePinnedAArch64CAT(cat2lisp, model, libdir string) (*catLispNode, error) {
	stdout := cappedCATBuffer{limit: catLispMaxBytes}
	stderr := cappedCATBuffer{limit: 1 << 20}
	command := exec.Command(cat2lisp, "-set-libdir", libdir, model)
	command.Stdout = &stdout
	command.Stderr = &stderr
	if err := command.Run(); err != nil {
		return nil, fmt.Errorf("cat2lisp failed: %w\n%s", err, stderr.String())
	}
	return parseCATLisp(stdout.Bytes())
}

type pinnedCATBlob struct {
	mode string
	oid  string
}

func pinnedCATBlobIDs(checkout, revision string) (map[string]pinnedCATBlob, error) {
	command := exec.Command("git", "-C", checkout, "ls-tree", "-r", revision, "--", "herd/libdir")
	output, err := command.Output()
	if err != nil {
		return nil, fmt.Errorf("list pinned CAT blobs: %w", err)
	}
	result := make(map[string]pinnedCATBlob)
	for lineNumber, line := range strings.Split(strings.TrimSpace(string(output)), "\n") {
		if line == "" {
			continue
		}
		fields := strings.Fields(line)
		if len(fields) != 4 || fields[1] != "blob" {
			return nil, fmt.Errorf("parse ls-tree line %d: %q", lineNumber+1, line)
		}
		path := fields[3]
		if !strings.HasPrefix(path, "herd/libdir/") || !strings.HasSuffix(path, ".cat") {
			continue
		}
		result[path] = pinnedCATBlob{mode: fields[0], oid: fields[2]}
	}
	if len(result) == 0 {
		return nil, errors.New("pinned revision contains no herd/libdir CAT files")
	}
	return result, nil
}

func readCATWorktreeBytes(path, mode string) ([]byte, error) {
	if mode == "120000" {
		target, err := os.Readlink(path)
		if err != nil {
			return nil, err
		}
		return []byte(target), nil
	}
	return os.ReadFile(path)
}

func verifyPinnedCATSourceBytes(checkout, revision string) error {
	expected, err := pinnedCATBlobIDs(checkout, revision)
	if err != nil {
		return err
	}
	for path, want := range expected {
		absolute := filepath.Join(checkout, filepath.FromSlash(path))
		actual, err := readCATWorktreeBytes(absolute, want.mode)
		if err != nil {
			return fmt.Errorf("read pinned CAT source %s: %w", path, err)
		}
		command := exec.Command("git", "-C", checkout, "cat-file", "blob", want.oid)
		pinned, err := command.Output()
		if err != nil {
			return fmt.Errorf("read pinned CAT blob %s for %s: %w", want.oid, path, err)
		}
		if !bytes.Equal(actual, pinned) {
			return fmt.Errorf("CAT source %s does not byte-match pinned blob %s", path, want.oid)
		}
	}
	libdir := filepath.Join(checkout, "herd", "libdir")
	return filepath.WalkDir(libdir, func(path string, entry fs.DirEntry, walkErr error) error {
		if walkErr != nil {
			return walkErr
		}
		if entry.IsDir() || !strings.HasSuffix(entry.Name(), ".cat") {
			return nil
		}
		relative, err := filepath.Rel(checkout, path)
		if err != nil {
			return err
		}
		relative = filepath.ToSlash(relative)
		if _, ok := expected[relative]; !ok {
			return fmt.Errorf("untracked CAT source can affect include resolution: %s", relative)
		}
		return nil
	})
}

func firstAtom(node *catLispNode) string {
	if node == nil || !node.isList() || len(node.list) == 0 || node.list[0].isList() {
		return ""
	}
	return node.list[0].atom
}

func bindingFromNode(node *catLispNode) (string, *catLispNode, bool) {
	if node == nil || !node.isList() {
		return "", nil, false
	}
	var name string
	var expression *catLispNode
	for _, child := range node.list {
		if firstAtom(child) == "cat::pat" && len(child.list) == 3 &&
			child.list[1].atom == ":pvar" && child.list[2].quoted {
			name = child.list[2].atom
		}
		if firstAtom(child) == "cat::exp" && len(child.list) >= 2 {
			expression = &catLispNode{list: child.list[1:]}
		}
	}
	return name, expression, name != "" && expression != nil
}

func collectBindings(node *catLispNode, result map[string][]*catLispNode) {
	if name, expression, ok := bindingFromNode(node); ok {
		result[name] = append(result[name], expression)
	}
	if node != nil && node.isList() {
		for _, child := range node.list {
			collectBindings(child, result)
		}
	}
}

func uniqueCATDefinition(bindings map[string][]*catLispNode, name string) (*catLispNode, error) {
	definitions := bindings[name]
	if len(definitions) == 0 {
		return nil, fmt.Errorf("expanded CAT AST has no %q definition", name)
	}
	canonical := definitions[0].canonical()
	for _, definition := range definitions[1:] {
		if definition.canonical() != canonical {
			return nil, fmt.Errorf("expanded CAT AST has conflicting %q definitions", name)
		}
	}
	return definitions[len(definitions)-1], nil
}

func expressionHash(node *catLispNode) string {
	hash := sha256.Sum256([]byte(node.canonical()))
	return fmt.Sprintf("%x", hash[:])
}

func catVariable(node *catLispNode, name string) bool {
	return node != nil && node.isList() && len(node.list) == 3 &&
		node.list[0].atom == ":e_var" && node.list[1].atom == "nil" &&
		node.list[2].quoted && node.list[2].atom == name
}

func catOperator(node *catLispNode, operator string) ([]*catLispNode, bool) {
	if node == nil || !node.isList() || len(node.list) != 4 ||
		node.list[0].atom != ":e_op" || node.list[1].atom != "nil" ||
		node.list[2].atom != operator || !node.list[3].isList() {
		return nil, false
	}
	return node.list[3].list, true
}

func catUnaryOperator(node *catLispNode, operator string) (*catLispNode, bool) {
	if node == nil || !node.isList() || len(node.list) != 4 ||
		node.list[0].atom != ":e_op1" || node.list[1].atom != "nil" ||
		node.list[2].atom != operator {
		return nil, false
	}
	return node.list[3], true
}

func containsCATVariable(node *catLispNode, name string) bool {
	if catVariable(node, name) {
		return true
	}
	if node != nil && node.isList() {
		for index := 0; index+2 < len(node.list); index++ {
			if node.list[index].atom == ":e_var" && node.list[index+1].atom == "nil" &&
				node.list[index+2].quoted && node.list[index+2].atom == name {
				return true
			}
		}
		for _, child := range node.list {
			if containsCATVariable(child, name) {
				return true
			}
		}
	}
	return false
}

func containsCATAtom(node *catLispNode, atom string) bool {
	if node == nil {
		return false
	}
	if !node.isList() {
		return node.atom == atom
	}
	for _, child := range node.list {
		if containsCATAtom(child, atom) {
			return true
		}
	}
	return false
}

func directUnionContainsVariable(node *catLispNode, name string) bool {
	operands, ok := catOperator(node, ":union")
	if !ok {
		return false
	}
	for _, operand := range operands {
		if catVariable(operand, name) {
			return true
		}
	}
	return false
}

func containsIntersection(node *catLispNode, left, right string) bool {
	if operands, ok := catOperator(node, ":inter"); ok && len(operands) == 2 &&
		catVariable(operands[0], left) && catVariable(operands[1], right) {
		return true
	}
	if node != nil && node.isList() {
		for _, child := range node.list {
			if containsIntersection(child, left, right) {
				return true
			}
		}
	}
	return false
}

func containsSequence(node *catLispNode, predicate func([]*catLispNode) bool) bool {
	if operands, ok := catOperator(node, ":seq"); ok && predicate(operands) {
		return true
	}
	if node != nil && node.isList() {
		for _, child := range node.list {
			if containsSequence(child, predicate) {
				return true
			}
		}
	}
	return false
}

type aarch64CATProjection struct {
	definitions map[string]*catLispNode
	external    *catLispNode
}

func extractAArch64CATProjection(root *catLispNode) (*aarch64CATProjection, error) {
	bindings := make(map[string][]*catLispNode)
	collectBindings(root, bindings)
	projection := &aarch64CATProjection{definitions: make(map[string]*catLispNode)}
	for name := range pinnedAArch64ProjectionHashes {
		definition, err := uniqueCATDefinition(bindings, name)
		if err != nil {
			return nil, err
		}
		projection.definitions[name] = definition
	}
	for _, form := range root.list {
		if firstAtom(form) != ":i_test" || !containsCATAtom(form, "external") {
			continue
		}
		if projection.external != nil {
			return nil, errors.New("expanded CAT AST has duplicate external tests")
		}
		projection.external = form
	}
	if projection.external == nil {
		return nil, errors.New("expanded CAT AST has no external test")
	}
	return projection, nil
}

func verifyAArch64ProjectionStructure(projection *aarch64CATProjection) error {
	definition := projection.definitions
	if !directUnionContainsVariable(definition["dmb.full"], "DMB.ISH") {
		return errors.New("dmb.full does not directly contain DMB.ISH")
	}
	bobArms, ok := catOperator(definition["bob"], ":union")
	if !ok {
		return errors.New("bob is not a union")
	}
	var fullDMB, beforeRelease, afterAcquire, releaseAcquire bool
	for _, arm := range bobArms {
		has := func(name string) bool { return containsCATVariable(arm, name) }
		switch {
		case has("dmb.full") && has("po") && has("Exp") && has("M") && !has("DC.CVAU"):
			fullDMB = true
		case has("L") && has("A") && has("po") && !has("Q") && !has("amo"):
			releaseAcquire = true
		case has("A") && has("Q") && has("po") && !has("L"):
			afterAcquire = true
		case has("L") && has("po") && !has("A") && !has("Q"):
			beforeRelease = true
		}
	}
	if !fullDMB || !beforeRelease || !afterAcquire || !releaseAcquire {
		return fmt.Errorf("bob scalar arms: full-dmb=%t before-release=%t after-acquire=%t release-acquire=%t",
			fullDMB, beforeRelease, afterAcquire, releaseAcquire)
	}
	chain := []struct{ definition, member string }{
		{"lob", "bob"},
		{"local-hw-reqs", "lob"},
		{"hw-reqs", "local-hw-reqs"},
	}
	for _, edge := range chain {
		if !directUnionContainsVariable(definition[edge.definition], edge.member) {
			return fmt.Errorf("%s does not directly contain %s", edge.definition, edge.member)
		}
	}
	if !containsIntersection(definition["Exp-obs"], "rf", "ext") ||
		!containsIntersection(definition["Exp-obs"], "ca", "ext") {
		return errors.New("Exp-obs lacks external rf or external ca")
	}
	if !containsSequence(definition["obs"], func(operands []*catLispNode) bool {
		if len(operands) != 2 || !catVariable(operands[0], "Exp-obs") {
			return false
		}
		optional, ok := catUnaryOperator(operands[1], ":opt")
		return ok && catVariable(optional, "sca-class")
	}) {
		return errors.New("obs lacks Exp-obs; sca-class?")
	}
	if !directUnionContainsVariable(definition["ob"], "hw-reqs") ||
		!directUnionContainsVariable(definition["ob"], "obs") ||
		!containsSequence(definition["ob"], func(operands []*catLispNode) bool {
			return len(operands) == 2 && catVariable(operands[0], "ob") && catVariable(operands[1], "ob")
		}) {
		return errors.New("ob lacks hw-reqs, obs, or ob; ob")
	}
	if !containsCATAtom(projection.external, ":irreflexive") ||
		!containsCATVariable(projection.external, "ob") {
		return fmt.Errorf("external test is not irreflexive ob: %s", projection.external.canonical())
	}
	return nil
}

func verifyAArch64ProjectionHashes(projection *aarch64CATProjection) error {
	var missing []string
	for name, want := range pinnedAArch64ProjectionHashes {
		got := expressionHash(projection.definitions[name])
		if want == "" {
			missing = append(missing, fmt.Sprintf("%s=%s", name, got))
			continue
		}
		if got != want {
			return fmt.Errorf("%s AST hash %s, want %s", name, got, want)
		}
	}
	bobArms, _ := catOperator(projection.definitions["bob"], ":union")
	var armHashes []string
	for _, arm := range bobArms {
		has := func(name string) bool { return containsCATVariable(arm, name) }
		if (has("dmb.full") && has("po") && has("Exp") && has("M") && !has("DC.CVAU")) ||
			(has("L") && has("A") && has("po") && !has("Q") && !has("amo")) ||
			(has("A") && has("Q") && has("po") && !has("L")) ||
			(has("L") && has("po") && !has("A") && !has("Q")) {
			armHashes = append(armHashes, expressionHash(arm))
		}
	}
	sort.Strings(armHashes)
	wantArms := append([]string(nil), pinnedAArch64BobArmHashes...)
	sort.Strings(wantArms)
	if len(wantArms) != len(armHashes) || strings.Join(wantArms, ",") != strings.Join(armHashes, ",") {
		missing = append(missing, "bob-arms="+strings.Join(armHashes, ","))
	}
	externalHash := expressionHash(projection.external)
	if pinnedAArch64ExternalIrreflexiveHash == "" {
		missing = append(missing, "external="+externalHash)
	} else if externalHash != pinnedAArch64ExternalIrreflexiveHash {
		return fmt.Errorf("external irreflexive AST hash %s, want %s", externalHash, pinnedAArch64ExternalIrreflexiveHash)
	}
	if len(missing) != 0 {
		sort.Strings(missing)
		return fmt.Errorf("unrecorded pinned CAT AST hashes: %s", strings.Join(missing, " "))
	}
	return nil
}

func replaceFirstCATAtom(node *catLispNode, from, to string) bool {
	if node == nil {
		return false
	}
	if !node.isList() {
		if node.atom == from {
			node.atom = to
			return true
		}
		return false
	}
	for _, child := range node.list {
		if replaceFirstCATAtom(child, from, to) {
			return true
		}
	}
	return false
}

func verifyAArch64ProjectionMutationChecks(projection *aarch64CATProjection) error {
	mutations := []struct{ definition, from string }{
		{"dmb.full", "DMB.ISH"},
		{"bob", "dmb.full"},
		{"lob", "bob"},
		{"local-hw-reqs", "lob"},
		{"hw-reqs", "local-hw-reqs"},
		{"Exp-obs", "rf"},
		{"Exp-obs", "ca"},
		{"obs", "Exp-obs"},
		{"ob", "hw-reqs"},
		{"ob", "obs"},
		{"ob", "ob"},
	}
	for _, mutation := range mutations {
		copyProjection := &aarch64CATProjection{definitions: make(map[string]*catLispNode), external: projection.external.clone()}
		for name, definition := range projection.definitions {
			copyProjection.definitions[name] = definition.clone()
		}
		if !replaceFirstCATAtom(copyProjection.definitions[mutation.definition], mutation.from, mutation.from+".removed") {
			return fmt.Errorf("mutation fixture cannot find %s in %s", mutation.from, mutation.definition)
		}
		if verifyAArch64ProjectionStructure(copyProjection) == nil {
			return fmt.Errorf("projection checker accepted %s without %s", mutation.definition, mutation.from)
		}
	}
	copyProjection := &aarch64CATProjection{definitions: projection.definitions, external: projection.external.clone()}
	if !replaceFirstCATAtom(copyProjection.external, ":irreflexive", ":acyclic") {
		return errors.New("mutation fixture cannot find external irreflexive test")
	}
	if verifyAArch64ProjectionStructure(copyProjection) == nil {
		return errors.New("projection checker accepted a non-irreflexive external test")
	}
	return nil
}

func verifyPinnedAArch64CATProjection(cat2lisp, model, libdir string) error {
	root, err := parsePinnedAArch64CAT(cat2lisp, model, libdir)
	if err != nil {
		return err
	}
	projection, err := extractAArch64CATProjection(root)
	if err != nil {
		return err
	}
	if err := verifyAArch64ProjectionStructure(projection); err != nil {
		return err
	}
	if err := verifyAArch64ProjectionMutationChecks(projection); err != nil {
		return err
	}
	return verifyAArch64ProjectionHashes(projection)
}

func TestCATLispParserRejectsMalformedInput(t *testing.T) {
	deep := strings.Repeat("(", catLispMaxDepth+2) + strings.Repeat(")", catLispMaxDepth+2)
	for _, input := range []string{"", "atom", "(", "())", "(\"unterminated)", "(ok) trailing", deep} {
		if _, err := parseCATLisp([]byte(input)); err == nil {
			t.Errorf("parseCATLisp(%q) succeeded", input)
		}
	}
}

func TestCATLispConflictingDefinitionRejected(t *testing.T) {
	root, err := parseCATLisp([]byte(`(
(:i_let nil (((cat::loc) (cat::pat :pvar "bob") (cat::exp :e_var nil "first"))))
(:i_let nil (((cat::loc) (cat::pat :pvar "bob") (cat::exp :e_var nil "second"))))
)`))
	if err != nil {
		t.Fatal(err)
	}
	bindings := make(map[string][]*catLispNode)
	collectBindings(root, bindings)
	if _, err := uniqueCATDefinition(bindings, "bob"); err == nil {
		t.Fatal("conflicting CAT definitions were accepted")
	}
}

func TestCATSourceBytesDetectChanges(t *testing.T) {
	path := filepath.Join(t.TempDir(), "model.cat")
	original := []byte("let ob = obs\n")
	if err := os.WriteFile(path, original, 0o600); err != nil {
		t.Fatal(err)
	}
	data, err := readCATWorktreeBytes(path, "100644")
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(data, original) {
		t.Fatal("unchanged CAT bytes differ")
	}
	if err := os.WriteFile(path, []byte("let ob = 0\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	data, err = readCATWorktreeBytes(path, "100644")
	if err != nil {
		t.Fatal(err)
	}
	if bytes.Equal(data, original) {
		t.Fatal("changed CAT bytes matched the original")
	}
}
