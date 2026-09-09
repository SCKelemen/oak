package compiler

// Module system loader and elaborator (docs/spec/83-modules.md).
//
// A package build (Compilation.WithPackageDir) locates the module root
// (oak.mod), loads every package the root package transitively imports,
// checks package clauses and import paths, orders the packages
// (modules.Order), and elaborates the whole program into ONE flat syntax tree
// the existing pipeline already understands: every package-level declaration
// of an imported package is renamed to its injective internal name
// (modules.Mangle) throughout that package, and every qualified reference
// `alias.member` in an importing package is resolved — visibility and
// sealing decided by modules.Lookup — to that internal name. The root
// package keeps its source names, so single-file programs are unchanged.
//
// The elaborator is the single resolution authority for package members: the
// type checker, borrow checker, lowering, and backend never see an import.

import (
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/lsp"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/packageapi"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/source"
	"github.com/SCKelemen/oak/stdlib"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/typechecker"
)

// Diagnostic codes of the module family (docs/spec/83-modules.md section 8).
const (
	// CodeImportPathInvalid rejects an import path outside the grammar of
	// section 3.1; the grammar is what makes the directory mapping
	// containment-safe.
	CodeImportPathInvalid = "OAK-M0101"
	// CodeImportUnresolvable rejects an import path that names no package
	// the build can see: no module provides it, the directory is missing
	// or empty, or the standard library package does not exist.
	CodeImportUnresolvable = "OAK-M0102"
	// CodePackageClause rejects a file without a leading package clause,
	// files of one directory disagreeing on the package name, an invalid
	// package name, or a name differing from the directory's import-path
	// segment.
	CodePackageClause = "OAK-M0103"
	// CodeImportCycle rejects a package graph with an import cycle; the
	// diagnostic names one concrete cycle.
	CodeImportCycle = "OAK-M0104"
	// CodeNoSuchMember rejects `alias.name` when the package declares no
	// such package-level name.
	CodeNoSuchMember = "OAK-M0105"
	// CodeMemberNotExported rejects `alias.name` when the declaration exists
	// but is not marked pub.
	CodeMemberNotExported = "OAK-M0106"
	// CodeImportAlias rejects alias misuse: a bare alias used as a value or
	// redeclared, two imports binding one alias to different paths, an
	// alias colliding with a package-level declaration or a compiler-known
	// library, and an unused import.
	CodeImportAlias = "OAK-M0107"
	// CodeReservedIdentifier rejects identifiers containing `__`, which are
	// reserved for internal names (the capture-freedom rule).
	CodeReservedIdentifier = "OAK-M0108"
	// CodeSignatureMismatch rejects a sealed import whose package does not
	// provide a signature member with the demanded kind, and access through
	// a sealed import to a member outside the signature.
	CodeSignatureMismatch = "OAK-M0109"
	// CodeImportPlacement rejects `import(...)` anywhere other than a
	// top-level import statement or a top-level binding initializer, and
	// imports that follow declarations.
	CodeImportPlacement = "OAK-M0111"
	// CodeManifest rejects an unreadable or malformed oak.mod, a dependency
	// module that cannot be located, or a module whose manifest disagrees
	// with the path it was required under.
	CodeManifest = "OAK-M0112"
	// CodeMethodOrphan rejects a method whose receiver type belongs to
	// another package: methods are declared where their type is declared
	// (the orphan rule, section 6.5).
	CodeMethodOrphan = "OAK-M0114"
	// CodeGenericPackageArity rejects importing a generic package without
	// arguments, a non-generic package with arguments, or with the wrong
	// number of arguments (section 6.7).
	CodeGenericPackageArity = "OAK-M0301"
	// CodeGenericPackageArgument rejects an instantiation argument the
	// loader cannot resolve to a type or constant.
	CodeGenericPackageArgument = "OAK-M0302"
)

// ModuleInfo is what elaboration hands the later phases.
type ModuleInfo struct {
	// Public is the root package's own syntax, the surface API tooling
	// projects from.
	Public *ast.Program
	// OpaqueTypes maps an internal type name to its declaring package path
	// for every pub(opaque) declaration.
	OpaqueTypes map[string]string
	// Obligations are the sealed-import member types the type checker must
	// verify after checking the program.
	Obligations []typechecker.SignatureObligation
	// Parameters are the generic package instantiation constraints the
	// type checker must verify.
	Parameters []typechecker.ParameterObligation
	// SealedOpaque maps an internal type name to the packages that sealed
	// it as an abstract type member.
	SealedOpaque map[string]map[string]bool
	// PreludeCore requests the core prelude (std.oak) because a standard
	// library package was imported; `import(std)` requests the full one.
	PreludeCore bool
	// LibraryNames maps the flat names of imported standard library
	// packages' exports to their internal names, for the library sugar.
	LibraryNames map[string]string
	// Sealed lists every sealed import of the build with the canonical
	// member contract each signature demands, for offline compatibility
	// checks against a dependency's API snapshot
	// (docs/spec/82-package-semver.md section 8).
	Sealed []SealedImport
	// Abstract maps each fresh abstract type (one per sealed binding and
	// type member) to the internal name of its underlying type.
	Abstract map[string]string
	// Packages lists the loaded package paths in compile order (root last).
	Packages []string
}

// bootstrapImports are the prelude-style imports the standard-library
// loader splices in unqualified (docs/spec/83-modules.md section 9).
var bootstrapImports = map[string]bool{"std": true, "testing": true}

type packageFile struct {
	Path string
	Text string
	Root *ast.Program
	File *source.File
}

type importBinding struct {
	Alias     string
	Path      string
	Signature ast.Expression
	Statement *ast.ImportStatement
	File      string
	Used      bool
	// Selective lists the unqualified names of `{ f, g } := import(path)`.
	Selective []*ast.Identifier
	// Arguments instantiate a generic package; Template is the generic
	// package's path when Path names an instance.
	Arguments []ast.Expression
	Template  string
	// resolved signature members (nil when unsealed)
	sig      *modules.Signature
	sigOrder []string
	sigKinds map[string]modules.MemberKind
	shape    *ast.RecordLiteral
	// abstract type members: source name -> fresh internal type name
	abstractNames map[string]string
	// value members whose signature mentions abstract members: coercions
	// to insert at call sites (parameter positions and result)
	coerce map[string]*memberCoercion
}

// memberCoercion records where a sealed value member's signature uses
// abstract type members: params[i] and result name the fresh type or "".
type memberCoercion struct {
	params []string
	result string
	// value is the fresh type of a non-function member of abstract type.
	value string
}

type loadedPackage struct {
	Path    string
	Dir     string
	Name    string
	IsRoot  bool
	Files   []*packageFile
	Imports map[string]*importBinding // by alias
	Edges   []string                  // imported package paths
	Exports modules.Exports
	Renames map[string]string
	// TemplatePath is the generic package's import path when this package
	// is an instantiation (Path carries the arguments after '@').
	TemplatePath string
	// Selective maps unqualified selective-import names to their binding.
	Selective map[string]*importBinding
	// pendingParams are instantiation constraints awaiting the instance's
	// rename table (finishPackage).
	pendingParams []typechecker.ParameterObligation
	Bootstrap     map[string]*ast.ImportStatement
	// statements after elaboration, in source order across files
	Statements []ast.Statement
}

// SealedImport is one sealed import's contract: the dependency package and
// the members the importing package relies on.
type SealedImport struct {
	Importer string
	Alias    string
	Package  string
	Members  []SealedMember
}

// SealedMember is one signature member: a type member (Kind "type") or a
// value member with the canonical type text the signature requires, spelled
// as the dependency's own snapshot spells it.
type SealedMember struct {
	Name string
	Kind string
	Type string
}

type moduleRoot struct {
	Dir      string
	Manifest modules.Manifest
}

type moduleLoader struct {
	comp        Compilation
	cache       string
	root        *moduleRoot
	located     map[string]*moduleRoot
	packages    map[string]*loadedPackage
	diagnostics []*diagnostic.Diagnostic
	nextFileID  source.ID
	opaque      map[string]string
	sealed      map[string]map[string]bool
	abstract    map[string]string
	sealedList  []SealedImport
	preludeCore bool
	parameters  []typechecker.ParameterObligation
	// session relaxes the unused-import rule for the root package: a REPL
	// imports first and uses later.
	session     bool
	obligations []typechecker.SignatureObligation
}

// WithPackageDir configures a whole-package build: dir is compiled as the
// root package together with every package it imports, resolved through the
// enclosing module's oak.mod (docs/spec/83-modules.md section 4).
func (comp Compilation) WithPackageDir(dir string) Compilation {
	comp.packageDir = dir
	return comp
}

// WithTestFiles includes `*_test.oak` files of the root package in a
// package build (the `oak test` runner's contract).
func (comp Compilation) WithTestFiles(include bool) Compilation {
	comp.includeTests = include
	return comp
}

// WithModuleCache sets the directory where required modules are looked up
// as `<path>@v<version>`; the default is $OAKMODCACHE.
func (comp Compilation) WithModuleCache(dir string) Compilation {
	comp.moduleCache = dir
	return comp
}

// WithSessionSources configures an in-memory root package (the REPL's
// session): files are named sources, and imports resolve through the module
// enclosing moduleDir (the working directory, typically) as if the package
// lived at `<module path>/repl`. Nothing is written to disk.
func (comp Compilation) WithSessionSources(moduleDir string, files map[string]string) Compilation {
	comp.packageDir = moduleDir
	comp.sessionFiles = files
	return comp
}

func (comp Compilation) parsePackageBuild() (*SyntaxTree, error) {
	loader := &moduleLoader{
		comp:     comp,
		cache:    comp.moduleCache,
		located:  map[string]*moduleRoot{},
		packages: map[string]*loadedPackage{},
		opaque:   map[string]string{},
		sealed:   map[string]map[string]bool{},
		abstract: map[string]string{},
	}
	if loader.cache == "" {
		loader.cache = os.Getenv("OAKMODCACHE")
	}
	if comp.sessionFiles != nil {
		tree, ok := loader.loadSession(comp.packageDir, comp.sessionFiles)
		if !ok || len(loader.diagnostics) != 0 {
			if len(loader.diagnostics) == 0 {
				return nil, fmt.Errorf("modules failed")
			}
			return nil, &DiagnosticError{Phase: "modules", Diagnostics: loader.diagnostics}
		}
		return tree, nil
	}
	tree, ok := loader.load(comp.packageDir)
	if !ok || len(loader.diagnostics) != 0 {
		if len(loader.diagnostics) == 0 {
			return nil, fmt.Errorf("modules failed")
		}
		return nil, &DiagnosticError{Phase: "modules", Diagnostics: loader.diagnostics}
	}
	return tree, nil
}

func (l *moduleLoader) report(code string, node ast.Node, format string, args ...interface{}) *diagnostic.Diagnostic {
	title := fmt.Sprintf(format, args...)
	var d *diagnostic.Diagnostic
	if node != nil {
		d = diagnostic.NewDiagnosticFromNodeWithCode(node, "compiler", code, title)
	} else {
		d = diagnostic.NewDiagnosticWithCode(lsp.Range{}, "compiler", code, title)
	}
	l.diagnostics = append(l.diagnostics, d)
	return d
}

func (l *moduleLoader) reportAt(code string, file string, node ast.Node, format string, args ...interface{}) *diagnostic.Diagnostic {
	title := fmt.Sprintf(format, args...)
	if file != "" {
		title = file + ": " + title
	}
	return l.report(code, node, "%s", title)
}

// load drives the build: module root, package graph, order, elaboration.
func (l *moduleLoader) load(dir string) (*SyntaxTree, bool) {
	absDir, err := filepath.Abs(dir)
	if err != nil {
		l.report(CodeManifest, nil, "package directory %s: %v", dir, err)
		return nil, false
	}
	info, err := os.Stat(absDir)
	if err != nil || !info.IsDir() {
		l.report(CodeManifest, nil, "package directory %s is not a directory", dir)
		return nil, false
	}
	rootPath := "main"
	if root, found := l.findModuleRoot(absDir); found {
		if !l.locateDependencies() {
			return nil, false
		}
		rel, err := filepath.Rel(root.Dir, absDir)
		if err != nil {
			l.report(CodeManifest, nil, "package directory %s is outside module root %s", absDir, root.Dir)
			return nil, false
		}
		rootPath = root.Manifest.Path
		if rel != "." {
			rootPath = root.Manifest.Path + "/" + filepath.ToSlash(rel)
		}
	} else if len(l.diagnostics) != 0 {
		return nil, false
	}
	rootPkg := l.loadPackage(absDir, rootPath, true)
	if rootPkg == nil {
		return nil, false
	}
	if len(l.diagnostics) != 0 {
		return nil, false
	}
	return l.orderAndElaborate(rootPkg)
}

// orderAndElaborate orders the loaded graph, elaborates every package in
// dependency order, and merges the program.
func (l *moduleLoader) orderAndElaborate(rootPkg *loadedPackage) (*SyntaxTree, bool) {
	// Order the closed graph.
	nodes := make([]string, 0, len(l.packages))
	graph := map[string][]string{}
	for path, pkg := range l.packages {
		nodes = append(nodes, path)
		graph[path] = pkg.Edges
	}
	order, stuck := modules.Order(nodes, graph)
	if len(stuck) != 0 {
		cycle := modules.ImportCycle(stuck, graph)
		var node ast.Node
		if first := l.packages[cycle[0]]; first != nil {
			for _, binding := range first.Imports {
				if len(cycle) > 1 && binding.Path == cycle[1] || len(cycle) == 1 && binding.Path == cycle[0] {
					node = binding.Statement
				}
			}
		}
		d := l.report(CodeImportCycle, node, "import cycle: %s", strings.Join(append(cycle, cycle[0]), " -> "))
		d.AddNote("packages form a directed acyclic graph; move the shared declarations into a package both sides import")
		return nil, false
	}
	// Elaborate dependencies first so their exports are known to importers.
	for _, path := range order {
		l.elaborate(l.packages[path])
	}
	if len(l.diagnostics) != 0 {
		return nil, false
	}
	return l.merge(order, rootPkg), true
}

// loadSession builds an in-memory root package (the REPL session) inside the
// module enclosing moduleDir, or outside any module when there is none.
func (l *moduleLoader) loadSession(moduleDir string, files map[string]string) (*SyntaxTree, bool) {
	absDir, err := filepath.Abs(moduleDir)
	if err != nil {
		l.report(CodeManifest, nil, "session directory %s: %v", moduleDir, err)
		return nil, false
	}
	l.session = true
	rootPath := "main"
	if root, found := l.findModuleRoot(absDir); found {
		if !l.locateDependencies() {
			return nil, false
		}
		rootPath = root.Manifest.Path + "/repl"
	} else if len(l.diagnostics) != 0 {
		return nil, false
	}
	pkg := &loadedPackage{
		Path:         rootPath,
		Dir:          absDir,
		IsRoot:       true,
		TemplatePath: rootPath,
		Imports:      map[string]*importBinding{},
		Selective:    map[string]*importBinding{},
		Exports:      modules.Exports{},
		Renames:      map[string]string{},
		Bootstrap:    map[string]*ast.ImportStatement{},
	}
	l.packages[rootPath] = pkg
	names := make([]string, 0, len(files))
	for name := range files {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		file, parsed := l.parseFile(name, files[name])
		if !parsed {
			return nil, false
		}
		pkg.Files = append(pkg.Files, file)
	}
	if len(pkg.Files) == 0 {
		l.report(CodeManifest, nil, "session has no source")
		return nil, false
	}
	if l.finishPackage(pkg, nil, nil) == nil || len(l.diagnostics) != 0 {
		return nil, false
	}
	return l.orderAndElaborate(pkg)
}

// findModuleRoot walks up from dir looking for oak.mod.
func (l *moduleLoader) findModuleRoot(dir string) (*moduleRoot, bool) {
	current := dir
	for {
		candidate := filepath.Join(current, modules.ManifestFile)
		if info, err := os.Stat(candidate); err == nil && !info.IsDir() {
			manifest, ok := l.readManifest(candidate)
			if !ok {
				return nil, false
			}
			l.root = &moduleRoot{Dir: current, Manifest: manifest}
			l.located[manifest.Path] = l.root
			return l.root, true
		}
		parent := filepath.Dir(current)
		if parent == current {
			return nil, false
		}
		current = parent
	}
}

func (l *moduleLoader) readManifest(path string) (modules.Manifest, bool) {
	info, err := os.Stat(path)
	if err != nil {
		l.report(CodeManifest, nil, "%s: %v", path, err)
		return modules.Manifest{}, false
	}
	if info.Size() > modules.MaxManifestSize {
		l.report(CodeManifest, nil, "%s exceeds %d bytes", path, modules.MaxManifestSize)
		return modules.Manifest{}, false
	}
	text, err := os.ReadFile(path)
	if err != nil {
		l.report(CodeManifest, nil, "%s: %v", path, err)
		return modules.Manifest{}, false
	}
	manifest, err := modules.ParseManifest(string(text))
	if err != nil {
		l.report(CodeManifest, nil, "%s: %v", filepath.Dir(path), err)
		return modules.Manifest{}, false
	}
	return manifest, true
}

// locateDependencies performs minimal version selection over every manifest
// reachable from the root and locates each selected module on disk.
func (l *moduleLoader) locateDependencies() bool {
	requirements := append([]modules.Requirement(nil), l.root.Manifest.Requires...)
	versions := map[string]packageapi.Version{}
	for iteration := 0; iteration < 1000; iteration++ {
		selected := modules.Select(requirements)
		stable := true
		for _, path := range modules.SelectedPaths(selected) {
			version := selected[path]
			if have, seen := versions[path]; seen && have == version {
				continue
			}
			stable = false
			versions[path] = version
			root, ok := l.locateModule(path, version)
			if !ok {
				return false
			}
			l.located[path] = root
			requirements = append(requirements, root.Manifest.Requires...)
		}
		if stable {
			return true
		}
	}
	l.report(CodeManifest, nil, "module graph did not stabilize")
	return false
}

func (l *moduleLoader) locateModule(path string, version packageapi.Version) (*moduleRoot, bool) {
	var dir string
	if replacement, replaced := l.root.Manifest.Replaces[path]; replaced {
		dir = replacement
		if !filepath.IsAbs(dir) {
			dir = filepath.Join(l.root.Dir, filepath.FromSlash(dir))
		}
	} else {
		if l.cache == "" {
			l.report(CodeManifest, nil, "module %s v%s is required but no replace directive and no module cache ($OAKMODCACHE) provide it", path, version)
			return nil, false
		}
		dir = filepath.Join(l.cache, filepath.FromSlash(path)+"@v"+version.String())
	}
	dir, err := filepath.Abs(dir)
	if err != nil {
		l.report(CodeManifest, nil, "module %s: %v", path, err)
		return nil, false
	}
	manifestPath := filepath.Join(dir, modules.ManifestFile)
	if _, err := os.Stat(manifestPath); err != nil {
		l.report(CodeManifest, nil, "module %s v%s: %s has no %s", path, version, dir, modules.ManifestFile)
		return nil, false
	}
	manifest, ok := l.readManifest(manifestPath)
	if !ok {
		return nil, false
	}
	if manifest.Path != path {
		l.report(CodeManifest, nil, "module at %s declares path %q but was required as %q", dir, manifest.Path, path)
		return nil, false
	}
	return &moduleRoot{Dir: dir, Manifest: manifest}, true
}

// resolveImportDir maps an import path to the directory of its package.
func (l *moduleLoader) resolveImportDir(path string) (string, bool) {
	var candidates []string
	for modulePath := range l.located {
		if modules.HasPathPrefix(path, modulePath) {
			candidates = append(candidates, modulePath)
		}
	}
	if len(candidates) == 0 {
		return "", false
	}
	// The longest module path wins (nested modules are not supported, but
	// the rule is deterministic either way).
	sort.Slice(candidates, func(i, j int) bool { return len(candidates[i]) > len(candidates[j]) })
	root := l.located[candidates[0]]
	rel := strings.TrimPrefix(strings.TrimPrefix(path, candidates[0]), "/")
	dir := root.Dir
	if rel != "" {
		dir = filepath.Join(root.Dir, filepath.FromSlash(rel))
	}
	// Containment: the resolved directory must lie within the module root,
	// through symlinks too.
	rootReal, err := filepath.EvalSymlinks(root.Dir)
	if err != nil {
		return "", false
	}
	dirReal, err := filepath.EvalSymlinks(dir)
	if err != nil {
		return "", false
	}
	relCheck, err := filepath.Rel(rootReal, dirReal)
	if err != nil || relCheck == ".." || strings.HasPrefix(relCheck, ".."+string(filepath.Separator)) {
		return "", false
	}
	return dir, true
}

// parseFile runs the canonical front end on one file with its own source id.
func (l *moduleLoader) parseFile(path, text string) (*packageFile, bool) {
	if offset, ok := source.ValidateUTF8(text); !ok {
		l.report(CodeManifest, nil, "%s: source is not valid UTF-8 at byte offset %d", path, offset)
		return nil, false
	}
	l.nextFileID++
	file := source.NewFile(l.nextFileID, path, text)
	tokens := layout.New(scanner.NewFile(file))
	p := parser.New(tokens)
	root := p.ParseProgram()
	if errors := p.Errors(); len(errors) != 0 {
		for _, message := range errors {
			l.report("OAK-P0000", nil, "%s: %s", path, message)
		}
		return nil, false
	}
	return &packageFile{Path: path, Text: text, Root: root, File: file}, true
}

// loadPackage reads a package directory, checks its clause and imports, and
// recursively loads what it imports. It returns nil after reporting.
func (l *moduleLoader) loadPackage(dir, path string, isRoot bool) *loadedPackage {
	return l.loadPackageInstance(dir, path, path, nil, nil, isRoot)
}

// loadPackageInstance loads a package directory as the package `path`; when
// arguments are given, `template` is the generic package's path and the
// files are instantiated by substituting its parameters (section 6.7).
func (l *moduleLoader) loadPackageInstance(dir, path, template string, arguments []ast.Expression, importer *importBinding, isRoot bool) *loadedPackage {
	if existing, loaded := l.packages[path]; loaded {
		return existing
	}
	pkg := &loadedPackage{
		Path:         path,
		Dir:          dir,
		IsRoot:       isRoot,
		TemplatePath: template,
		Imports:      map[string]*importBinding{},
		Selective:    map[string]*importBinding{},
		Exports:      modules.Exports{},
		Renames:      map[string]string{},
		Bootstrap:    map[string]*ast.ImportStatement{},
	}
	// Register before recursing so cycles terminate; Order reports them.
	l.packages[path] = pkg
	entries, err := os.ReadDir(dir)
	if err != nil {
		l.report(CodeImportUnresolvable, nil, "package %s: %v", path, err)
		return nil
	}
	var names []string
	for _, entry := range entries {
		name := entry.Name()
		if entry.IsDir() || !strings.HasSuffix(name, ".oak") || strings.HasPrefix(name, ".") {
			continue
		}
		if strings.HasSuffix(name, "_test.oak") && !(isRoot && l.comp.includeTests) {
			continue
		}
		names = append(names, name)
	}
	sort.Strings(names)
	if len(names) == 0 {
		l.report(CodeImportUnresolvable, nil, "package %s: directory %s contains no .oak files", path, dir)
		return nil
	}
	ok := true
	for _, name := range names {
		filePath := filepath.Join(dir, name)
		text, err := os.ReadFile(filePath)
		if err != nil {
			l.report(CodeImportUnresolvable, nil, "%s: %v", filePath, err)
			return nil
		}
		file, parsed := l.parseFile(filePath, string(text))
		if !parsed {
			ok = false
			continue
		}
		pkg.Files = append(pkg.Files, file)
	}
	if !ok {
		return nil
	}
	return l.finishPackage(pkg, arguments, importer)
}

// loadStdlibPackage loads an embedded standard library file as a real
// package (docs/spec/83-modules.md section 9): its declarations are renamed
// like any dependency, its own library imports resolve recursively, and the
// core prelude is spliced into the program for the names it uses unqualified.
func (l *moduleLoader) loadStdlibPackage(path, text string) *loadedPackage {
	if existing, loaded := l.packages[path]; loaded {
		return existing
	}
	pkg := &loadedPackage{
		Path:         path,
		Dir:          "<stdlib>",
		TemplatePath: path,
		Imports:      map[string]*importBinding{},
		Selective:    map[string]*importBinding{},
		Exports:      modules.Exports{},
		Renames:      map[string]string{},
		Bootstrap:    map[string]*ast.ImportStatement{},
	}
	l.packages[path] = pkg
	l.preludeCore = true
	file, parsed := l.parseFile("<stdlib>/"+path+".oak", text)
	if !parsed {
		return nil
	}
	pkg.Files = []*packageFile{file}
	return l.finishPackage(pkg, nil, nil)
}

// finishPackage runs the per-package steps after its files are parsed:
// instantiation, clause check, declaration and import tables, and the
// recursive load of what it imports.
func (l *moduleLoader) finishPackage(pkg *loadedPackage, arguments []ast.Expression, importer *importBinding) *loadedPackage {
	if !l.instantiate(pkg, arguments, importer) {
		return nil
	}
	if !l.checkPackageClause(pkg) {
		return nil
	}
	l.collectDeclarations(pkg)
	// Parameter constraints name the template's own declarations; resolve
	// them to the instance's internal names now that the rename table exists.
	for _, obligation := range pkg.pendingParams {
		(&syntaxVisitor{ident: func(id *ast.Identifier, label bool) {
			if label {
				return
			}
			if internal, renamed := pkg.Renames[id.Value]; renamed {
				id.Value = internal
			}
		}}).walk(reflect.ValueOf(&obligation.Constraint).Elem(), false)
		l.parameters = append(l.parameters, obligation)
	}
	pkg.pendingParams = nil
	if !l.collectImports(pkg) {
		return nil
	}
	for _, alias := range sortedAliases(pkg.Imports) {
		binding := pkg.Imports[alias]
		if bootstrapImports[binding.Path] {
			continue
		}
		if _, loaded := l.packages[binding.Path]; loaded {
			continue
		}
		if len(binding.Arguments) != 0 {
			depDir, found := l.resolveImportDir(binding.Template)
			if !found {
				l.reportAt(CodeImportUnresolvable, binding.File, binding.Statement, "cannot resolve import %q", binding.Template)
				continue
			}
			l.loadPackageInstance(depDir, binding.Path, binding.Template, binding.Arguments, binding, false)
			continue
		}
		if librarySource, isLibrary := stdlib.Packages[binding.Path]; isLibrary {
			l.loadStdlibPackage(binding.Path, librarySource)
			continue
		}
		depDir, found := l.resolveImportDir(binding.Path)
		if !found {
			d := l.reportAt(CodeImportUnresolvable, binding.File, binding.Statement, "cannot resolve import %q", binding.Path)
			if modules.IsStandardLibraryPath(binding.Path) {
				d.AddNote("only the bootstrap standard library imports std and testing exist today")
			} else if l.root == nil {
				d.AddNote("the package is not inside a module: add an oak.mod with a module directive to import packages")
			} else {
				d.AddHelp("require the module providing the package in oak.mod, or check the directory exists under the module root")
			}
			continue
		}
		if l.loadPackage(depDir, binding.Path, false) == nil {
			continue
		}
	}
	return pkg
}

func sortedAliases(imports map[string]*importBinding) []string {
	aliases := make([]string, 0, len(imports))
	for alias := range imports {
		aliases = append(aliases, alias)
	}
	sort.Strings(aliases)
	return aliases
}

// checkPackageClause enforces section 2: every file opens with the same
// package clause, the name is valid, and an importable package is named
// after its directory segment.
func (l *moduleLoader) checkPackageClause(pkg *loadedPackage) bool {
	ok := true
	for _, file := range pkg.Files {
		var clause *ast.PackageStatement
		if len(file.Root.Statements) != 0 {
			clause, _ = file.Root.Statements[0].(*ast.PackageStatement)
		}
		if clause == nil {
			// The root package may omit the clause: a clause-less file is
			// `package main`, the single-file rule (section 2). Imported
			// packages must declare theirs.
			if !pkg.IsRoot {
				var node ast.Node
				if len(file.Root.Statements) != 0 {
					node = file.Root.Statements[0]
				}
				l.reportAt(CodePackageClause, file.Path, node, "an imported package's file must begin with a package clause")
				ok = false
				continue
			}
			if pkg.Name == "" {
				pkg.Name = "main"
			} else if pkg.Name != "main" {
				l.reportAt(CodePackageClause, file.Path, nil, "file without a package clause is package main, but a sibling declares %q", pkg.Name)
				ok = false
			}
			continue
		}
		name := clause.Name.Value
		if !modules.ValidPackageName(name) {
			l.reportAt(CodePackageClause, file.Path, clause, "invalid package name %q (lowercase ASCII identifier, no __)", name)
			ok = false
			continue
		}
		if pkg.Name == "" {
			pkg.Name = name
		} else if pkg.Name != name {
			l.reportAt(CodePackageClause, file.Path, clause, "package clause %q disagrees with %q in a sibling file", name, pkg.Name)
			ok = false
		}
		for _, stmt := range declarationsOf(file) {
			if _, again := stmt.(*ast.PackageStatement); again {
				l.reportAt(CodePackageClause, file.Path, stmt, "duplicate package clause")
				ok = false
			}
		}
	}
	if !ok {
		return false
	}
	if !pkg.IsRoot && pkg.Name != modules.LastSegment(pkg.TemplatePath) {
		l.reportAt(CodePackageClause, pkg.Files[0].Path, pkg.Files[0].Root.Statements[0], "package %q must be named after its import path segment %q (import path %s)", pkg.Name, modules.LastSegment(pkg.TemplatePath), pkg.TemplatePath)
		return false
	}
	if !pkg.IsRoot && pkg.Name == "main" {
		l.reportAt(CodePackageClause, pkg.Files[0].Path, pkg.Files[0].Root.Statements[0], "package main cannot be imported")
		return false
	}
	return true
}

// declarationsOf returns a file's statements after its package clause.
func declarationsOf(file *packageFile) []ast.Statement {
	if len(file.Root.Statements) != 0 {
		if _, isClause := file.Root.Statements[0].(*ast.PackageStatement); isClause {
			return file.Root.Statements[1:]
		}
	}
	return file.Root.Statements
}

// collectDeclarations builds the export table and the rename map.
func (l *moduleLoader) collectDeclarations(pkg *loadedPackage) {
	seen := map[string]string{}
	for _, file := range pkg.Files {
		for _, stmt := range file.Root.Statements {
			name, kind, exported, opaque, renamable := declarationMember(stmt)
			if name == "" {
				continue
			}
			if prior, dup := seen[name]; dup && kind != modules.KindValue {
				l.reportAt(CodePackageClause, file.Path, stmt, "%s redeclared (first in %s)", name, prior)
				continue
			}
			seen[name] = file.Path
			pkg.Exports[name] = modules.Member{Name: name, Kind: kind, Exported: exported, Opaque: opaque}
			if renamable && !pkg.IsRoot {
				pkg.Renames[name] = modules.Mangle(pkg.Path, name)
			}
			if opaque {
				internal := name
				if !pkg.IsRoot {
					internal = modules.Mangle(pkg.Path, name)
				}
				l.opaque[internal] = pkg.Path
			}
		}
	}
}

// declarationMember classifies a top-level statement. Methods and tag
// schemas are looked up by label, never renamed (section 7).
func declarationMember(stmt ast.Statement) (name string, kind modules.MemberKind, exported, opaque, renamable bool) {
	switch s := stmt.(type) {
	case *ast.FunctionStatement:
		if s.Name == nil {
			return "", 0, false, false, false
		}
		if s.Receiver != nil {
			return "", 0, false, false, false
		}
		return s.Name.Value, modules.KindValue, s.Exported, false, true
	case *ast.VariableDeclaration:
		if s.Name == nil {
			return "", 0, false, false, false
		}
		return s.Name.Value, modules.KindValue, s.Exported, false, true
	case *ast.ADTType:
		if s.Name == nil {
			return "", 0, false, false, false
		}
		return s.Name.Value, modules.KindType, s.Exported, s.Opaque, true
	case *ast.InterfaceType:
		if s.Name == nil {
			return "", 0, false, false, false
		}
		return s.Name.Value, modules.KindInterface, s.Exported, false, true
	case *ast.TagDeclaration:
		if s.Name == nil {
			return "", 0, false, false, false
		}
		return s.Name.Value, modules.KindTag, s.Exported, false, true
	}
	return "", 0, false, false, false
}

// collectImports validates the import statements of every file and merges
// them into the package's alias table (imports are package-scoped, section
// 3.3).
func (l *moduleLoader) collectImports(pkg *loadedPackage) bool {
	ok := true
	for _, file := range pkg.Files {
		declarationsStarted := false
		for _, stmt := range declarationsOf(file) {
			imp, isImport := stmt.(*ast.ImportStatement)
			if !isImport {
				declarationsStarted = true
				continue
			}
			if declarationsStarted {
				l.reportAt(CodeImportPlacement, file.Path, imp, "imports must precede declarations")
				ok = false
			}
			if imp.Path == nil {
				l.reportAt(CodeImportPathInvalid, file.Path, imp, "import without a path")
				ok = false
				continue
			}
			path := imp.Path.Value
			if err := modules.ValidateImportPath(path); err != nil {
				l.reportAt(CodeImportPathInvalid, file.Path, imp, "%v", err)
				ok = false
				continue
			}
			if bootstrapImports[path] {
				if imp.Alias != nil || imp.Signature != nil {
					l.reportAt(CodeImportPlacement, file.Path, imp, "the bootstrap import %s is unqualified and cannot be bound or sealed", path)
					ok = false
					continue
				}
				pkg.Bootstrap[path] = imp
				continue
			}
			if len(imp.Names) != 0 {
				if imp.Signature != nil {
					l.reportAt(CodeImportPlacement, file.Path, imp, "a selective import cannot be sealed")
					ok = false
					continue
				}
				binding := &importBinding{Path: path, Template: path, Statement: imp, File: file.Path, Selective: imp.Names, Arguments: imp.Arguments}
				if len(imp.Arguments) != 0 {
					binding.Path = l.instancePath(pkg, imp.Path.Value, imp.Arguments, file, imp)
				}
				for _, name := range imp.Names {
					if modules.Reserved(name.Value) {
						l.reportAt(CodeReservedIdentifier, file.Path, name, "identifier %q contains the reserved sequence __", name.Value)
						ok = false
						continue
					}
					if _, declared := pkg.Exports[name.Value]; declared {
						l.reportAt(CodeImportAlias, file.Path, name, "selective import %q collides with a package-level declaration", name.Value)
						ok = false
						continue
					}
					if _, dup := pkg.Selective[name.Value]; dup {
						l.reportAt(CodeImportAlias, file.Path, name, "selective import %q is bound twice", name.Value)
						ok = false
						continue
					}
					if _, isAlias := pkg.Imports[name.Value]; isAlias {
						l.reportAt(CodeImportAlias, file.Path, name, "selective import %q collides with an import alias", name.Value)
						ok = false
						continue
					}
					pkg.Selective[name.Value] = binding
				}
				pkg.Imports["{"+binding.Path] = binding
				pkg.Edges = append(pkg.Edges, binding.Path)
				continue
			}
			alias := modules.LastSegment(path)
			if imp.Alias != nil {
				alias = imp.Alias.Value
			}
			if !modules.ValidPackageName(alias) && imp.Alias == nil {
				l.reportAt(CodeImportPathInvalid, file.Path, imp, "import path %q does not end in a package name; bind it explicitly (name := import(...))", path)
				ok = false
				continue
			}
			if modules.Reserved(alias) {
				l.reportAt(CodeReservedIdentifier, file.Path, imp, "import alias %q contains the reserved sequence __", alias)
				ok = false
				continue
			}
			if typechecker.CompilerKnownLibrary(alias) || alias == "derive" {
				l.reportAt(CodeImportAlias, file.Path, imp, "import alias %q is a compiler-known library name", alias)
				ok = false
				continue
			}
			if _, declared := pkg.Exports[alias]; declared {
				l.reportAt(CodeImportAlias, file.Path, imp, "import alias %q collides with a package-level declaration", alias)
				ok = false
				continue
			}
			if existing, dup := pkg.Imports[alias]; dup {
				if existing.Path != path {
					l.reportAt(CodeImportAlias, file.Path, imp, "import alias %q already binds %q (in %s)", alias, existing.Path, existing.File)
					ok = false
				} else if imp.Signature != nil || existing.Signature != nil {
					l.reportAt(CodeImportAlias, file.Path, imp, "import %q is bound in more than one file with a signature; seal it once", path)
					ok = false
				}
				continue
			}
			binding := &importBinding{Alias: alias, Path: path, Template: path, Signature: imp.Signature, Statement: imp, File: file.Path, Arguments: imp.Arguments}
			if len(imp.Arguments) != 0 {
				binding.Path = l.instancePath(pkg, imp.Path.Value, imp.Arguments, file, imp)
			}
			if _, selective := pkg.Selective[alias]; selective {
				l.reportAt(CodeImportAlias, file.Path, imp, "import alias %q collides with a selective import", alias)
				ok = false
				continue
			}
			pkg.Imports[alias] = binding
			pkg.Edges = append(pkg.Edges, binding.Path)
		}
	}
	sort.Strings(pkg.Edges)
	return ok
}

// elaborate renames a dependency's declarations and resolves the package's
// qualified references. Dependencies are elaborated before importers.
func (l *moduleLoader) elaborate(pkg *loadedPackage) {
	// Reserved identifiers are checked before any renaming introduces __.
	for _, file := range pkg.Files {
		(&syntaxVisitor{ident: func(id *ast.Identifier, label bool) {
			if !label && modules.Reserved(id.Value) && !strings.Contains(id.Value, ".") {
				l.reportAt(CodeReservedIdentifier, file.Path, id, "identifier %q contains the reserved sequence __", id.Value)
			}
		}}).walk(reflect.ValueOf(file.Root), false)
	}
	// Methods live with their receiver type (section 6.5).
	for _, file := range pkg.Files {
		for _, stmt := range declarationsOf(file) {
			fn, isFn := stmt.(*ast.FunctionStatement)
			if !isFn || fn.Receiver == nil || fn.Receiver.Type == nil {
				continue
			}
			base := firstIdentifier(fn.Receiver.Type)
			if base == nil {
				continue
			}
			if library, _, qualified := splitDotted(base.Value); qualified {
				if binding := pkg.Imports[library]; binding != nil {
					d := l.reportAt(CodeMethodOrphan, file.Path, fn.Receiver.Type, "method %s declared on %s, a type of package %s", fn.Name.Value, base.Value, binding.Path)
					d.AddNote("methods are declared in the package that declares their receiver type; write a function taking the value instead")
				}
			}
		}
	}
	// Sealed imports: resolve the signature shape, check membership and
	// kind, and substitute type members before names are rewritten.
	for _, alias := range sortedAliases(pkg.Imports) {
		l.prepareSignature(pkg, pkg.Imports[alias])
	}
	// Selective imports bind unqualified names through the same lookup.
	for name, binding := range pkg.Selective {
		target := l.packages[binding.Path]
		if target == nil {
			continue
		}
		internal := l.resolveMember(pkg, nil, binding, name, binding.Statement)
		pkg.Renames[name] = internal
	}
	for _, file := range pkg.Files {
		visitor := &syntaxVisitor{
			expr: func(slot reflect.Value) {
				switch node := slot.Interface().(type) {
				case *ast.InvocationExpression:
					if replacement := l.rewriteSealedCall(pkg, file, node); replacement != nil {
						slot.Set(reflect.ValueOf(ast.Expression(replacement)))
					}
				case *ast.IndexExpression:
					if !node.Dot {
						return
					}
					base, isIdent := node.Left.(*ast.Identifier)
					if !isIdent {
						return
					}
					binding := pkg.Imports[base.Value]
					if binding == nil {
						return
					}
					member, isMember := node.Index.(*ast.Identifier)
					if !isMember {
						return
					}
					binding.Used = true
					internal := l.resolveMember(pkg, file, binding, member.Value, node)
					replacement := &ast.Identifier{Token: base.Token, Value: internal}
					replacement.Token.Literal = internal
					if coercion := binding.coerce[member.Value]; coercion != nil {
						if coercion.value != "" {
							slot.Set(reflect.ValueOf(ast.Expression(coerceCall("__abstract_"+coercion.value, base.Token, replacement))))
							return
						}
						l.reportAt(CodeSignatureMismatch, file.Path, node, "%s.%s uses abstract types in its signature and must be called directly", binding.Alias, member.Value)
					}
					slot.Set(reflect.ValueOf(ast.Expression(replacement)))
				}
			},
			ident: func(id *ast.Identifier, label bool) {
				if label {
					return
				}
				if library, member, qualified := splitDotted(id.Value); qualified {
					if binding := pkg.Imports[library]; binding != nil {
						binding.Used = true
						id.Value = l.resolveMember(pkg, file, binding, member, id)
					}
					return
				}
				if _, isAlias := pkg.Imports[id.Value]; isAlias {
					d := l.reportAt(CodeImportAlias, file.Path, id, "%s is an imported package, not a value; use %s.member", id.Value, id.Value)
					d.AddNote("import aliases are package-scoped names and cannot be redeclared or passed around")
					return
				}
				if binding := pkg.Selective[id.Value]; binding != nil {
					binding.Used = true
				}
				if internal, renamed := pkg.Renames[id.Value]; renamed {
					id.Value = internal
				}
			},
			tag: func(name *string) {
				if library, member, qualified := splitDotted(*name); qualified {
					if binding := pkg.Imports[library]; binding != nil {
						binding.Used = true
						*name = l.resolveMember(pkg, file, binding, member, nil)
					}
					return
				}
				if binding := pkg.Selective[*name]; binding != nil {
					binding.Used = true
				}
				if internal, renamed := pkg.Renames[*name]; renamed {
					*name = internal
				}
			},
		}
		visitor.walk(reflect.ValueOf(file.Root), false)
	}
	for _, alias := range sortedAliases(pkg.Imports) {
		binding := pkg.Imports[alias]
		if !binding.Used && !(l.session && pkg.IsRoot) {
			d := l.reportAt(CodeImportAlias, binding.File, binding.Statement, "import %q is unused", binding.Path)
			d.AddHelp("remove the import or use one of its members")
		}
		l.collectObligations(pkg, binding)
	}
	// Every token records its package and file: position-keyed resolution
	// records stay distinct across packages, the checker reads the owning
	// package back for opacity, and diagnostics name the file (section 7).
	for _, file := range pkg.Files {
		stampSemanticContext(reflect.ValueOf(file.Root), pkg.Path+"#"+file.Path)
	}
	for _, file := range pkg.Files {
		for _, stmt := range file.Root.Statements {
			switch stmt.(type) {
			case *ast.PackageStatement, *ast.ImportStatement:
				continue
			}
			// Signature shapes (`Name: type = { Key: type, ... }`) are
			// compile-time interfaces, never runtime records.
			if isSignatureShape(stmt) {
				continue
			}
			pkg.Statements = append(pkg.Statements, stmt)
		}
	}
}

// isSignatureShape reports whether a declaration is a record shape with an
// abstract type member, i.e. a named import signature (section 6.3).
func isSignatureShape(stmt ast.Statement) bool {
	adt, isADT := stmt.(*ast.ADTType)
	if !isADT || len(adt.Variants) != 1 {
		return false
	}
	shape, isShape := adt.Variants[0].Literal.(*ast.RecordLiteral)
	if !isShape {
		return false
	}
	for _, field := range shape.FieldOrder {
		if ident, isIdent := field.Value.(*ast.Identifier); isIdent && ident.Value == "type" {
			return true
		}
	}
	return false
}

// stampSemanticContext sets every token's SemanticContext so position-keyed
// resolution records never collide across packages (the stdlib stamps
// "std" the same way).
func stampSemanticContext(value reflect.Value, context string) {
	switch value.Kind() {
	case reflect.Ptr, reflect.Interface:
		if value.IsNil() {
			return
		}
		stampSemanticContext(value.Elem(), context)
	case reflect.Struct:
		if value.Type() == reflect.TypeOf(token.Token{}) {
			if value.CanSet() {
				value.FieldByName("SemanticContext").SetString(context)
			}
			return
		}
		for i := 0; i < value.NumField(); i++ {
			field := value.Field(i)
			if field.CanSet() || field.Kind() == reflect.Ptr || field.Kind() == reflect.Interface || field.Kind() == reflect.Slice {
				stampSemanticContext(field, context)
			}
		}
	case reflect.Slice:
		for i := 0; i < value.Len(); i++ {
			stampSemanticContext(value.Index(i), context)
		}
	case reflect.Map:
		for _, key := range value.MapKeys() {
			stampSemanticContext(value.MapIndex(key), context)
		}
	}
}

func splitDotted(name string) (library, member string, ok bool) {
	index := strings.IndexByte(name, '.')
	if index <= 0 || index == len(name)-1 {
		return "", "", false
	}
	return name[:index], name[index+1:], true
}

// resolveMember decides `alias.member` with modules.Lookup and returns the
// internal name to substitute. On failure it reports and still returns the
// would-be internal name so the failure does not cascade.
func (l *moduleLoader) resolveMember(pkg *loadedPackage, file *packageFile, binding *importBinding, member string, node ast.Node) string {
	target := l.packages[binding.Path]
	internal := modules.Mangle(binding.Path, member)
	if target == nil {
		return internal
	}
	found, outcome := modules.Lookup(target.Exports, binding.sig, member)
	switch outcome {
	case modules.Resolved:
		_ = found
		if fresh, abstract := binding.abstractNames[member]; abstract {
			// A sealed `Name: type` member is a fresh abstract type.
			return fresh
		}
		return internal
	case modules.NotInSignature:
		d := l.reportAt(CodeSignatureMismatch, fileName(file, binding), node, "%s.%s is outside the signature %s was sealed with", binding.Alias, member, binding.Alias)
		d.AddNote("a sealed import exposes exactly the members its signature lists")
	case modules.NoSuchMember:
		l.reportAt(CodeNoSuchMember, fileName(file, binding), node, "package %s has no member %s", binding.Template, member)
	case modules.NotExported:
		d := l.reportAt(CodeMemberNotExported, fileName(file, binding), node, "%s is not exported by package %s", member, binding.Template)
		d.AddHelp(fmt.Sprintf("mark the declaration pub in package %s to export it", binding.Template))
	}
	return internal
}

func fileName(file *packageFile, binding *importBinding) string {
	if file != nil {
		return file.Path
	}
	return binding.File
}

// coerceCall wraps expr in a compiler-only coercion builtin between a fresh
// abstract type and its underlying type (typechecker/modules.go).
func coerceCall(builtin string, tok token.Token, expr ast.Expression) ast.Expression {
	callee := &ast.Identifier{Token: tok, Value: builtin}
	callee.Token.Literal = builtin
	return &ast.InvocationExpression{Token: tok, Function: callee, Arguments: []ast.Expression{expr}}
}

// rewriteSealedCall rewrites `alias.member(args)` through a sealed import
// whose member signature mentions abstract type members: arguments in
// abstract positions are unwrapped to the underlying type and an abstract
// result is wrapped, so the fresh type is introduced and eliminated only at
// the sealed boundary (section 6.3).
func (l *moduleLoader) rewriteSealedCall(pkg *loadedPackage, file *packageFile, call *ast.InvocationExpression) ast.Expression {
	access, isAccess := call.Function.(*ast.IndexExpression)
	if !isAccess || !access.Dot {
		return nil
	}
	base, isIdent := access.Left.(*ast.Identifier)
	member, isMember := access.Index.(*ast.Identifier)
	if !isIdent || !isMember {
		return nil
	}
	binding := pkg.Imports[base.Value]
	if binding == nil || binding.coerce == nil {
		return nil
	}
	coercion := binding.coerce[member.Value]
	if coercion == nil || coercion.value != "" {
		return nil
	}
	binding.Used = true
	internal := l.resolveMember(pkg, file, binding, member.Value, access)
	callee := &ast.Identifier{Token: base.Token, Value: internal}
	callee.Token.Literal = internal
	rewritten := &ast.InvocationExpression{BaseNode: call.BaseNode, Token: call.Token, Function: callee}
	for i, arg := range call.Arguments {
		if i < len(coercion.params) && coercion.params[i] != "" {
			arg = coerceCall("__concrete_"+coercion.params[i], base.Token, arg)
		}
		rewritten.Arguments = append(rewritten.Arguments, arg)
	}
	if coercion.result != "" {
		return coerceCall("__abstract_"+coercion.result, base.Token, rewritten)
	}
	return rewritten
}

// prepareSignature resolves a sealed import's signature shape (inline, a
// shape declared in this package, or an exported shape of an imported
// package), validates membership and kind against the package's export
// table, marks abstract type members opaque for this package, and
// substitutes type members in place before renaming (section 6.3).
func (l *moduleLoader) prepareSignature(pkg *loadedPackage, binding *importBinding) {
	if binding.Signature == nil {
		return
	}
	target := l.packages[binding.Path]
	if target == nil {
		return
	}
	shape := l.signatureShape(pkg, binding)
	if shape == nil {
		return
	}
	binding.shape = shape
	binding.sigKinds = map[string]modules.MemberKind{}
	binding.abstractNames = map[string]string{}
	binding.coerce = map[string]*memberCoercion{}
	typeMembers := map[string]string{}
	usingKey := pkg.Path
	for _, field := range shape.FieldOrder {
		binding.sigOrder = append(binding.sigOrder, field.Name)
		if ident, isIdent := field.Value.(*ast.Identifier); isIdent && ident.Value == "type" {
			binding.sigKinds[field.Name] = modules.KindType
			internal := modules.Mangle(binding.Path, field.Name)
			typeMembers[field.Name] = internal
			if field.Manifest != nil {
				// `Key: type = T`: shared, transparent; T must be the
				// package's definition (checked by the type checker).
				l.obligations = append(l.obligations, typechecker.SignatureObligation{
					Internal: internal, Member: binding.Alias + "." + field.Name, Type: field.Manifest, Node: binding.Statement, TypeMember: true,
				})
				continue
			}
			// An abstract member is a fresh nominal type for this binding;
			// its definition is unreachable here (sealed opacity).
			fresh := modules.Mangle(pkg.Path+"@"+binding.Alias, field.Name)
			binding.abstractNames[field.Name] = fresh
			l.abstract[fresh] = internal
			if l.sealed[fresh] == nil {
				l.sealed[fresh] = map[string]bool{}
			}
			l.sealed[fresh][usingKey] = true
			continue
		}
		binding.sigKinds[field.Name] = modules.KindValue
	}
	// Value members mentioning abstract members need boundary coercions.
	for _, field := range shape.FieldOrder {
		if binding.sigKinds[field.Name] != modules.KindValue {
			continue
		}
		abstractOf := func(expr ast.Expression) string {
			if ident, isIdent := expr.(*ast.Identifier); isIdent {
				return binding.abstractNames[ident.Value]
			}
			return ""
		}
		switch t := field.Value.(type) {
		case *ast.FunctionTypeExpression:
			coercion := &memberCoercion{result: abstractOf(t.Return)}
			mentions := coercion.result != ""
			for _, param := range t.Parameters {
				fresh := abstractOf(param)
				mentions = mentions || fresh != ""
				coercion.params = append(coercion.params, fresh)
			}
			if mentions {
				binding.coerce[field.Name] = coercion
			}
		default:
			if fresh := abstractOf(field.Value); fresh != "" {
				binding.coerce[field.Name] = &memberCoercion{value: fresh}
			}
		}
	}
	binding.sig = &modules.Signature{Members: binding.sigKinds}
	problems := modules.Conforms(target.Exports, *binding.sig, binding.sigOrder)
	for _, problem := range problems {
		switch problem.Outcome {
		case modules.NoSuchMember:
			l.reportAt(CodeSignatureMismatch, binding.File, binding.Statement, "signature member %s: package %s has no such declaration", problem.Name, binding.Path)
		case modules.NotExported:
			l.reportAt(CodeSignatureMismatch, binding.File, binding.Statement, "signature member %s is not exported by package %s", problem.Name, binding.Path)
		default:
			l.reportAt(CodeSignatureMismatch, binding.File, binding.Statement, "signature member %s must be a %s, but package %s declares a %s", problem.Name, problem.Want, binding.Path, problem.Got)
		}
	}
	if len(problems) != 0 {
		binding.shape = nil
		return
	}
	// Sibling type members denote the package's types. Substituted names
	// are internal (or prelude) names, which the renaming walk leaves alone.
	for _, field := range shape.FieldOrder {
		if binding.sigKinds[field.Name] != modules.KindValue {
			continue
		}
		value := field.Value
		(&syntaxVisitor{ident: func(id *ast.Identifier, label bool) {
			if label {
				return
			}
			if internal, isTypeMember := typeMembers[id.Value]; isTypeMember {
				id.Value = internal
			}
		}}).walk(reflect.ValueOf(&value).Elem(), false)
	}
}

// signatureShape resolves the signature expression to a record shape:
// inline `{ ... }`, `Name` declared in this package, or `alias.Name`
// exported by an imported package.
func (l *moduleLoader) signatureShape(pkg *loadedPackage, binding *importBinding) *ast.RecordLiteral {
	switch sig := binding.Signature.(type) {
	case *ast.RecordLiteral:
		if sig.TypeName == nil {
			return sig
		}
	case *ast.Identifier:
		if library, member, qualified := splitDotted(sig.Value); qualified {
			other := pkg.Imports[library]
			if other == nil {
				break
			}
			other.Used = true
			source := l.packages[other.Path]
			if source == nil {
				break
			}
			if _, outcome := modules.Lookup(source.Exports, other.sig, member); outcome != modules.Resolved {
				l.reportAt(CodeSignatureMismatch, binding.File, binding.Statement, "signature %s is not an exported shape of package %s", sig.Value, other.Path)
				return nil
			}
			if shape := declaredShape(source, modules.Mangle(other.Path, member)); shape != nil {
				return shape
			}
			break
		}
		if shape := declaredShape(pkg, sig.Value); shape != nil {
			return shape
		}
	}
	l.reportAt(CodeSignatureMismatch, binding.File, binding.Statement, "an import signature must be a record shape { member: Type, Name: type, ... }, inline or declared as Name: type = { ... }")
	return nil
}

// declaredShape finds `name: type = { ... }` in a package's files. Imported
// packages have already been renamed, so name is their internal name.
func declaredShape(pkg *loadedPackage, name string) *ast.RecordLiteral {
	for _, file := range pkg.Files {
		for _, stmt := range file.Root.Statements {
			adt, isADT := stmt.(*ast.ADTType)
			if !isADT || adt.Name == nil || adt.Name.Value != name || len(adt.Variants) != 1 {
				continue
			}
			if shape, isShape := adt.Variants[0].Literal.(*ast.RecordLiteral); isShape && shape.TypeName == nil {
				return shape
			}
		}
	}
	return nil
}

// collectObligations records, after renaming, the member types the checker
// must verify for a sealed import, and the contract for offline checks.
func (l *moduleLoader) collectObligations(pkg *loadedPackage, binding *importBinding) {
	if binding.shape == nil {
		return
	}
	sealed := SealedImport{Importer: pkg.Path, Alias: binding.Alias, Package: binding.Template}
	for _, field := range binding.shape.FieldOrder {
		member := SealedMember{Name: field.Name, Kind: "type"}
		if binding.sigKinds[field.Name] == modules.KindValue {
			member.Kind = "value"
			if canonical, err := canonicalTypeExpression(field.Value); err == nil {
				member.Type = dependencySpelling(canonical, binding.Path)
			}
		}
		sealed.Members = append(sealed.Members, member)
	}
	l.sealedList = append(l.sealedList, sealed)
	for _, field := range binding.shape.FieldOrder {
		if binding.sigKinds[field.Name] != modules.KindValue {
			continue
		}
		internal := modules.Mangle(binding.Path, field.Name)
		l.obligations = append(l.obligations, typechecker.SignatureObligation{
			Internal: internal,
			Member:   binding.Alias + "." + field.Name,
			Type:     field.Value,
			Node:     binding.Statement,
		})
	}
}

// firstIdentifier returns the leftmost identifier of a type expression.
func firstIdentifier(expr ast.Expression) *ast.Identifier {
	switch e := expr.(type) {
	case *ast.Identifier:
		return e
	case *ast.IndexExpression:
		return firstIdentifier(e.Left)
	case *ast.PrefixExpression:
		return firstIdentifier(e.Right)
	}
	return nil
}

// merge assembles the flat program: bootstrap imports first, dependencies
// in compile order, the root package last.
func (l *moduleLoader) merge(order []string, root *loadedPackage) *SyntaxTree {
	program := &ast.Program{}
	bootstrap := map[string]*ast.ImportStatement{}
	for _, path := range order {
		for name, imp := range l.packages[path].Bootstrap {
			if _, seen := bootstrap[name]; !seen {
				bootstrap[name] = imp
			}
		}
	}
	for _, name := range []string{"std", "testing"} {
		if imp, present := bootstrap[name]; present {
			program.Statements = append(program.Statements, imp)
		}
	}
	// The root package's clause is not forwarded: root declarations keep
	// their source names in the emitted C (oak_<name>) whatever the package
	// is called, so single-file programs, `oak build` roots, and the test
	// runner's harness agree on one naming rule.
	for _, path := range order {
		if path == root.Path {
			continue
		}
		program.Statements = append(program.Statements, l.packages[path].Statements...)
	}
	program.Statements = append(program.Statements, root.Statements...)
	public := &ast.Program{Statements: append([]ast.Statement(nil), root.Statements...)}
	libraryNames := map[string]string{}
	for _, path := range order {
		pkg := l.packages[path]
		if pkg.Dir != "<stdlib>" {
			continue
		}
		for name, member := range pkg.Exports {
			if member.Exported {
				libraryNames[name] = modules.Mangle(path, name)
			}
		}
	}
	info := &ModuleInfo{Public: public, OpaqueTypes: l.opaque, SealedOpaque: l.sealed, Abstract: l.abstract, Obligations: l.obligations, Parameters: l.parameters, Packages: order, PreludeCore: l.preludeCore, LibraryNames: libraryNames, Sealed: l.sealedList}
	return &SyntaxTree{
		Source:  SourceText{Path: root.Dir},
		File:    root.Files[0].File,
		Root:    program,
		Modules: info,
	}
}

// syntaxVisitor walks a syntax tree reflectively. expr is called on every
// settable expression slot (pre-order) and may replace its content; ident
// is called on every identifier with label=true for member labels
// (`.field`, variant and method names) that name nothing in scope.
type syntaxVisitor struct {
	expr  func(slot reflect.Value)
	ident func(id *ast.Identifier, label bool)
	// tag is called on every field tag namespace (a string, not an
	// identifier node): package-scoped tag schemas rename through it.
	tag func(name *string)
}

var (
	tokenType           = reflect.TypeOf(token.Token{})
	identifierType      = reflect.TypeOf(&ast.Identifier{})
	indexExpressionType = reflect.TypeOf(ast.IndexExpression{})
	variantExprType     = reflect.TypeOf(ast.VariantExpression{})
	variantPatternType  = reflect.TypeOf(ast.VariantPattern{})
	adtVariantType      = reflect.TypeOf(ast.ADTVariant{})
	interfaceMethodType = reflect.TypeOf(ast.InterfaceMethod{})
	functionStmtType    = reflect.TypeOf(ast.FunctionStatement{})
	fieldAccessorType   = reflect.TypeOf(ast.FieldAccessorExpression{})
	importStmtType      = reflect.TypeOf(ast.ImportStatement{})
	fieldTagType        = reflect.TypeOf(ast.FieldTag{})
	packageStmtType     = reflect.TypeOf(ast.PackageStatement{})
)

func (sv *syntaxVisitor) walk(v reflect.Value, label bool) {
	switch v.Kind() {
	case reflect.Interface:
		if v.IsNil() {
			return
		}
		if _, isExpr := v.Interface().(ast.Expression); isExpr && v.CanSet() && sv.expr != nil {
			sv.expr(v)
		}
		sv.walk(v.Elem(), label)
	case reflect.Pointer:
		if v.IsNil() {
			return
		}
		if v.Type() == identifierType {
			if sv.ident != nil {
				sv.ident(v.Interface().(*ast.Identifier), label)
			}
			return
		}
		sv.walk(v.Elem(), label)
	case reflect.Struct:
		t := v.Type()
		if t == tokenType || t == packageStmtType {
			return
		}
		if t == fieldTagType && sv.tag != nil && v.CanAddr() {
			sv.tag(v.FieldByName("Name").Addr().Interface().(*string))
		}
		for i := 0; i < v.NumField(); i++ {
			field := t.Field(i)
			if !field.IsExported() {
				continue
			}
			if t == importStmtType && field.Name != "Signature" {
				continue
			}
			sv.walk(v.Field(i), label || isLabelSlot(t, field.Name, v))
		}
	case reflect.Slice:
		for i := 0; i < v.Len(); i++ {
			sv.walk(v.Index(i), label)
		}
	case reflect.Map:
		keys := v.MapKeys()
		sort.Slice(keys, func(i, j int) bool { return keys[i].String() < keys[j].String() })
		for _, key := range keys {
			value := reflect.New(v.Type().Elem()).Elem()
			value.Set(v.MapIndex(key))
			sv.walk(value, label)
			v.SetMapIndex(key, value)
		}
	}
}

// isLabelSlot names the identifier slots that are member labels rather than
// references: field/variant/member selectors, variant declarations, method
// names in interfaces and receiver functions.
func isLabelSlot(t reflect.Type, field string, v reflect.Value) bool {
	switch t {
	case indexExpressionType:
		return field == "Index" && v.FieldByName("Dot").Bool()
	case variantExprType, variantPatternType:
		return field == "Variant"
	case adtVariantType, interfaceMethodType:
		return field == "Name"
	case fieldAccessorType:
		return field == "Field"
	case functionStmtType:
		return field == "Name" && !v.FieldByName("Receiver").IsNil()
	}
	return false
}

// instancePath is the identity of a generic package instantiation: the
// template path, '@', and the resolved argument atoms joined by ','. Import
// paths contain no '@' and atoms no ',', so the identity decodes uniquely
// and mangles injectively (section 6.7).
func (l *moduleLoader) instancePath(pkg *loadedPackage, template string, arguments []ast.Expression, file *packageFile, node ast.Node) string {
	atoms := make([]string, 0, len(arguments))
	for _, argument := range arguments {
		atom, ok := l.argumentAtom(pkg, argument)
		if !ok {
			l.reportAt(CodeGenericPackageArgument, file.Path, node, "instantiation argument %s is not a primitive type, an integer constant, a declared type, or an imported type", argument.String())
			atom = "?"
		}
		atoms = append(atoms, atom)
	}
	return template + "@" + strings.Join(atoms, ",")
}

// argumentAtom resolves an instantiation argument as the importer would
// resolve it: primitives and constants stand for themselves, the importer's
// own types and imported types become their internal names.
func (l *moduleLoader) argumentAtom(pkg *loadedPackage, argument ast.Expression) (string, bool) {
	switch a := argument.(type) {
	case *ast.IntegerLiteral:
		return fmt.Sprintf("%d", a.Value), true
	case *ast.Identifier:
		if primitiveTypeNames[a.Value] {
			return a.Value, true
		}
		if library, member, qualified := splitDotted(a.Value); qualified {
			binding := pkg.Imports[library]
			if binding == nil {
				return "", false
			}
			binding.Used = true
			if bootstrapImports[binding.Path] {
				return member, true
			}
			return modules.Mangle(binding.Path, member), true
		}
		if member, declared := pkg.Exports[a.Value]; declared && member.Kind == modules.KindType {
			if pkg.IsRoot {
				return a.Value, true
			}
			return modules.Mangle(pkg.Path, a.Value), true
		}
		if internal, renamed := pkg.Renames[a.Value]; renamed {
			return internal, true
		}
	case *ast.IndexExpression:
		if a.Dot {
			return "", false
		}
		left, ok := l.argumentAtom(pkg, a.Left)
		if !ok {
			return "", false
		}
		right, ok := l.argumentAtom(pkg, a.Index)
		if !ok {
			return "", false
		}
		return left + "_" + right, true
	}
	return "", false
}

var primitiveTypeNames = map[string]bool{
	"i8": true, "i16": true, "i32": true, "i64": true,
	"u8": true, "u16": true, "u32": true, "u64": true,
	"int": true, "uint": true, "ptr": true, "uptr": true,
	"byte": true, "rune": true, "Bool": true, "string": true,
}

// instantiate substitutes a generic package's parameters with the import's
// arguments (or checks that a non-generic package received none).
func (l *moduleLoader) instantiate(pkg *loadedPackage, arguments []ast.Expression, importer *importBinding) bool {
	var params []*ast.TypeParameter
	var clause *ast.PackageStatement
	for _, file := range pkg.Files {
		if len(file.Root.Statements) == 0 {
			continue
		}
		if c, ok := file.Root.Statements[0].(*ast.PackageStatement); ok && len(c.TypeParams) != 0 {
			if clause != nil && len(c.TypeParams) != len(clause.TypeParams) {
				l.reportAt(CodeGenericPackageArity, file.Path, c, "package parameter lists disagree between files")
				return false
			}
			clause, params = c, c.TypeParams
		}
	}
	if len(params) == 0 && len(arguments) == 0 {
		return true
	}
	if importer == nil {
		l.reportAt(CodeGenericPackageArity, pkg.Files[0].Path, clause, "generic package %s cannot be the root of a build", pkg.TemplatePath)
		return false
	}
	if len(params) != len(arguments) {
		l.reportAt(CodeGenericPackageArity, importer.File, importer.Statement, "package %s takes %d parameters but the import supplies %d arguments", pkg.TemplatePath, len(params), len(arguments))
		return false
	}
	bindings := map[string]ast.Expression{}
	for i, param := range params {
		if param.Name == nil {
			return false
		}
		bindings[param.Name.Value] = arguments[i]
	}
	// Arguments are spelled in the importer; resolve them to what the
	// importer's own elaboration would produce so the instance and its
	// importer agree on every name.
	resolved := map[string]ast.Expression{}
	for name, argument := range bindings {
		resolved[name] = l.resolvedArgument(importer, argument)
	}
	// Declared parameter contracts are checked at the import site by the
	// type checker, against the resolved argument (section 6.7).
	for _, param := range params {
		if param.Constraint == nil {
			continue
		}
		// `N: u32` is a const parameter: its argument must be an integer
		// constant, which the substitution already requires literally.
		if kind, isIdent := param.Constraint.(*ast.Identifier); isIdent && primitiveTypeNames[kind.Value] {
			if _, isLiteral := resolved[param.Name.Value].(*ast.IntegerLiteral); !isLiteral {
				l.reportAt(CodeGenericPackageArgument, importer.File, importer.Statement, "parameter %s: %s takes an integer constant, got %s", param.Name.Value, kind.Value, resolved[param.Name.Value].String())
				return false
			}
			continue
		}
		constraint := cloneSyntax(reflect.ValueOf(param.Constraint)).Interface().(ast.Expression)
		pkg.pendingParams = append(pkg.pendingParams, typechecker.ParameterObligation{
			Package:    pkg.TemplatePath,
			Param:      param.Name.Value,
			Constraint: constraint,
			Argument:   resolved[param.Name.Value],
			Node:       importer.Statement,
		})
	}
	for _, file := range pkg.Files {
		for _, stmt := range file.Root.Statements {
			if c, ok := stmt.(*ast.PackageStatement); ok {
				c.TypeParams = nil
			}
		}
		(&syntaxVisitor{
			expr: func(slot reflect.Value) {
				if ident, isIdent := slot.Interface().(*ast.Identifier); isIdent {
					if argument, bound := resolved[ident.Value]; bound {
						clone := cloneSyntax(reflect.ValueOf(argument)).Interface().(ast.Expression)
						slot.Set(reflect.ValueOf(clone))
					}
				}
			},
			ident: func(id *ast.Identifier, label bool) {
				if label {
					return
				}
				if argument, bound := resolved[id.Value]; bound {
					if argIdent, isIdent := argument.(*ast.Identifier); isIdent {
						id.Value = argIdent.Value
					} else if lit, isLit := argument.(*ast.IntegerLiteral); isLit {
						id.Value = fmt.Sprintf("%d", lit.Value)
					} else {
						l.reportAt(CodeGenericPackageArgument, file.Path, id, "parameter %s is used where only a type name can appear, but the argument %s is not a name", id.Value, argument.String())
					}
				}
			},
		}).walk(reflect.ValueOf(file.Root), false)
	}
	return true
}

// resolvedArgument rewrites an instantiation argument into the importer's
// resolved spelling (internal names for its own and imported types).
func (l *moduleLoader) resolvedArgument(importer *importBinding, argument ast.Expression) ast.Expression {
	pkg := l.packageOfBinding(importer)
	if pkg == nil {
		return argument
	}
	clone := cloneSyntax(reflect.ValueOf(argument)).Interface().(ast.Expression)
	(&syntaxVisitor{ident: func(id *ast.Identifier, label bool) {
		if label {
			return
		}
		if atom, ok := l.argumentAtom(pkg, id); ok {
			id.Value = atom
		}
	}}).walk(reflect.ValueOf(&clone).Elem(), false)
	return clone
}

func (l *moduleLoader) packageOfBinding(binding *importBinding) *loadedPackage {
	for _, pkg := range l.packages {
		for _, candidate := range pkg.Imports {
			if candidate == binding {
				return pkg
			}
		}
	}
	return nil
}

// dependencySpelling rewrites canonical type text containing internal names
// of package `path` into the spelling that package's own API snapshot uses:
// its declarations by bare name.
func dependencySpelling(canonical, path string) string {
	text := modules.DemangleText(canonical)
	return strings.ReplaceAll(text, path+".", "")
}
