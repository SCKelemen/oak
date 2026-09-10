package modules

import (
	"math/rand"
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/packageapi"
)

// Mangling laws (docs/spec/83-modules.md section 7, Oak.Modules.Mangle).

func TestEscapeNeverProducesAdjacentUnderscores(t *testing.T) {
	inputs := []string{"", "_", "__", "a__b", "___", "x_", "_x", "a/b.c-d_e", "ünïcödé", "😀", "a b"}
	for _, input := range inputs {
		escaped := Escape(input)
		if strings.Contains(escaped, "__") {
			t.Fatalf("Escape(%q) = %q contains %q", input, escaped, "__")
		}
		for _, r := range escaped {
			if !isASCIIAlnum(r) && r != '_' {
				t.Fatalf("Escape(%q) = %q leaves the identifier alphabet", input, escaped)
			}
		}
	}
}

func TestUnescapeEscapeRoundTrip(t *testing.T) {
	inputs := []string{"", "_", "__", "a__b", "ring_pop", "example.com/net/http", "a-b", "ünïcödé", "😀_x", "_x000041"}
	for _, input := range inputs {
		got, ok := Unescape(Escape(input))
		if !ok || got != input {
			t.Fatalf("Unescape(Escape(%q)) = (%q, %v)", input, got, ok)
		}
	}
}

func TestUnescapeRejectsNonImages(t *testing.T) {
	for _, bad := range []string{"_", "a_", "_q", "_x12", "_x12345g", "a.b", "a b", "__"} {
		if got, ok := Unescape(bad); ok {
			t.Fatalf("Unescape(%q) accepted as %q", bad, got)
		}
	}
}

func TestMangleDemangleRoundTrip(t *testing.T) {
	cases := [][2]string{
		{"example.com/net", "listen"},
		{"strings", "trim_left"},
		{"a_b", "c"}, {"a", "b_c"}, // the classic ambiguity, resolved by escaping
		{"x", "_leading"}, {"x_", "y"},
	}
	seen := map[string][2]string{}
	for _, c := range cases {
		internal := Mangle(c[0], c[1])
		if prev, dup := seen[internal]; dup {
			t.Fatalf("Mangle collision: %v and %v both map to %q", prev, c, internal)
		}
		seen[internal] = c
		path, name, ok := Demangle(internal)
		if !ok || path != c[0] || name != c[1] {
			t.Fatalf("Demangle(Mangle(%q, %q)) = (%q, %q, %v)", c[0], c[1], path, name, ok)
		}
		if !Reserved(internal) {
			t.Fatalf("mangled name %q must be reserved for user code", internal)
		}
	}
}

// Differential witness: random paths/names never collide and always
// round-trip, so the reserved-sequence rule makes capture impossible.
func TestMangleRandomizedInjective(t *testing.T) {
	rng := rand.New(rand.NewSource(7))
	alphabet := []rune("abcXYZ019_/.-é")
	random := func() string {
		n := rng.Intn(6)
		var b strings.Builder
		for i := 0; i < n; i++ {
			b.WriteRune(alphabet[rng.Intn(len(alphabet))])
		}
		return b.String()
	}
	seen := map[string][2]string{}
	for i := 0; i < 20000; i++ {
		path, name := random(), random()
		internal := Mangle(path, name)
		if prev, dup := seen[internal]; dup && (prev[0] != path || prev[1] != name) {
			t.Fatalf("collision: %v vs %v -> %q", prev, [2]string{path, name}, internal)
		}
		seen[internal] = [2]string{path, name}
		p, n, ok := Demangle(internal)
		if !ok || p != path || n != name {
			t.Fatalf("round trip failed for (%q, %q): (%q, %q, %v)", path, name, p, n, ok)
		}
	}
}

func TestDemangleText(t *testing.T) {
	text := "undefined variable: example_dcom_snet__listen (in oak_x__y__z)"
	got := DemangleText(text)
	want := "undefined variable: example.com/net.listen (in oak_x__y__z)"
	if got != want {
		t.Fatalf("DemangleText = %q, want %q", got, want)
	}
}

// Dependency order (section 5, Oak.Modules.Order).

func TestOrderPlacesImportsFirst(t *testing.T) {
	imports := map[string][]string{
		"main":            {"example.com/m/b", "example.com/m/a"},
		"example.com/m/b": {"example.com/m/a", "example.com/m/c"},
		"example.com/m/a": {"example.com/m/c"},
		"example.com/m/c": nil,
	}
	nodes := []string{"main", "example.com/m/a", "example.com/m/b", "example.com/m/c"}
	order, stuck := Order(nodes, imports)
	if stuck != nil {
		t.Fatalf("unexpected stuck set %v", stuck)
	}
	position := map[string]int{}
	for i, node := range order {
		position[node] = i
	}
	if len(position) != len(nodes) {
		t.Fatalf("order %v is not a permutation of %v", order, nodes)
	}
	for node, deps := range imports {
		for _, dep := range deps {
			if position[dep] >= position[node] {
				t.Fatalf("%s placed at %d before its import %s at %d", node, position[node], dep, position[dep])
			}
		}
	}
	// Determinism: same input, same order.
	again, _ := Order(nodes, imports)
	if !reflect.DeepEqual(order, again) {
		t.Fatalf("order is not deterministic: %v vs %v", order, again)
	}
}

func TestOrderReportsCycle(t *testing.T) {
	imports := map[string][]string{
		"main":               {"example.com/m/a"},
		"example.com/m/a":    {"example.com/m/b"},
		"example.com/m/b":    {"example.com/m/a"},
		"example.com/m/leaf": nil,
	}
	nodes := []string{"main", "example.com/m/a", "example.com/m/b", "example.com/m/leaf"}
	order, stuck := Order(nodes, imports)
	if !reflect.DeepEqual(order, []string{"example.com/m/leaf"}) {
		t.Fatalf("order = %v", order)
	}
	if !reflect.DeepEqual(stuck, []string{"example.com/m/a", "example.com/m/b", "main"}) {
		t.Fatalf("stuck = %v", stuck)
	}
	// Every stuck package imports a stuck package.
	inStuck := map[string]bool{}
	for _, s := range stuck {
		inStuck[s] = true
	}
	for _, s := range stuck {
		found := false
		for _, imported := range imports[s] {
			found = found || inStuck[imported]
		}
		if !found {
			t.Fatalf("stuck package %s has no stuck import", s)
		}
	}
	cycle := ImportCycle(stuck, imports)
	if !reflect.DeepEqual(cycle, []string{"example.com/m/a", "example.com/m/b"}) {
		t.Fatalf("cycle = %v", cycle)
	}
}

// Import paths (section 3).

func TestValidateImportPath(t *testing.T) {
	good := []string{"std", "testing", "example.com/net", "example.com/net/http2", "a-b.c/d_e", "x/y/z"}
	for _, p := range good {
		if err := ValidateImportPath(p); err != nil {
			t.Fatalf("ValidateImportPath(%q) = %v", p, err)
		}
	}
	bad := []string{"", "/a", "a/", "a//b", "a/../b", "./a", "..", "A", "a b", "a/_b", "a/-b", "a/b__c", "ä", "a\\b", strings.Repeat("a", 257)}
	for _, p := range bad {
		if err := ValidateImportPath(p); err == nil {
			t.Fatalf("ValidateImportPath(%q) accepted", p)
		}
	}
	if !IsStandardLibraryPath("std") || !IsStandardLibraryPath("encoding/utf8") || IsStandardLibraryPath("example.com/x") {
		t.Fatal("standard library path rule broken")
	}
	if LastSegment("example.com/net/http") != "http" || LastSegment("std") != "std" {
		t.Fatal("LastSegment broken")
	}
	if !ValidPackageName("http2") || !ValidPackageName("my_pkg") || ValidPackageName("Http") || ValidPackageName("a__b") || ValidPackageName("_x") || ValidPackageName("") {
		t.Fatal("ValidPackageName broken")
	}
	if !HasPathPrefix("a/b/c", "a/b") || HasPathPrefix("a/bc", "a/b") || !HasPathPrefix("a", "a") {
		t.Fatal("HasPathPrefix broken")
	}
}

// Manifests (section 4).

func TestParseManifest(t *testing.T) {
	manifest, err := ParseManifest(`
// module manifest
module example.com/hello
oak 0.1.0

require example.com/dep 1.2.0
require example.com/other 0.3.1 // trailing comment
replace example.com/dep => ../dep
profile strict
steady example.com/hello serve
steady example.com/hello/net poll
`)
	if err != nil {
		t.Fatal(err)
	}
	if manifest.Path != "example.com/hello" || manifest.Oak != "0.1.0" || manifest.Profile != "strict" {
		t.Fatalf("manifest = %+v", manifest)
	}
	if plain, err := ParseManifest("module example.com/x\n"); err != nil || plain.Profile != "" {
		t.Fatalf("manifest without profile = %+v, %v", plain, err)
	}
	if len(manifest.Requires) != 2 || manifest.Requires[0].Path != "example.com/dep" || manifest.Requires[0].Version != (packageapi.Version{Major: 1, Minor: 2}) {
		t.Fatalf("requires = %+v", manifest.Requires)
	}
	if manifest.Replaces["example.com/dep"] != "../dep" {
		t.Fatalf("replaces = %v", manifest.Replaces)
	}
	if len(manifest.Steady) != 2 || manifest.Steady[0] != (SteadyEntry{Path: "example.com/hello", Name: "serve"}) || manifest.Steady[1].Name != "poll" {
		t.Fatalf("steady = %+v", manifest.Steady)
	}
	bad := map[string]string{
		"missing module":     "oak 0.1.0\n",
		"unknown directive":  "module example.com/x\nfetch y\n",
		"stdlib module path": "module strings\n",
		"bad version":        "module example.com/x\nrequire example.com/y 1.2\n",
		"duplicate module":   "module example.com/x\nmodule example.com/y\n",
		"duplicate require":  "module example.com/x\nrequire example.com/y 1.0.0\nrequire example.com/y 1.0.1\n",
		"replace unrequired": "module example.com/x\nreplace example.com/y => ../y\n",
		"replace shape":      "module example.com/x\nrequire example.com/y 1.0.0\nreplace example.com/y ../y\n",
		"require stdlib":     "module example.com/x\nrequire strings 1.0.0\n",
		"unknown profile":    "module example.com/x\nprofile lenient\n",
		"profile arity":      "module example.com/x\nprofile\n",
		"duplicate profile":  "module example.com/x\nprofile strict\nprofile default\n",
		"steady arity":       "module example.com/x\nsteady example.com/x\n",
		"steady bad path":    "module example.com/x\nsteady strings serve\n",
		"steady bad name":    "module example.com/x\nsteady example.com/x 9serve\n",
		"duplicate steady":   "module example.com/x\nsteady example.com/x serve\nsteady example.com/x serve\n",
	}
	for name, text := range bad {
		if _, err := ParseManifest(text); err == nil {
			t.Fatalf("%s: manifest accepted", name)
		}
	}
}

// Minimal version selection (section 4.2, Oak.Modules.Versions).

func TestSelectIsMaximumOfRequirements(t *testing.T) {
	v := func(a, b, c int) packageapi.Version { return packageapi.Version{Major: a, Minor: b, Patch: c} }
	selected := Select([]Requirement{
		{Path: "example.com/a", Version: v(1, 2, 0)}, {Path: "example.com/b", Version: v(0, 1, 0)},
		{Path: "example.com/a", Version: v(1, 10, 0)}, {Path: "example.com/a", Version: v(1, 9, 9)},
	})
	if selected["example.com/a"] != v(1, 10, 0) || selected["example.com/b"] != v(0, 1, 0) {
		t.Fatalf("selected = %v", selected)
	}
	if !reflect.DeepEqual(SelectedPaths(selected), []string{"example.com/a", "example.com/b"}) {
		t.Fatalf("paths = %v", SelectedPaths(selected))
	}
	if !Less(v(1, 9, 9), v(1, 10, 0)) || Less(v(2, 0, 0), v(1, 99, 99)) || Less(v(1, 0, 0), v(1, 0, 0)) {
		t.Fatal("Less broken")
	}
}

// Visibility and sealing (section 6, Oak.Modules.Visibility).

func TestLookupVisibilityAndSealing(t *testing.T) {
	exports := Exports{
		"pub_fn":  {Name: "pub_fn", Kind: KindValue, Exported: true},
		"priv_fn": {Name: "priv_fn", Kind: KindValue},
		"Key":     {Name: "Key", Kind: KindType, Exported: true, Opaque: true},
	}
	if _, outcome := Lookup(exports, nil, "pub_fn"); outcome != Resolved {
		t.Fatalf("pub_fn: %v", outcome)
	}
	if _, outcome := Lookup(exports, nil, "priv_fn"); outcome != NotExported {
		t.Fatalf("priv_fn: %v", outcome)
	}
	if _, outcome := Lookup(exports, nil, "nope"); outcome != NoSuchMember {
		t.Fatalf("nope: %v", outcome)
	}
	sig := &Signature{Members: map[string]MemberKind{"Key": KindType, "priv_fn": KindValue}}
	if _, outcome := Lookup(exports, sig, "pub_fn"); outcome != NotInSignature {
		t.Fatalf("sealed pub_fn: %v", outcome)
	}
	// Sealing never widens: a private member listed in the signature stays
	// unreachable.
	if _, outcome := Lookup(exports, sig, "priv_fn"); outcome != NotExported {
		t.Fatalf("sealed priv_fn: %v", outcome)
	}
	member, outcome := Lookup(exports, sig, "Key")
	if outcome != Resolved || !member.Opaque {
		t.Fatalf("sealed Key: %v %+v", outcome, member)
	}
	problems := Conforms(exports, Signature{Members: map[string]MemberKind{"Key": KindValue, "pub_fn": KindValue, "missing": KindType}}, []string{"Key", "pub_fn", "missing"})
	if len(problems) != 2 || problems[0].Name != "Key" || problems[0].Want != KindValue || problems[0].Got != KindType || problems[1].Name != "missing" || problems[1].Outcome != NoSuchMember {
		t.Fatalf("problems = %+v", problems)
	}
	if !ProjectionAllowed("p", "p", true) || ProjectionAllowed("p", "q", true) || !ProjectionAllowed("p", "q", false) {
		t.Fatal("ProjectionAllowed broken")
	}
}
