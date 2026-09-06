from pathlib import Path
import re


def replace_once(text: str, old: str, new: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence, got {count}: {old[:80]!r}")
    return text.replace(old, new, 1)


path = Path("semir/validate.go")
s = path.read_text()
s = replace_once(s, 'import "fmt"', 'import (\n\t"fmt"\n\t"strings"\n)')

needle = '''\tprotocols := make(map[string]struct{}, len(m.Protocols))
'''
insert = '''\tallocators := make(map[string]struct{}, len(m.Allocators))
\tfor _, allocator := range m.Allocators {
\t\tif err := allocator.Validate(); err != nil {
\t\t\treturn err
\t\t}
\t\tif _, exists := allocators[allocator.Name]; exists {
\t\t\treturn fmt.Errorf("duplicate allocator %q", allocator.Name)
\t\t}
\t\tallocators[allocator.Name] = struct{}{}
\t}

\tprotocols := make(map[string]struct{}, len(m.Protocols))
'''
s = replace_once(s, needle, insert)

authority = '''func (a Authority) Validate() error {
\tif err := validateEffectList("required", a.RequiredEffects); err != nil {
\t\treturn err
\t}
\tif err := validateEffectList("forbidden", a.ForbiddenEffects); err != nil {
\t\treturn err
\t}
\tfor _, required := range a.RequiredEffects {
\t\tfor _, forbidden := range a.ForbiddenEffects {
\t\t\tif effectsOverlap(required, forbidden) {
\t\t\t\trequiredKey, _ := effectKey(required)
\t\t\t\tforbiddenKey, _ := effectKey(forbidden)
\t\t\t\treturn fmt.Errorf("effect %q overlaps %q and is both required and forbidden", requiredKey, forbiddenKey)
\t\t\t}
\t\t}
\t}

\tcapabilities := make(map[string]struct{}, len(a.Capabilities))
\tfor _, capability := range a.Capabilities {
\t\tif capability.Name == "" {
\t\t\treturn fmt.Errorf("capability has empty name")
\t\t}
\t\tkey := qualified(capability.Namespace, capability.Name)
\t\tif _, exists := capabilities[key]; exists {
\t\t\treturn fmt.Errorf("duplicate capability %q", key)
\t\t}
\t\tcapabilities[key] = struct{}{}
\t}
\treturn nil
}
'''
s, n = re.subn(r'func \(a Authority\) Validate\(\) error \{.*?\n\}\n\nfunc \(p Protocol\) Validate', authority + '\nfunc (p Protocol) Validate', s, count=1, flags=re.S)
if n != 1:
    raise RuntimeError(f"Authority.Validate replacement count {n}")

old = '''func effectKey(effect Effect) (string, error) {
\tif effect.Name == "" {
\t\treturn "", fmt.Errorf("effect has empty name")
\t}
\treturn qualified(effect.Namespace, effect.Name), nil
}
'''
new = '''func validateEffectList(kind string, effects []Effect) error {
\tseen := make(map[string]struct{}, len(effects))
\tfor _, effect := range effects {
\t\tkey, err := effectKey(effect)
\t\tif err != nil {
\t\t\treturn err
\t\t}
\t\tif _, exists := seen[key]; exists {
\t\t\treturn fmt.Errorf("duplicate %s effect %q", kind, key)
\t\t}
\t\tseen[key] = struct{}{}
\t}
\treturn nil
}

func effectKey(effect Effect) (string, error) {
\tif effect.Name == "" {
\t\treturn "", fmt.Errorf("effect has empty name")
\t}
\tbase := qualified(effect.Namespace, effect.Name)
\tif len(effect.Parameters) == 0 {
\t\treturn base, nil
\t}
\tfor _, parameter := range effect.Parameters {
\t\tif parameter == "" {
\t\t\treturn "", fmt.Errorf("effect %q has empty parameter", base)
\t\t}
\t}
\treturn base + "[" + strings.Join(effect.Parameters, ",") + "]", nil
}

// effectsOverlap implements effect-class subsumption: an unparameterized effect
// denotes the whole class, while two parameterized effects overlap only when
// their parameter lists are identical.
func effectsOverlap(left, right Effect) bool {
\tif left.Namespace != right.Namespace || left.Name != right.Name {
\t\treturn false
\t}
\tif len(left.Parameters) == 0 || len(right.Parameters) == 0 {
\t\treturn true
\t}
\tif len(left.Parameters) != len(right.Parameters) {
\t\treturn false
\t}
\tfor i := range left.Parameters {
\t\tif left.Parameters[i] != right.Parameters[i] {
\t\t\treturn false
\t\t}
\t}
\treturn true
}
'''
s = replace_once(s, old, new)
path.write_text(s)
