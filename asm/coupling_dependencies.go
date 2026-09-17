package asm

// couplingDependencies caches machine-symbol dependencies of source terms
// and coupling replacements, which stay fixed while the search changes
// sigma. It does not retain the large terms each substitution rebuilds.
type couplingDependencies struct {
	symbols map[string]bool
	cache   map[*term][]string
}

func (d *couplingDependencies) names(t *term) []string {
	if names, known := d.cache[t]; known {
		return names
	}
	mentioned := map[string]bool{}
	collectParams(t, mentioned)
	var names []string
	for name := range mentioned {
		if d.symbols[name] {
			names = append(names, name)
		}
	}
	if d.cache == nil {
		d.cache = map[*term][]string{}
	}
	d.cache[t] = names
	return names
}

// ready conservatively predicts whether substitute(t, sigma) will mention
// no unpaired machine symbol. Substitution replaces a parameter once, so
// inspect its replacement's names without recursively substituting them.
// A later width change can erase a dependency; deferring in that case only
// misses an early refutation, never the complete candidate's proof.
func (d *couplingDependencies) ready(t *term, sigma map[string]*term) bool {
	for _, name := range d.names(t) {
		replacement := sigma[name]
		if replacement == nil {
			return false
		}
		for _, introduced := range d.names(replacement) {
			if sigma[introduced] == nil {
				return false
			}
		}
	}
	return true
}
