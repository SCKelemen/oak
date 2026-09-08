// Package resourceflow is Oak's checker-independent resource-authority core.
//
// It owns alias classes, consumption provenance, and path-state joins. The
// borrow checker and type checker project diagnostics and local policy from
// this one state machine rather than maintaining independent move models.
package resourceflow

import (
	"fmt"
	"sort"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
)

// Authority summarizes every control-flow path reaching a program point.
// A resource is usable only when it is definitely Live on all incoming paths.
type Authority uint8

const (
	AuthorityInvalid Authority = iota
	AuthorityLive
	AuthorityConsumed
	AuthorityMaybeConsumed
)

func (a Authority) String() string {
	switch a {
	case AuthorityLive:
		return "live"
	case AuthorityConsumed:
		return "consumed"
	case AuthorityMaybeConsumed:
		return "maybe-consumed"
	default:
		return "invalid"
	}
}

// JoinAuthority is the path join. Live and Consumed represent singleton sets
// of possible runtime states; MaybeConsumed represents {Live, Consumed}.
func JoinAuthority(left, right Authority) Authority {
	if left == AuthorityInvalid || right == AuthorityInvalid {
		return AuthorityInvalid
	}
	if left == right {
		return left
	}
	return AuthorityMaybeConsumed
}

// Consumption is one programmer-visible path that consumed an authority class.
type Consumption struct {
	Name string
	Site ast.Node
}

type classID uint64

type aliasInfo struct {
	class  classID
	parent string
	origin ast.Node
}

type classState struct {
	authority    Authority
	consumptions []Consumption
}

// AliasEdge is a directed provenance edge: Child derives authority from Parent.
type AliasEdge struct {
	Child  string
	Parent string
	Origin ast.Node
}

// Flow is one path-sensitive resource environment.
type Flow struct {
	nextClass classID
	aliases   map[string]aliasInfo
	classes   map[classID]*classState
}

func New() *Flow {
	return &Flow{
		aliases: make(map[string]aliasInfo),
		classes: make(map[classID]*classState),
	}
}

// Clone creates an independent branch state while retaining immutable source
// provenance. Later consumption in the clone does not mutate its parent path.
func (f *Flow) Clone() *Flow {
	if f == nil {
		return New()
	}
	out := &Flow{
		nextClass: f.nextClass,
		aliases:   make(map[string]aliasInfo, len(f.aliases)),
		classes:   make(map[classID]*classState, len(f.classes)),
	}
	for name, info := range f.aliases {
		out.aliases[name] = info
	}
	for id, state := range f.classes {
		if state == nil {
			continue
		}
		copyState := &classState{authority: state.authority}
		copyState.consumptions = append(copyState.consumptions, state.consumptions...)
		out.classes[id] = copyState
	}
	return out
}

// Register introduces a new independent resource authority class.
func (f *Flow) Register(name string, origin ast.Node) bool {
	if f == nil || name == "" {
		return false
	}
	if _, exists := f.aliases[name]; exists {
		return false
	}
	id := f.nextClass
	f.nextClass++
	f.aliases[name] = aliasInfo{class: id, origin: origin}
	f.classes[id] = &classState{authority: AuthorityLive}
	return true
}

// Alias records that alias derives authority from source. Alias creation
// requires source to be definitely live at this program point.
func (f *Flow) Alias(alias, source string, origin ast.Node) bool {
	if f == nil || alias == "" || source == "" || alias == source {
		return false
	}
	if _, exists := f.aliases[alias]; exists {
		return false
	}
	sourceInfo, exists := f.aliases[source]
	if !exists || !f.CanUse(source) {
		return false
	}
	f.aliases[alias] = aliasInfo{class: sourceInfo.class, parent: source, origin: origin}
	return true
}

// AuthorityOf reports the current path summary for a registered resource name.
func (f *Flow) AuthorityOf(name string) (Authority, bool) {
	if f == nil {
		return AuthorityInvalid, false
	}
	info, exists := f.aliases[name]
	if !exists {
		return AuthorityInvalid, false
	}
	state := f.classes[info.class]
	if state == nil {
		return AuthorityInvalid, false
	}
	return state.authority, true
}

func (f *Flow) Registered(name string) bool {
	_, ok := f.AuthorityOf(name)
	return ok
}

// CanUse is deliberately strict: conditional authority is not authority.
func (f *Flow) CanUse(name string) bool {
	authority, exists := f.AuthorityOf(name)
	return exists && authority == AuthorityLive
}

// Consume permanently consumes a definitely-live alias class on this path.
// MaybeConsumed is rejected because the operation would double-consume on some
// incoming path.
func (f *Flow) Consume(name string, site ast.Node) bool {
	if f == nil {
		return false
	}
	info, exists := f.aliases[name]
	if !exists {
		return false
	}
	state := f.classes[info.class]
	if state == nil || state.authority != AuthorityLive {
		return false
	}
	state.authority = AuthorityConsumed
	state.consumptions = []Consumption{{Name: name, Site: site}}
	return true
}

// Consumptions returns deterministic programmer-visible consume provenance for
// a name's class. MaybeConsumed states retain the consuming incoming paths.
func (f *Flow) Consumptions(name string) []Consumption {
	if f == nil {
		return nil
	}
	info, exists := f.aliases[name]
	if !exists {
		return nil
	}
	state := f.classes[info.class]
	if state == nil {
		return nil
	}
	out := append([]Consumption(nil), state.consumptions...)
	sort.SliceStable(out, func(i, j int) bool {
		li, lj := nodeOrder(out[i].Site), nodeOrder(out[j].Site)
		if li.line != lj.line {
			return li.line < lj.line
		}
		if li.column != lj.column {
			return li.column < lj.column
		}
		return out[i].Name < out[j].Name
	})
	return dedupeConsumptions(out)
}

// Aliases reports whether two registered names carry authority from one class.
func (f *Flow) Aliases(left, right string) bool {
	if f == nil {
		return false
	}
	li, lok := f.aliases[left]
	ri, rok := f.aliases[right]
	return lok && rok && li.class == ri.class
}

// AliasPath returns the deterministic shortest programmer-visible provenance
// path between two aliases in one authority class.
func (f *Flow) AliasPath(from, to string) []AliasEdge {
	if f == nil || from == "" || to == "" || from == to || !f.Aliases(from, to) {
		return nil
	}
	class := f.aliases[from].class
	neighbors := make(map[string][]string)
	for name, info := range f.aliases {
		if info.class != class || info.parent == "" {
			continue
		}
		neighbors[name] = append(neighbors[name], info.parent)
		neighbors[info.parent] = append(neighbors[info.parent], name)
	}
	for name := range neighbors {
		sort.Strings(neighbors[name])
	}

	queue := []string{from}
	seen := map[string]bool{from: true}
	prev := make(map[string]string)
	for len(queue) > 0 {
		current := queue[0]
		queue = queue[1:]
		for _, next := range neighbors[current] {
			if seen[next] {
				continue
			}
			seen[next] = true
			prev[next] = current
			if next == to {
				names := []string{to}
				for cursor := to; cursor != from; {
					cursor = prev[cursor]
					names = append(names, cursor)
				}
				for i, j := 0, len(names)-1; i < j; i, j = i+1, j-1 {
					names[i], names[j] = names[j], names[i]
				}
				edges := make([]AliasEdge, 0, len(names)-1)
				for i := 0; i+1 < len(names); i++ {
					if edge, ok := f.aliasEdge(names[i], names[i+1]); ok {
						edges = append(edges, edge)
					}
				}
				return edges
			}
			queue = append(queue, next)
		}
	}
	return nil
}

func (f *Flow) aliasEdge(left, right string) (AliasEdge, bool) {
	if info, exists := f.aliases[left]; exists && info.parent == right {
		return AliasEdge{Child: left, Parent: right, Origin: info.origin}, true
	}
	if info, exists := f.aliases[right]; exists && info.parent == left {
		return AliasEdge{Child: right, Parent: left, Origin: info.origin}, true
	}
	return AliasEdge{}, false
}

// Join merges reachable branch exits. Branches are expected to be clones of a
// common predecessor. Names introduced on only some paths do not escape the
// join; incompatible provenance also fails closed by dropping that name.
func Join(flows ...*Flow) *Flow {
	if len(flows) == 0 || flows[0] == nil {
		return New()
	}
	for _, flow := range flows {
		if flow == nil {
			return New()
		}
	}
	out := flows[0].Clone()

	for name, info := range out.aliases {
		compatible := true
		for _, flow := range flows[1:] {
			other, exists := flow.aliases[name]
			if !exists || other.class != info.class || other.parent != info.parent {
				compatible = false
				break
			}
		}
		if !compatible {
			delete(out.aliases, name)
		}
	}

	for id, state := range out.classes {
		if state == nil {
			continue
		}
		authority := state.authority
		consumptions := append([]Consumption(nil), state.consumptions...)
		valid := true
		for _, flow := range flows[1:] {
			other := flow.classes[id]
			if other == nil {
				valid = false
				break
			}
			authority = JoinAuthority(authority, other.authority)
			consumptions = append(consumptions, other.consumptions...)
		}
		if !valid {
			delete(out.classes, id)
			continue
		}
		state.authority = authority
		state.consumptions = dedupeConsumptions(consumptions)
	}

	usedClasses := make(map[classID]bool)
	for name, info := range out.aliases {
		if _, exists := out.classes[info.class]; !exists {
			delete(out.aliases, name)
			continue
		}
		usedClasses[info.class] = true
	}
	for id := range out.classes {
		if !usedClasses[id] {
			delete(out.classes, id)
		}
	}
	return out
}

type orderKey struct {
	line, column int
}

func nodeOrder(node ast.Node) orderKey {
	if node == nil {
		max := int(^uint(0) >> 1)
		return orderKey{line: max, column: max}
	}
	start := diagnostic.NodeToRange(node).Start
	return orderKey{line: start.Line, column: start.Character}
}

func dedupeConsumptions(in []Consumption) []Consumption {
	out := make([]Consumption, 0, len(in))
	seen := make(map[string]bool)
	for _, item := range in {
		key := item.Name
		if item.Site != nil {
			start := diagnostic.NodeToRange(item.Site).Start
			key += fmt.Sprintf("@%d:%d", start.Line, start.Character)
		}
		if seen[key] {
			continue
		}
		seen[key] = true
		out = append(out, item)
	}
	return out
}
