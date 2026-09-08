package borrowchecker

import (
	"fmt"
	"sort"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
)

// CodeResourceUsedAfterConsume is the stable diagnostic for a resource name
// (including any alias in the same authority class) used after consumption.
const CodeResourceUsedAfterConsume diagnostic.Code = "OAK-B0111"

type resourceClassID uint64

type resourceAliasInfo struct {
	class  resourceClassID
	parent string
	origin ast.Node
}

type resourceConsumption struct {
	name string
	site ast.Node
}

type resourceClassState struct {
	consumed *resourceConsumption
}

// ResourceFlow is the executable counterpart of Oak.ResourceFlow. It tracks
// resource authority separately from temporary borrow state: a UniqueWrite
// borrow can be released, while a consumed alias class never regains authority.
//
// Surface syntax is intentionally not part of this type. The semantic layer
// should register resource-typed values/aliases and invoke Use/Consume after
// type resolution, once Oak's consume spelling is frozen.
type ResourceFlow struct {
	checker   *BorrowChecker
	nextClass resourceClassID
	aliases   map[string]resourceAliasInfo
	classes   map[resourceClassID]*resourceClassState
}

// NewResourceFlow creates an empty resource-flow analysis associated with a
// borrow checker. The association lets consumption reject any live view/span
// whose backing owner belongs to the same resource alias class.
func NewResourceFlow(checker *BorrowChecker) *ResourceFlow {
	return &ResourceFlow{
		checker: checker,
		aliases: make(map[string]resourceAliasInfo),
		classes: make(map[resourceClassID]*resourceClassState),
	}
}

// Register introduces a new independently-owned resource authority class.
// Duplicate registrations are rejected without mutating existing provenance.
func (rf *ResourceFlow) Register(name string, origin ast.Node) bool {
	if rf == nil || name == "" {
		return false
	}
	if _, exists := rf.aliases[name]; exists {
		return false
	}

	classID := rf.nextClass
	rf.nextClass++
	rf.aliases[name] = resourceAliasInfo{class: classID, origin: origin}
	rf.classes[classID] = &resourceClassState{}
	return true
}

// Alias records that alias derives resource authority from source. Alias
// creation itself uses source authority, so it is rejected if source was
// already consumed. The parent edge is retained for programmer-facing
// provenance diagnostics; authority remains class-wide.
func (rf *ResourceFlow) Alias(alias, source string, origin ast.Node) bool {
	if rf == nil || alias == "" || source == "" || alias == source {
		return false
	}
	if _, exists := rf.aliases[alias]; exists {
		return false
	}
	sourceInfo, exists := rf.aliases[source]
	if !exists {
		return false
	}
	if !rf.Use(source, origin) {
		return false
	}

	rf.aliases[alias] = resourceAliasInfo{
		class:  sourceInfo.class,
		parent: source,
		origin: origin,
	}
	return true
}

// Use validates one resource access. Non-resource names are ignored so the
// caller can invoke this after ordinary identifier classification. A consumed
// class produces OAK-B0111 with the original consume site and the shortest
// available programmer-visible alias chain.
func (rf *ResourceFlow) Use(name string, node ast.Node) bool {
	if rf == nil || name == "" {
		return true
	}
	info, exists := rf.aliases[name]
	if !exists {
		return true
	}
	classState := rf.classes[info.class]
	if classState == nil || classState.consumed == nil {
		return true
	}

	rf.reportConsumedUse(name, node, classState.consumed)
	return false
}

// Consume permanently removes authority from name's entire alias class.
// Consumption is rejected while any live borrow depends on a class member.
// A second consume is itself a use-after-consume and therefore reports
// OAK-B0111.
func (rf *ResourceFlow) Consume(name string, site ast.Node) bool {
	if rf == nil || name == "" {
		return false
	}
	info, exists := rf.aliases[name]
	if !exists {
		return false
	}
	classState := rf.classes[info.class]
	if classState == nil {
		return false
	}
	if classState.consumed != nil {
		rf.reportConsumedUse(name, site, classState.consumed)
		return false
	}

	if borrowName, borrow, ok := rf.firstDependentBorrow(info.class); ok {
		if rf.checker != nil {
			d := rf.checker.reportBorrow(site, CodeBorrowGeneric,
				fmt.Sprintf("resource %q cannot be consumed while borrow %q is live", name, borrowName))
			rf.checker.addBorrowContext(d, borrowName, borrow,
				fmt.Sprintf("borrow %q still depends on this resource authority", borrowName))
			d.AddNote("consumption is permanent; Oak requires dependent temporary borrows to end first")
			d.AddHelp("let the view/span leave scope before consuming the resource")
		}
		return false
	}

	classState.consumed = &resourceConsumption{name: name, site: site}
	return true
}

// Consumed reports whether name is a registered resource whose alias class has
// already lost authority. It is primarily useful to semantic pipeline tests
// and later control-flow joining.
func (rf *ResourceFlow) Consumed(name string) bool {
	if rf == nil {
		return false
	}
	info, exists := rf.aliases[name]
	if !exists {
		return false
	}
	classState := rf.classes[info.class]
	return classState != nil && classState.consumed != nil
}

func (rf *ResourceFlow) reportConsumedUse(name string, node ast.Node, consumed *resourceConsumption) {
	if rf == nil || rf.checker == nil || consumed == nil {
		return
	}

	d := rf.checker.reportBorrow(node, CodeResourceUsedAfterConsume,
		fmt.Sprintf("resource %q cannot be used after its authority was consumed", name))
	if consumed.site != nil {
		d.AddSecondary(diagnostic.NodeToRange(consumed.site),
			fmt.Sprintf("resource authority was consumed here through %q", consumed.name))
	} else {
		d.AddNote(fmt.Sprintf("resource authority was previously consumed through %q", consumed.name))
	}

	path := rf.aliasPath(consumed.name, name)
	for i := 0; i+1 < len(path); i++ {
		left, right := path[i], path[i+1]
		child, parent, origin, ok := rf.aliasEdge(left, right)
		if !ok {
			continue
		}
		message := fmt.Sprintf("resource alias %q derives authority from %q", child, parent)
		if origin != nil {
			d.AddSecondary(diagnostic.NodeToRange(origin), message)
		} else {
			d.AddNote(message)
		}
	}
	d.AddHelp("use the resource value returned by the consuming operation, if it transfers authority back")
}

// firstDependentBorrow finds the earliest source-causal live borrow whose
// owner belongs to classID. Sorting makes diagnostics independent of Go map
// iteration order.
func (rf *ResourceFlow) firstDependentBorrow(classID resourceClassID) (string, borrowInfo, bool) {
	if rf == nil || rf.checker == nil {
		return "", borrowInfo{}, false
	}
	type candidate struct {
		name string
		info borrowInfo
	}
	candidates := make([]candidate, 0)
	for borrowName, info := range rf.checker.activeBorrows {
		ownerInfo, ok := rf.aliases[info.owner]
		if !ok || ownerInfo.class != classID {
			continue
		}
		candidates = append(candidates, candidate{name: borrowName, info: info})
	}
	if len(candidates) == 0 {
		return "", borrowInfo{}, false
	}

	sort.Slice(candidates, func(i, j int) bool {
		left, right := candidates[i], candidates[j]
		if left.info.origin != nil && right.info.origin != nil {
			lr := diagnostic.NodeToRange(left.info.origin).Start
			rr := diagnostic.NodeToRange(right.info.origin).Start
			if lr.Line != rr.Line {
				return lr.Line < rr.Line
			}
			if lr.Character != rr.Character {
				return lr.Character < rr.Character
			}
		} else if left.info.origin != nil {
			return true
		} else if right.info.origin != nil {
			return false
		}
		return left.name < right.name
	})
	return candidates[0].name, candidates[0].info, true
}

// aliasPath returns the deterministic shortest path between two names in one
// alias class. Alias registration forms a tree today, but BFS deliberately
// treats the graph generically so future provenance edges do not change the
// diagnostic contract.
func (rf *ResourceFlow) aliasPath(from, to string) []string {
	if rf == nil || from == "" || to == "" {
		return nil
	}
	if from == to {
		return []string{from}
	}
	fromInfo, fromOK := rf.aliases[from]
	toInfo, toOK := rf.aliases[to]
	if !fromOK || !toOK || fromInfo.class != toInfo.class {
		return nil
	}

	neighbors := make(map[string][]string)
	for name, info := range rf.aliases {
		if info.class != fromInfo.class || info.parent == "" {
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
				path := []string{to}
				for cursor := to; cursor != from; {
					cursor = prev[cursor]
					path = append(path, cursor)
				}
				for i, j := 0, len(path)-1; i < j; i, j = i+1, j-1 {
					path[i], path[j] = path[j], path[i]
				}
				return path
			}
			queue = append(queue, next)
		}
	}
	return nil
}

// aliasEdge recovers the directed provenance edge between adjacent names.
func (rf *ResourceFlow) aliasEdge(left, right string) (child, parent string, origin ast.Node, ok bool) {
	if info, exists := rf.aliases[left]; exists && info.parent == right {
		return left, right, info.origin, true
	}
	if info, exists := rf.aliases[right]; exists && info.parent == left {
		return right, left, info.origin, true
	}
	return "", "", nil, false
}
