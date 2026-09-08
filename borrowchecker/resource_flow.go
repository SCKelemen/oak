package borrowchecker

import (
	"fmt"
	"sort"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/resourceflow"
)

// CodeResourceUsedAfterConsume is the stable diagnostic for a resource name
// (including any alias in the same authority class) used after consumption.
const CodeResourceUsedAfterConsume diagnostic.Code = "OAK-B0111"

// ResourceFlow is the borrow-checker projection of Oak's shared path-sensitive
// resource authority state. Temporary borrow conflicts remain borrow-checker
// policy; alias classes, consumption, snapshots, and joins live in resourceflow.
type ResourceFlow struct {
	checker *BorrowChecker
	flow    *resourceflow.Flow
}

// NewResourceFlow creates an empty resource-flow analysis associated with a
// borrow checker. The association lets consumption reject any live view/span
// whose backing owner belongs to the same resource alias class.
func NewResourceFlow(checker *BorrowChecker) *ResourceFlow {
	return &ResourceFlow{checker: checker, flow: resourceflow.New()}
}

// Clone creates an independent control-flow branch state.
func (rf *ResourceFlow) Clone() *ResourceFlow {
	if rf == nil {
		return NewResourceFlow(nil)
	}
	return &ResourceFlow{checker: rf.checker, flow: rf.flow.Clone()}
}

// JoinResourceFlows joins reachable branch exits. Only authority definitely
// live on every incoming path remains usable after the join.
func JoinResourceFlows(flows ...*ResourceFlow) *ResourceFlow {
	if len(flows) == 0 {
		return NewResourceFlow(nil)
	}
	checker := flows[0].checker
	cores := make([]*resourceflow.Flow, 0, len(flows))
	for _, flow := range flows {
		if flow == nil {
			cores = append(cores, nil)
			continue
		}
		cores = append(cores, flow.flow)
	}
	return &ResourceFlow{checker: checker, flow: resourceflow.Join(cores...)}
}

// Register introduces a new independently-owned resource authority class.
func (rf *ResourceFlow) Register(name string, origin ast.Node) bool {
	return rf != nil && rf.flow != nil && rf.flow.Register(name, origin)
}

// Alias records that alias derives resource authority from source. Alias
// creation itself uses source authority, so consumed/maybe-consumed sources
// produce the same OAK-B0111 diagnostic as any later use.
func (rf *ResourceFlow) Alias(alias, source string, origin ast.Node) bool {
	if rf == nil || rf.flow == nil || alias == "" || source == "" {
		return false
	}
	if !rf.Use(source, origin) {
		return false
	}
	return rf.flow.Alias(alias, source, origin)
}

// Use validates one resource access. Non-resource names are ignored so the
// caller can invoke this after ordinary identifier classification.
func (rf *ResourceFlow) Use(name string, node ast.Node) bool {
	if rf == nil || rf.flow == nil || name == "" || !rf.flow.Registered(name) {
		return true
	}
	if rf.flow.CanUse(name) {
		return true
	}
	rf.reportUnavailableUse(name, node)
	return false
}

// Consume permanently removes authority from name's entire alias class on the
// current path. Consumption is rejected while a dependent temporary borrow is
// live, and also when authority is already consumed or only maybe live.
func (rf *ResourceFlow) Consume(name string, site ast.Node) bool {
	if rf == nil || rf.flow == nil || name == "" || !rf.flow.Registered(name) {
		return false
	}
	if !rf.flow.CanUse(name) {
		rf.reportUnavailableUse(name, site)
		return false
	}

	if borrowName, borrow, ok := rf.firstDependentBorrow(name); ok {
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
	return rf.flow.Consume(name, site)
}

// Authority reports the path summary for a registered resource.
func (rf *ResourceFlow) Authority(name string) (resourceflow.Authority, bool) {
	if rf == nil || rf.flow == nil {
		return resourceflow.AuthorityInvalid, false
	}
	return rf.flow.AuthorityOf(name)
}

// Consumed is true only when every incoming path has consumed the authority.
// Maybe-consumed remains unavailable, but is not definitely consumed.
func (rf *ResourceFlow) Consumed(name string) bool {
	authority, exists := rf.Authority(name)
	return exists && authority == resourceflow.AuthorityConsumed
}

func (rf *ResourceFlow) reportUnavailableUse(name string, node ast.Node) {
	if rf == nil || rf.flow == nil || rf.checker == nil {
		return
	}
	authority, exists := rf.flow.AuthorityOf(name)
	if !exists || authority == resourceflow.AuthorityLive {
		return
	}

	title := fmt.Sprintf("resource %q cannot be used after its authority was consumed", name)
	if authority == resourceflow.AuthorityMaybeConsumed {
		title = fmt.Sprintf("resource %q cannot be used because its authority may have been consumed", name)
	}
	d := rf.checker.reportBorrow(node, CodeResourceUsedAfterConsume, title)

	consumptions := rf.flow.Consumptions(name)
	for _, consumed := range consumptions {
		if consumed.Site != nil {
			message := fmt.Sprintf("resource authority was consumed on this path through %q", consumed.Name)
			if authority == resourceflow.AuthorityConsumed && len(consumptions) == 1 {
				message = fmt.Sprintf("resource authority was consumed here through %q", consumed.Name)
			}
			d.AddSecondary(diagnostic.NodeToRange(consumed.Site), message)
		} else {
			d.AddNote(fmt.Sprintf("resource authority was consumed through %q on an incoming path", consumed.Name))
		}

		for _, edge := range rf.flow.AliasPath(consumed.Name, name) {
			message := fmt.Sprintf("resource alias %q derives authority from %q", edge.Child, edge.Parent)
			if edge.Origin != nil {
				d.AddSecondary(diagnostic.NodeToRange(edge.Origin), message)
			} else {
				d.AddNote(message)
			}
		}
	}
	if authority == resourceflow.AuthorityMaybeConsumed {
		d.AddNote("the control-flow join includes both a live path and a consumed path; authority must be live on every path")
	}
	d.AddHelp("use the resource value returned by the consuming operation, if it transfers authority back")
}

// firstDependentBorrow finds the earliest source-causal live borrow whose
// owner aliases resourceName. Sorting keeps diagnostics deterministic.
func (rf *ResourceFlow) firstDependentBorrow(resourceName string) (string, borrowInfo, bool) {
	if rf == nil || rf.flow == nil || rf.checker == nil {
		return "", borrowInfo{}, false
	}
	type candidate struct {
		name string
		info borrowInfo
	}
	candidates := make([]candidate, 0)
	for borrowName, info := range rf.checker.activeBorrows {
		if !rf.flow.Aliases(info.owner, resourceName) {
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
