from pathlib import Path

path = Path("borrowchecker/borrowchecker.go")
text = path.read_text()


def replace_once(old: str, new: str, label: str) -> None:
    global text
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected exactly one match, found {count}")
    text = text.replace(old, new, 1)


replace_once(
'''type borrowInfo struct {
\towner      string     // The owner variable name
\tkind       borrowKind // Whether this is a view or span
\tblockDepth int        // Block depth where this borrow was created
\tregion     *Region    // Optional: region information for disjointness checks (nil if unknown)
}''',
'''type borrowInfo struct {
\towner      string     // The owner variable name
\tkind       borrowKind // Whether this is a view or span
\tblockDepth int        // Block depth where this borrow was created
\tregion     *Region    // Optional: region information for disjointness checks (nil if unknown)
\torigin     ast.Node   // Source expression that created this borrow, when known
}''',
"borrowInfo origin",
)

replace_once(
'''\t// errors collects borrow checker errors
\terrors []string
''',
'''\t// diagnostics are the first-class borrow-checking result. Errors() remains
\t// a compatibility projection for older callers and tests.
\tdiagnostics *diagnosticsState
''',
"BorrowChecker diagnostics field",
)

replace_once(
'''\t\townerStates:   make(map[string]BorrowState),
\t\townerOf:       make(map[string]string),
\t\tactiveBorrows: make(map[string]borrowInfo),
\t\terrors:        []string{},
''',
'''\t\townerStates:   make(map[string]BorrowState),
\t\townerOf:       make(map[string]string),
\t\tactiveBorrows: make(map[string]borrowInfo),
\t\tdiagnostics:   newDiagnosticsState(),
''',
"New diagnostics initialization",
)

replace_once(
'''// Errors returns all borrow checker errors
func (bc *BorrowChecker) Errors() []string {
\treturn bc.errors
}

// ClearErrors clears all errors
func (bc *BorrowChecker) ClearErrors() {
\tbc.errors = []string{}
}

// addError adds an error to the error list
func (bc *BorrowChecker) addError(msg string) {
\tbc.errors = append(bc.errors, fmt.Sprintf("[borrow error] %s", msg))
}''',
'''// Errors returns a compatibility text projection of first-class diagnostics.
func (bc *BorrowChecker) Errors() []string {
\treturn bc.diagnostics.errorStrings()
}

// ClearErrors clears all borrow diagnostics.
func (bc *BorrowChecker) ClearErrors() {
\tbc.diagnostics.clear()
}

// addError is the migration fallback for borrow checks that have not yet been
// assigned a specific stable code. New checks should call reportBorrow.
func (bc *BorrowChecker) addError(msg string) {
\tbc.reportBorrow(nil, CodeBorrowGeneric, msg)
}''',
"legacy error collector",
)

replace_once(
'''\tif _, exists := bc.activeBorrows[stmt.Name.Value]; exists {
\t\tbc.addError(fmt.Sprintf("cannot reassign borrow variable '%s'; borrows are immutable bindings", stmt.Name.Value))
\t\treturn
\t}''',
'''\tif info, exists := bc.activeBorrows[stmt.Name.Value]; exists {
\t\td := bc.reportBorrow(stmt.Name, CodeBorrowReassign,
\t\t\tfmt.Sprintf("borrow %q cannot be reassigned", stmt.Name.Value))
\t\tbc.addBorrowContext(d, stmt.Name.Value, info,
\t\t\t"this binding already carries borrowed access")
\t\td.AddNote("views and spans are non-owning access paths tied to their backing owner")
\t\td.AddHelp("create a new view/span binding, or end the current borrow before reusing the name")
\t\treturn
\t}''',
"borrow reassignment diagnostic",
)

text = text.replace('bc.checkIdentifierUse(stmt.Name.Value, env, true)', 'bc.checkIdentifierUse(stmt.Name, stmt.Name.Value, env, true)')
text = text.replace('bc.checkIdentifierUse(e.Value, env, false)', 'bc.checkIdentifierUse(e, e.Value, env, false)')

replace_once(
'''\t\t\tbc.createViewBorrowWithRegion(ownerName, targetVar, region)''',
'''\t\t\tbc.createViewBorrowWithRegion(ownerName, targetVar, region, slice)''',
"slice view origin",
)

replace_once(
'''\t\tbc.createViewBorrowWithRegion(ownerName, targetVar, region)''',
'''\t\tbc.createViewBorrowWithRegion(ownerName, targetVar, region, call)''',
"view call origin",
)

replace_once(
'''\t\tbc.createSpanBorrowWithRegion(ownerName, targetVar, region)''',
'''\t\tbc.createSpanBorrowWithRegion(ownerName, targetVar, region, call)''',
"span call origin",
)

replace_once(
'''func (bc *BorrowChecker) checkIdentifierUse(name string, env *typechecker.TypeEnvironment, isWrite bool) {
\t// Check if this is an owner
\tstate, isOwner := bc.ownerStates[name]
\tif !isOwner {
\t\t// Not an owner - could be a borrow or other variable, no restriction
\t\treturn
\t}

\t// This is an owner - check if it's being used while borrowed
\tif state == UniqueWrite {
\t\t// Owner has an active writable span - disallow any use (read or write)
\t\tbc.addError(fmt.Sprintf("cannot use owner '%s' while it has an active writable span", name))
\t\treturn
\t}

\tif state == SharedRead && isWrite {
\t\t// Owner has active read-only views - disallow writes
\t\tbc.addError(fmt.Sprintf("cannot write to owner '%s' while it has active read-only views", name))
\t\treturn
\t}

\t// SharedRead + read operation: allowed (multiple readers can coexist)
}''',
'''func (bc *BorrowChecker) checkIdentifierUse(node ast.Node, name string, env *typechecker.TypeEnvironment, isWrite bool) {
\t// Check if this is an owner
\tstate, isOwner := bc.ownerStates[name]
\tif !isOwner {
\t\t// Not an owner - could be a borrow or other variable, no restriction
\t\treturn
\t}

\t// This is an owner - check if it's being used while borrowed.
\tif state == UniqueWrite {
\t\td := bc.reportBorrow(node, CodeOwnerUsedDuringSpan,
\t\t\tfmt.Sprintf("owner %q cannot be used while writable access is active", name))
\t\tif borrowName, info, ok := bc.firstActiveBorrow(name, BorrowSpan); ok {
\t\t\tbc.addBorrowContext(d, borrowName, info,
\t\t\t\tfmt.Sprintf("writable span %q keeps exclusive access here", borrowName))
\t\t}
\t\td.AddHelp("use the existing span for access, or let it leave scope before using the owner directly")
\t\treturn
\t}

\tif state == SharedRead && isWrite {
\t\td := bc.reportBorrow(node, CodeOwnerWrittenDuringView,
\t\t\tfmt.Sprintf("owner %q cannot be written while read-only views are active", name))
\t\tif borrowName, info, ok := bc.firstActiveBorrow(name, BorrowView); ok {
\t\t\tbc.addBorrowContext(d, borrowName, info,
\t\t\t\tfmt.Sprintf("read-only view %q observes this owner", borrowName))
\t\t}
\t\td.AddHelp("finish using the views before mutating the owner")
\t\treturn
\t}

\t// SharedRead + read operation: allowed (multiple readers can coexist).
}''',
"identifier-use diagnostics",
)

replace_once(
'''func (bc *BorrowChecker) createViewBorrow(ownerName, borrowName string) {
\tbc.createViewBorrowWithRegion(ownerName, borrowName, nil)
}

// createViewBorrowWithRegion creates a read-only borrow (view) from an owner with region information
func (bc *BorrowChecker) createViewBorrowWithRegion(ownerName, borrowName string, region *Region) {
\tstate := bc.ownerStates[ownerName]
\tif state == UniqueWrite {
\t\tbc.addError(fmt.Sprintf("cannot create view '%s' from '%s': owner has active writable borrow", borrowName, ownerName))
\t\treturn
\t}

\t// Transition to SharedRead if not already
\tbc.ownerStates[ownerName] = SharedRead
\tbc.ownerOf[borrowName] = ownerName

\t// Track this borrow with metadata
\tbc.activeBorrows[borrowName] = borrowInfo{
\t\towner:      ownerName,
\t\tkind:       BorrowView,
\t\tblockDepth: bc.currentBlockDepth,
\t\tregion:     region,
\t}
}''',
'''func (bc *BorrowChecker) createViewBorrow(ownerName, borrowName string) {
\tbc.createViewBorrowWithRegion(ownerName, borrowName, nil, nil)
}

// createViewBorrowWithRegion creates a read-only borrow (view) from an owner with region information.
func (bc *BorrowChecker) createViewBorrowWithRegion(ownerName, borrowName string, region *Region, origin ast.Node) {
\tstate := bc.ownerStates[ownerName]
\tif state == UniqueWrite {
\t\td := bc.reportBorrow(origin, CodeViewConflictsWithSpan,
\t\t\tfmt.Sprintf("view %q cannot be created while %q has writable access", borrowName, ownerName))
\t\tif existingName, info, ok := bc.firstActiveBorrow(ownerName, BorrowSpan); ok {
\t\t\tbc.addBorrowContext(d, existingName, info,
\t\t\t\tfmt.Sprintf("writable span %q already has exclusive access", existingName))
\t\t}
\t\td.AddHelp("end the writable span before creating a read-only view")
\t\treturn
\t}

\t// Transition to SharedRead if not already.
\tbc.ownerStates[ownerName] = SharedRead
\tbc.ownerOf[borrowName] = ownerName

\t// Track this borrow with metadata.
\tbc.activeBorrows[borrowName] = borrowInfo{
\t\towner:      ownerName,
\t\tkind:       BorrowView,
\t\tblockDepth: bc.currentBlockDepth,
\t\tregion:     region,
\t\torigin:     origin,
\t}
}''',
"view conflict diagnostics",
)

replace_once(
'''func (bc *BorrowChecker) createSpanBorrow(ownerName, borrowName string) {
\tbc.createSpanBorrowWithRegion(ownerName, borrowName, nil)
}''',
'''func (bc *BorrowChecker) createSpanBorrow(ownerName, borrowName string) {
\tbc.createSpanBorrowWithRegion(ownerName, borrowName, nil, nil)
}''',
"span wrapper origin",
)

old_span = '''// createSpanBorrowWithRegion creates a unique writable borrow (span) from an owner with region information
// This implements v2 region-level disjointness: multiple spans are allowed if their regions are provably disjoint
func (bc *BorrowChecker) createSpanBorrowWithRegion(ownerName, borrowName string, region *Region) {
\tstate := bc.ownerStates[ownerName]

\t// Check for existing spans on the same owner
\texistingSpans := []borrowInfo{}
\tfor _, info := range bc.activeBorrows {
\t\tif info.owner == ownerName && info.kind == BorrowSpan {
\t\t\texistingSpans = append(existingSpans, info)
\t\t}
\t}

\tif len(existingSpans) > 0 {
\t\t// We have existing spans - check if regions are disjoint
\t\tif region != nil {
\t\t\t// We have region information - check disjointness
\t\t\tallDisjoint := true
\t\t\tfor _, existing := range existingSpans {
\t\t\t\tif existing.region != nil {
\t\t\t\t\tif bc.regionsOverlap(region, existing.region) {
\t\t\t\t\t\tallDisjoint = false
\t\t\t\t\t\tbreak
\t\t\t\t\t}
\t\t\t\t} else {
\t\t\t\t\t// Existing span has unknown region - can't prove disjointness
\t\t\t\t\tallDisjoint = false
\t\t\t\t\tbreak
\t\t\t\t}
\t\t\t}

\t\t\tif allDisjoint {
\t\t\t\t// All regions are disjoint - allow multiple spans
\t\t\t\t// Don't change owner state - we track multiple spans now
\t\t\t\tbc.ownerOf[borrowName] = ownerName
\t\t\t\tbc.activeBorrows[borrowName] = borrowInfo{
\t\t\t\t\towner:      ownerName,
\t\t\t\t\tkind:       BorrowSpan,
\t\t\t\t\tblockDepth: bc.currentBlockDepth,
\t\t\t\t\tregion:     region,
\t\t\t\t}
\t\t\t\treturn
\t\t\t}
\t\t}

\t\t// Can't prove disjointness - fall back to v1 behavior (reject)
\t\tbc.addError(fmt.Sprintf("cannot create span '%s' from '%s': owner has active span borrows (state: %s). Use disjoint regions to allow multiple spans", borrowName, ownerName, state))
\t\treturn
\t}

\t// No existing spans - check for views
\tif state == SharedRead {
\t\tbc.addError(fmt.Sprintf("cannot create span '%s' from '%s': owner has active read-only views", borrowName, ownerName))
\t\treturn
\t}

\t// Transition to UniqueWrite (or keep Free if we're allowing multiple disjoint spans)
\tif state == Free {
\t\tbc.ownerStates[ownerName] = UniqueWrite
\t}
\tbc.ownerOf[borrowName] = ownerName

\t// Track this borrow with metadata
\tbc.activeBorrows[borrowName] = borrowInfo{
\t\towner:      ownerName,
\t\tkind:       BorrowSpan,
\t\tblockDepth: bc.currentBlockDepth,
\t\tregion:     region,
\t}
}'''
new_span = '''// createSpanBorrowWithRegion creates a unique writable borrow (span) from an owner with region information.
// Multiple spans are allowed only when every active writable region is provably disjoint.
func (bc *BorrowChecker) createSpanBorrowWithRegion(ownerName, borrowName string, region *Region, origin ast.Node) {
\tstate := bc.ownerStates[ownerName]
\tspanNames := bc.activeBorrowNames(ownerName, BorrowSpan)

\tif len(spanNames) > 0 {
\t\tvar conflictName string
\t\tvar conflict borrowInfo
\t\tallDisjoint := region != nil
\t\tif allDisjoint {
\t\t\tfor _, existingName := range spanNames {
\t\t\t\texisting := bc.activeBorrows[existingName]
\t\t\t\tif existing.region == nil || bc.regionsOverlap(region, existing.region) {
\t\t\t\t\tallDisjoint = false
\t\t\t\t\tconflictName = existingName
\t\t\t\t\tconflict = existing
\t\t\t\t\tbreak
\t\t\t\t}
\t\t\t}
\t\t} else {
\t\t\tconflictName = spanNames[0]
\t\t\tconflict = bc.activeBorrows[conflictName]
\t\t}

\t\tif allDisjoint {
\t\t\tbc.ownerOf[borrowName] = ownerName
\t\t\tbc.activeBorrows[borrowName] = borrowInfo{
\t\t\t\towner:      ownerName,
\t\t\t\tkind:       BorrowSpan,
\t\t\t\tblockDepth: bc.currentBlockDepth,
\t\t\t\tregion:     region,
\t\t\t\torigin:     origin,
\t\t\t}
\t\t\treturn
\t\t}

\t\td := bc.reportBorrow(origin, CodeSpanOverlap,
\t\t\tfmt.Sprintf("writable span %q may overlap existing writable access to %q", borrowName, ownerName))
\t\td.AddNote(fmt.Sprintf("requested region: %s", describeRegion(region)))
\t\tif conflictName != "" {
\t\t\tbc.addBorrowContext(d, conflictName, conflict,
\t\t\t\tfmt.Sprintf("existing span %q covers %s", conflictName, describeRegion(conflict.region)))
\t\t}
\t\tif region == nil || (conflictName != "" && conflict.region == nil) {
\t\t\td.AddNote("Oak could not prove the writable regions are disjoint, so it rejects the alias conservatively")
\t\t}
\t\td.AddHelp("split the owner into statically disjoint regions before taking multiple writable spans")
\t\treturn
\t}

\tif state == SharedRead {
\t\td := bc.reportBorrow(origin, CodeSpanConflictsWithView,
\t\t\tfmt.Sprintf("writable span %q cannot be created while %q has read-only views", borrowName, ownerName))
\t\tif existingName, info, ok := bc.firstActiveBorrow(ownerName, BorrowView); ok {
\t\t\tbc.addBorrowContext(d, existingName, info,
\t\t\t\tfmt.Sprintf("read-only view %q is still active", existingName))
\t\t}
\t\td.AddHelp("finish using the views before requesting writable access")
\t\treturn
\t}

\tif state == Free {
\t\tbc.ownerStates[ownerName] = UniqueWrite
\t}
\tbc.ownerOf[borrowName] = ownerName
\tbc.activeBorrows[borrowName] = borrowInfo{
\t\towner:      ownerName,
\t\tkind:       BorrowSpan,
\t\tblockDepth: bc.currentBlockDepth,
\t\tregion:     region,
\t\torigin:     origin,
\t}
}'''
replace_once(old_span, new_span, "span conflict diagnostics")

replace_once(
'''\tbc.activeBorrows[subsliceName] = borrowInfo{
\t\towner:      sourceInfo.owner,
\t\tkind:       sourceInfo.kind,      // Subslice preserves view/span kind
\t\tblockDepth: bc.currentBlockDepth, // Use current block depth, not source depth
\t\tregion:     region,
\t}''',
'''\tbc.activeBorrows[subsliceName] = borrowInfo{
\t\towner:      sourceInfo.owner,
\t\tkind:       sourceInfo.kind,      // Subslice preserves view/span kind
\t\tblockDepth: bc.currentBlockDepth, // Use current block depth, not source depth
\t\tregion:     region,
\t\torigin:     sourceInfo.origin,
\t}''',
"subslice origin inheritance",
)

path.write_text(text)
