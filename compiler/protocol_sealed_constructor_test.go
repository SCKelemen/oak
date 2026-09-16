package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

const sealedConstructorProtocol = `
Seal: protocol = {
	data {
		uses: u8
	}
	init {
		uses: u8(0)
	}
	initial Ready
	advance: Ready -> Used when data.uses == u8(0) then {
		data.uses = data.uses + u8(1)
	}
	reset: Used -> Ready
}
`

func checkSealedConstructorProgram(name string, body string) error {
	_, err := New().WithSource(name+".oak", sealedConstructorProtocol+body).Check().Get()
	return err
}

func TestProtocolSealedInitialConstructionRejected(t *testing.T) {
	tests := []struct {
		name string
		body string
	}{
		{
			name: "direct literal",
			body: `
main: (): i32 = {
	handle: Seal[SealReady] = Seal { data: seal_initial_data() }
	0
}
`,
		},
		{
			name: "literal reassignment",
			body: `
main: (): i32 = {
	handle: Seal[SealReady] = seal_handle()
	handle = Seal { data: seal_initial_data() }
	0
}
`,
		},
		{
			name: "nested literal",
			body: `
Box: type = struct {
	handle: Seal[SealReady]
	tag: u8
}

main: (): i32 = {
	box: Box = Box {
		handle: Seal { data: seal_initial_data() },
		tag: u8(0),
	}
	0
}
`,
		},
		{
			name: "uninitialized handle",
			body: `
main: (): i32 = {
	handle: Seal[SealReady]
	0
}
`,
		},
		{
			name: "uninitialized aggregate",
			body: `
Box: type = struct {
	handle: Seal[SealReady]
	tag: u8
}

main: (): i32 = {
	box: Box
	0
}
`,
		},
		{
			name: "uninitialized nested array",
			body: `
Vault: type = struct {
	handles: [2]Seal[SealReady]
}

main: (): i32 = {
	vault: Vault
	0
}
`,
		},
		{
			name: "uninitialized fixed array",
			body: `
main: (): i32 = {
	handles: [2]Seal[SealReady]
	0
}
`,
		},
		{
			name: "fixed array nested literal",
			body: `
main: (): i32 = {
	handles: [2]Seal[SealReady] = [
		Seal { data: seal_initial_data() },
		seal_handle(),
	]
	0
}
`,
		},
		{
			name: "global direct literal",
			body: `
global_handle: Seal[SealReady] = Seal { data: seal_initial_data() }

main: (): i32 = 0
`,
		},
		{
			name: "global nested literal",
			body: `
GlobalBox: type = struct {
	handle: Seal[SealReady]
	tag: u8
}

global_box: GlobalBox = GlobalBox {
	handle: Seal { data: seal_initial_data() },
	tag: u8(0),
}

main: (): i32 = 0
`,
		},
		{
			name: "global uninitialized handle",
			body: `
global_handle: Seal[SealReady]

main: (): i32 = 0
`,
		},
		{
			name: "global uninitialized aggregate",
			body: `
GlobalVault: type = struct {
	handles: [2]Seal[SealReady]
}

global_vault: GlobalVault

main: (): i32 = 0
`,
		},
		{
			name: "deep aggregate beyond resource path cutoff",
			body: `
Deep9: type = struct { handle: Seal[SealReady] }
Deep8: type = struct { next: Deep9 }
Deep7: type = struct { next: Deep8 }
Deep6: type = struct { next: Deep7 }
Deep5: type = struct { next: Deep6 }
Deep4: type = struct { next: Deep5 }
Deep3: type = struct { next: Deep4 }
Deep2: type = struct { next: Deep3 }
Deep1: type = struct { next: Deep2 }
Deep0: type = struct { next: Deep1 }

main: (): i32 = {
	root: Deep0
	0
}
`,
		},
		{
			name: "local constructor name spoof",
			body: `
main: (): i32 = {
	seal_handle: (): Seal[SealReady] = Seal { data: seal_initial_data() }
	forged: Seal[SealReady] = seal_handle()
	0
}
`,
		},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			err := checkSealedConstructorProgram("sealed_"+test.name, test.body)
			expectCode(t, test.name, err, typechecker.CodeResourceTypestateConstruction)
		})
	}
}

func TestProtocolSealedConstructorAndTransitionsAccepted(t *testing.T) {
	err := checkSealedConstructorProgram("sealed_constructor_accepted", `
make_seal: (): Seal[SealReady] = seal_handle()

main: (): i32 = {
	direct: Seal[SealReady] = seal_handle()
	wrapped: Seal[SealReady] = make_seal()
	moved: Seal[SealReady] = direct
	outcome: SealAdvanceOutcome = seal_advance(moved)
	outcome ?
	| .ToUsed(used) => {
		ready: Seal[SealReady] = seal_reset(used)
		0
	}
	| .Refused(still_ready) => {
		still_ready.data.uses
		0
	}
}
`)
	if err != nil {
		t.Fatalf("generated constructor, wrapper, move, and guarded/cyclic transitions should check: %v", err)
	}
}

func TestProtocolSealedTransitionConsumesAliases(t *testing.T) {
	err := checkSealedConstructorProgram("sealed_transition_consumes_aliases", `
main: (): i32 = {
	handle: Seal[SealReady] = seal_handle()
	moved: Seal[SealReady] = handle
	outcome: SealAdvanceOutcome = seal_advance(moved)
	stale: u8 = handle.data.uses
	0
}
`)
	expectCode(t, "transition consumes aliases", err, typechecker.CodeResourceUsedAfterConsume)
}

func TestProtocolExplicitResourceInitialLiteralRemainsAccepted(t *testing.T) {
	_, err := New().WithSource("explicit_resource_initial_literal.oak", `
Handle: type = struct {
	id: u32
}

close_handle: (handle: Handle): () = {}

Lifecycle: protocol = {
	resource Handle
	initial Open
	close: Open -> Closed via close_handle
}

main: (): i32 = {
	handle: Handle = Handle { id: u32(7) }
	0
}
`).Check().Get()
	if err != nil {
		t.Fatalf("explicit-resource initial literals should remain accepted: %v", err)
	}
}
