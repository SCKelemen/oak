# Oak test

Build the CLI with `go build -o build/oak .` from the repository root. A host C
compiler (`cc` by default) is required. Then:

```sh
./build/oak test examples/testing
./build/oak test -list ./...
./build/oak test -run '^Property' -seed 42 -runs 1000 examples/testing
./build/oak test -sim '^SimTimerIrq$' -seed 42 -runs 1000 examples/testing
./build/oak test -fuzz '^FuzzUtf8$' -runs 10000 examples/testing
./build/oak test -json -runs 20 examples/testing
```

Flags precede directory arguments. Put tests in `*_test.oak` alongside the
production `.oak` sources they exercise:

```oak
import(testing)

TestAddition: (): () {
  test_check(u32(2) + u32(3) == u32(5), u32(1001))
}

PropertyRange: (data: []u8): () {
  state: [1]TestChoices
  choices: [*]TestChoices = span(&state)
  low: u32 = test_range(choices, data, u32(0), u32(100))
  high: u32 = test_range(choices, data, low, u32(200))
  test_check(low <= high, u32(1002))
}
```

A failure prints an exact replay command and saves its minimized input under
`testdata/oak/<TestName>/`. Keep useful failures in version control. Ordinary
runs execute the corpus before exploring new inputs. `-replay` checks the exact
build and expected failure; a reproduced failure still exits nonzero.

Use `testing_trace(id, a, b)` to record semantic actions or observations with a
stable `u32` event ID and two `u64` payloads. Failures retain the first 256 events
with an explicit truncation flag; the terminal prints the last eight retained
events. The saved trace describes the **minimized** input, and exact replay
compares both the failure and its recorded trace. JSON payloads are decimal
strings so tools can preserve every 64-bit value. Trace calls are no-ops in
libFuzzer exports; rerun a raw crash input with `oak test` to collect its trace.

`-timeout`, `-max-bytes`, `-max-discards`, `-shrink`, and `-shrink-timeout` make
campaign costs explicit. `-cover 1:10,2:1` requires sample counts for IDs emitted
by `testing_classify`. Rejected inputs never count as passes. Use `-sanitize`
when your C compiler supports address/undefined-behavior sanitizers.

For coverage-guided fuzzing:

```sh
./build/oak test -fuzz '^FuzzUtf8$' -emit-fuzz-harness build/fuzz.c examples/testing
clang -std=c11 -O1 -g -fsanitize=fuzzer,address,undefined \
  -fno-sanitize-recover=all build/fuzz.c -o build/fuzz
mkdir -p build/fuzz-corpus
./build/fuzz -max_len=256 -runs=100000 build/fuzz-corpus
```

Use a new output path for each export. libFuzzer executes many inputs in one
process, so reset all tested state per call. Copy useful libFuzzer crash files
to `testdata/oak/FuzzUtf8/*.bin` for the ordinary runner to replay.

Packages with `Sim` tests reject unsafe blocks, machine/atomic operations and
unlisted FFI across the whole package. For native OS components, use an explicit
adapter manifest with exact scalar ABI declarations and hash-pinned objects:

```sh
./build/oak test -adapter path/to/adapter.json -sim '^SimDevice$' path/to/tests
./build/oak test -adapter path/to/adapter.json -replay path/to/failure.json path/to/tests
```

The adapter itself is trusted code; the compiler does not prove its determinism.
Retain the original manifest and native archive for exact replay. Fuzz exports
also accept `-adapter`; link the archive explicitly alongside the exported C.

The [testing specification](../docs/spec/110-testing.md) records exact semantics
and limits. The event simulator is an explicit bounded foundation; whole-OS
simulation and automatic external-effect interception are not implemented.
