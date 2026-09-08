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

The [testing specification](../docs/spec/110-testing.md) records exact semantics
and limits. The event simulator is an explicit bounded foundation; whole-OS
simulation and automatic external-effect interception are not implemented.
