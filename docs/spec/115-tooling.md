# The oak command

Status: normative for the command-line interface; the compiler, module
system, test runner, and REPL it drives are specified in their own chapters
(`83-modules.md`, `82-package-semver.md`, `110-testing.md`, `85-discipline.md`).

## 1. Shape

One binary, the shape of the Go tool:

```text
oak <command> [flags] [arguments]
oak help [command]
```

`oak` with no arguments starts the REPL; `oak file.oak` compiles one file to
C beside it (the original single-file mode). Flags precede positional
arguments and every command answers `-h` with its usage and flags; an unknown
flag is a usage error. **Package patterns**: where a command takes package
directories, `./...` and `dir/...` expand to every package under the
directory — the module's packages when an `oak.mod` is above it, otherwise
every directory holding `.oak` files (hidden, `vendor`, and `testdata`
directories excluded) — so `oak build ./...`, `oak vet ./...`, `oak list
./util/...`, `oak fmt -l ./...`, and `oak test ./...` do what their Go
counterparts do. `oak run [dir] -- args` passes everything after `--` to the
program. Every command exits 0 on success, 1 on a failed check or build, 2
on a usage error. Every command is offline unless this chapter says otherwise;
external programs (the C compiler, Lean) are invoked with fixed argument lists
and never through a shell; nothing is written outside the paths a command
names or the module cache.

| Command | Go counterpart | What it does |
|---|---|---|
| `oak build [-o out] [-emit-c] [-header out.h] [-lean out.lean] [-profile p] [-lines] [dir\|file.oak]` | `go build` | Compile a package (or one file) to an **executable**, named after the package directory unless `-o` says otherwise. `-emit-c`, or an `-o` ending in `.c`, writes the C instead. `-header` and `-lean` write the exported C header and the Lean extraction alongside. |
| `oak run [-profile p] [dir]` | `go run` | Build into a temporary directory and run with this process's stdio; the program's exit status is propagated. |
| `oak install [-profile p] [dir]` | `go install` | Build the executable into `$OAKBIN` (default `$HOME/.oak/bin`), named after the package directory. |
| `oak vet [-profile p] [dir\|file.oak]` | `go vet` | Run every semantic gate without generating code and print what the checker recorded: errors, and the assumptions it could not discharge (the same list as the REPL's `:obligations`). |
| `oak test [flags] [dir]` | `go test` | Run the package's tests (`110-testing.md`). |
| `oak doc [-package P] [dir] [name]` | `go doc` | The public declarations of the module's packages (or one package) with their canonical types, from the API snapshot; a name filters. |
| `oak fmt [-l] [-w] [file\|dir]...` | `gofmt` | Canonicalize whitespace: CRLF to LF, trailing whitespace removed, blank-line runs collapsed, one final newline. A file is rewritten only when the result parses to the same syntax tree, so formatting cannot change meaning; a file that does not parse is reported and left alone. `-l` lists, `-w` writes, neither prints. Layout-sensitive indentation is never touched. |
| `oak list [-json] [-deps] [dir]` | `go list` | The packages of the module with their imports; `-deps` includes every package a build reaches (dependencies and standard library), `-json` emits one object per package with `path`, `dir`, `module`, `imports`. |
| `oak mod ...` | `go mod` | Module maintenance, section 2. |
| `oak clean -modcache` | `go clean -modcache` | Empty the module cache. Only an explicit `$OAKMODCACHE` that is a directory is touched; the tool never guesses a location to delete. |
| `oak env [NAME...]` | `go env` | Print the environment oak reads: `OAKMODCACHE`, `OAKBIN`, `OAK_LEAN_DIR`, and the derived `OAKROOT` (the module root of the working directory). |
| `oak repl` | — | The interactive session (`83-modules.md` section 10). |
| `oak version` | `go version` | The module version and VCS revision the Go toolchain recorded in the binary. |
| `oak help [command]` | `go help` | Usage. |
| `oak completion bash\|zsh\|fish` | — | A shell completion script generated from the command tables; nothing from the invocation is interpolated. |

## 2. Module maintenance

| Subcommand | Go counterpart | Chapter |
|---|---|---|
| `oak mod init <module-path> [dir]` | `go mod init` | Create `oak.mod` with `module` and `oak` directives; refuses to overwrite and rejects standard-library paths. |
| `oak mod download [dir]` | `go mod download` | Fetch pinned requirements into the cache, verifying digests and carried `api.json` (`83-modules.md` 4.4). **Network.** |
| `oak mod tidy [-w] [dir]` | `go mod tidy` | Reconcile `require` directives with imports (`83-modules.md` 4.5). |
| `oak mod edit [-require p@v] [-droprequire p] [-replace p=>dir] [-dropreplace p] [-version v] [-profile p] [dir]` | `go mod edit` | Rewrite directives line by line; the result must parse (a `replace` without its `require` is rejected, as always); `-droprequire` also drops the module's `replace`. |
| `oak mod vendor [dir]` | `go mod vendor` | Copy the dependency modules a build would locate (replace directives, then the cache, at the versions minimal version selection picks) into `vendor/<module path>/` — regular `.oak` files, `oak.mod`, `api.json` only, every destination checked to lie under `vendor/` — and write `vendor/modules.txt`. A vendored module takes precedence over replace directives and the cache when the loader locates it (`83-modules.md` 4.3), so the tree builds with neither. |
| `oak mod verify [dir]` | `go mod verify` | Every download writes a record beside the cached module (`.oakdigest`: the verified archive digest and a hash over the extracted files). `verify` recomputes the tree hash of each cached requirement and reports `modified`, `missing`, or `unrecorded` entries. |
| `oak mod graph [dir]` | `go mod graph` | The requirement graph reachable from the module, one `module requirement@version` line per edge, root first, following `replace` directives and the cache. |
| `oak mod why <import-path> [dir]` | `go mod why` | For each package of the module that reaches the path, a shortest import chain. |
| `oak mod api`, `diff`, `bump`, `compat`, `pack`, `upgrade`, `try` | — | API snapshots and semver (`82-package-semver.md` sections 6–8). |

## 3. Environment

| Variable | Meaning |
|---|---|
| `OAKMODCACHE` | The module cache, `<cache>/<path>@v<version>`. Unset means dependencies resolve only through `replace` directives; `oak mod download` and `oak clean -modcache` require it. |
| `OAKBIN` | Where `oak install` puts executables. Default `$HOME/.oak/bin`, created on demand. |
| `OAK_LEAN_DIR` | The `spec/lean` directory for the REPL's `:lean check`; default: found above the working directory. |

## 4. Not provided, and why

- `oak get` — Oak has no registry and the compiler never fetches. Adding a
  dependency is `oak mod edit -require path@version` (or a pinned `require`
  line with a location and digest) followed by `oak mod download`.
- A pretty-printing `oak fmt` — the whitespace canonicalizer above is what a
  layout-sensitive syntax admits safely; reflowing tokens needs a
  comment-preserving printer for both surfaces, recorded as direction.
- `oak generate`, `oak work`, `oak fix` — no counterpart yet.
