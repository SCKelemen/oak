# Production checker correspondence

The bounded experimental checker and the production certificate rung have
different implementations. Their proof boundaries must stay explicit.

| Implementation | Role | Current assurance |
| --- | --- | --- |
| `self_hosted_*.oak`, extracted into `OakTextExtracted.lean` | Bounded experimental ASCII checker | `OakVerification.Extraction.rup_text_check_sound_text` proves soundness of the extracted program under its size/fuel premises. Extractor/compiler fidelity remains assumed. |
| `experiments/verification-poc/internal/lrat` | Independent map-based Go reference | Compared with the executable Lean checker and compiled experimental Oak on the documented corpora. |
| Root `internal/lrat`, exposed through `prove/lrat.go` | Production text/word acceptance kernel | Go regressions, production Oak comparisons, and the shared-profile line-boundary gate below. No universal implementation-refinement theorem is claimed. |
| `prove/solver/lrat.oak` | Production Oak word checker | Compared with Go on the production certificate path. The experimental extraction theorem does not cover this source. |

## Line-boundary gate

Review of the production text scanner found a control-flow error:
`scanner.token` consumes a newline before returning no token, but `Check`
then called `skipLine` for both a blank line and a comment. After a blank
line this discarded the following line. A valid deletion could disappear,
and an invalid suffix after a refutation could be ignored.

The production loop now continues immediately for a blank line and calls
`skipLine` only after reading the comment marker. Unit regressions require
every addition/deletion to be counted, reject malformed and unjustified
suffixes even after a refutation, and reject use of a clause deleted after
a blank line. LF, CRLF, horizontal whitespace, comments, and EOF boundaries
are covered.

`TestProductionLineBoundaries` compares the production and independent Go
checkers on 483 cases (105 accepted, 378 rejected). Expected decisions and
accepted command counts come from explicit fixtures, not either checker.
The corpus inserts blank/comment lines at every boundary of each fixture
and varies its ending. It deliberately stays inside their shared ASCII
profile; it does not claim equality of their resource limits or complete
grammars.

The opt-in workflow exports the corpus using
`OAK_PRODUCTION_LRAT_CORPUS_OUT` and replays it with
`RUPTextCompare.lean`, whose acceptance path uses the proved executable
text checker. Its JSON adapter is outside the theorem. The production
kernel and both Go corpus checks run with the race detector.

This gate checks correspondence on the supplied cases. It is neither a
universal proof of the production scanner nor evidence that the experimental
theorem covers production storage, word decoding, or clause-ID remapping.

## Next proof obligations

1. Define the production word-record acceptance profile and a relation from
   its decoded initial clauses and commands to the certified stream model.
   Account explicitly for production capacities, IDs, and deletions rather
   than silently importing the experiment's bounds.
2. Relate the actual production Oak checker's array state and updates to that
   model, using extraction where supported; prove acceptance preservation.
   Text decoding and Go dense/sparse storage require their own connections.
3. Bind the checked initial formula to the exact obligation produced from
   the source. The source lowering, trap/claim roots, CNF construction, and
   serialization must each preserve the claim; a checked refutation alone
   does not establish that connection.

See [the verification-chain audit](../../../docs/spec/126-verification-chain.md)
for the remaining source, compiler, target, object, and execution assumptions.
