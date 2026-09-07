# Atomicity, Consistency, Isolation, Durability

ACID is a database acronym, but each letter names a *ladder* that systems
code climbs rung by rung — and a systems language must take a position on
each. Oak's positions are unusually explicit: three of the four ladders
are enforced by machinery that already exists in this repository, and the
fourth is deliberately delegated with stated support.

Each letter has its own hierarchy page:

- **[Atomicity](atomicity.md)** — what is indivisible: from nothing, to a
  machine word, to constructed protocols; why transactions are not a
  primitive.
- **[Consistency](consistency.md)** — two ladders that share a name: the
  ordering models (eventual → consistent prefix → causal → snapshot →
  sequential → linearizable) and the invariant-obligation ladder (types →
  checkers → assertions → proofs).
- **[Isolation](isolation.md)** — read uncommitted through serializable,
  and why the borrow checker is a static isolation-level scheduler with
  predicate locks.
- **[Durability](durability.md)** — from "gone at power loss" to
  quorum-replicated, and what a language can honestly contribute to a
  storage protocol's rungs.

The composition rule across all four: **name your rung.** Most concurrency
and storage bugs are not failures to implement a rung — they are programs
standing on a lower rung than the invariant they claim. The ladders exist
so the claim can be written down, reviewed, and (increasingly) checked.
