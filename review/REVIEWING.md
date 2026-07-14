# Reviewing this candidate proof

## Review question

Please assess one narrow question:

> Is the proposed proof of the middle-stair conjecture mathematically correct,
> apparently new, and worth developing into a short paper?

The theorem is checked in Lean, but this is not a request for a Lean code
review alone. The main unresolved issue is originality, especially whether the
low-activity density inequality is already known in parallel chip-firing,
fixed-energy sandpile, or rotation-number terminology.

## Efficient reading order

1. Read the abstract and Theorem 1.1 in the
   [compiled paper](../output/pdf/middle-stair.pdf).
2. Read Lemma 3.1, the selected-prefix low-activity density bound, in full.
3. Check Lemma 4.1, where affine complementation gives the high-activity bound.
4. Check the activity-one-half and alternation argument in Section 5.
5. Consult [PRIOR_ART.md](PRIOR_ART.md) for the novelty boundary.
6. Use [PROOF_MAP.md](PROOF_MAP.md) to inspect the corresponding Lean
   declarations.

## Exact claim boundary

For deterministic synchronous degree-threshold parallel chip-firing on a
finite connected simple graph, the paper claims that every nonnegative integer
configuration with

```text
2|E|-|V| < total chips < 2|E|
```

has least eventual state period exactly two.

The proof also gives the following bounds for a returning orbit:

- activity below `1/2` implies at most `2|E|-|V|` chips;
- activity above `1/2` and below `1` implies at least `2|E|` chips.

It does **not** claim:

- period two from time zero;
- either endpoint of the chip-count interval;
- a useful upper bound on transient length;
- directed, weighted, stochastic, infinite, or multigraph variants;
- configurations with negative chips;
- a new algorithm or applied computational technique; or
- publication priority.

The path configuration `(0,0,2)` supplies a formally checked example showing
why “eventual” is necessary. The endpoint configurations `deg(v)-1` and
`deg(v)` show why the strict inequalities cannot simply be closed.

## New ingredient versus dependencies

The candidate new ingredient is the graph-independent low-activity density
inequality. Finite-state recurrence, equal firing counts on a connected
returning orbit, the affine complement, and Jiang-Scully-Zhang
nonclumpiness are prior ideas or routine deductions. Once activity one half is
known, alternation and two-step return are short consequences.

## Questions worth checking closely

- May one choose a different centered-prefix minimum at each vertex and then
  sum the resulting coordinate inequalities?
- For an edge `{v,w}`, does the argument correctly derive
  `T K_vw <= 2q < T`, and hence the integral inequality `K_vw <= 0`?
- Does `q<T` put every coordinate of a returning orbit in the box required for
  affine complementation?
- Does Jiang-Scully-Zhang Theorem 6.2 apply with the same cyclic boundary
  convention and with an arbitrary return length rather than a least period?
- Does balanced nonclumpiness force vertexwise alternation as claimed?
- Does the last step prove least eventual state period, rather than only a
  firing-word period?
- Is the low-activity density inequality known through a potential,
  rotation-number, motor, or fixed-energy-sandpile result?

## Formal check and trust boundary

From `formal/`, run:

```text
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

The terminal result is
`MiddleStair.middle_stair_least_eventual_period_two`. There are no proof-hole
placeholders or project axioms. The finite nonclumpiness certificate is
kernel-checked, but a human should still compare its sector and local-state
encoding with the published Jiang-Scully-Zhang argument.

Three standards should remain separate:

1. Lean checks the result relative to the encoded definitions.
2. A mathematical reviewer checks that those definitions and arguments match
   the conventional game and cited theorem.
3. Literature review and specialist judgment determine originality and
   significance.

Feedback may be sent to [Nathan Lannan](mailto:nathan@nathanlannan.com) or
left in a [GitHub issue](https://github.com/NathanLannanDotCom/middle-stair-paper/issues).
