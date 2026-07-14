# Claim boundary

## What the paper proves

For deterministic synchronous degree-threshold parallel chip-firing on a
finite connected simple graph `G=(V,E)`, every nonnegative integer
configuration with

```text
2|E|-|V| < total chips < 2|E|
```

has least eventual state period exactly two.

The proof establishes a stronger intermediate statement for any returning
orbit:

- activity below `1/2` implies at most `2|E|-|V|` chips;
- activity above `1/2` and below `1` implies at least `2|E|` chips.

These inequalities force activity `1/2` in the strict band. Known
nonclumpiness then forces alternating firing.

## What it does not prove

- Period two from time zero. The path state `(0,0,2)` has a two-step transient.
- Any assertion at either endpoint. The configurations `deg(v)-1` and
  `deg(v)` are fixed at totals `2|E|-|V|` and `2|E|`.
- A sharp or useful upper bound on transient length.
- Results for directed, weighted, stochastic, infinite, or multigraph models.
- Results for configurations with negative chips.
- A new algorithm, optimization method, compression primitive, or AI
  technique.
- The separate diamond-tail transient result.
- Publication priority or novelty.

## Dependency boundary

The graph-independent low-activity density lemma is the proposed new
mathematical ingredient. The following are prior ideas or routine deductions:

- finite-state recurrence;
- equality of vertex firing counts on a returning connected orbit;
- the affine complement `2 deg(v)-1-sigma(v)`;
- Jiang-Scully-Zhang nonclumpiness; and
- alternation and two-step return once activity `1/2` is known.

The paper cites the prior dependencies rather than presenting them as new.

## Three distinct standards of confidence

1. **Formal correctness.** Lean verifies the encoded terminal theorem from
   mathlib foundations and the included formal nonclumpiness argument.
2. **Mathematical correctness.** A human must verify that the definitions,
   cyclic indexing, and formalized published dependency match conventional
   mathematics.
3. **Originality and significance.** Neither follows from formal correctness.
   Targeted literature review and specialist judgment remain necessary.

## Main failure modes to look for

- a hidden mismatch between selected cyclic phases and integer representatives;
- an illegitimate sum of inequalities evaluated at different times;
- a missing condition in the periodic upper-box complement argument;
- a stronger formulation of the density lemma already in the literature; or
- a mismatch between the paper's nonclumpiness statement and the hypotheses of
  Jiang-Scully-Zhang Theorem 6.2.
