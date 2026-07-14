# Prior art and novelty status

Status checked 13 July 2026. This is a targeted search record, not a proof of
priority.

## Exact conjecture source

David Ji, Michael Li, and Daniel Wang, *Non-Stabilizing Parallel Chip-Firing
Games*, [arXiv:2408.10508v2](https://arxiv.org/abs/2408.10508v2), revised 24
August 2024, state as Conjecture 2 that every configuration in

```text
2|E|-|V| < |sigma| < 2|E|
```

has period two. Their convention shifts an orbit to its periodic part, so the
paper's phrase `least eventual state period` is the appropriate explicit
formulation. Version 2 remains the latest official arXiv version found; no
later arXiv revision was found during the recorded search.

Their paper proves general exclusions of periods three and four and handles
special graph classes. Its balanced complete-bipartite statement contains an
apparent range inconsistency between Theorem 3 and its proof. This draft does
not rely on that special-case statement and cites Conjecture 2 directly.

## Central dependency

Tian-Yi Jiang, Ziv Scully, and Yan X. Zhang, *Motors and Impossible Firing
Patterns in the Parallel Chip-Firing Game*, SIAM Journal on Discrete
Mathematics 29(1), 615-630 (2015),
[DOI 10.1137/130933770](https://doi.org/10.1137/130933770), prove in Theorem
6.2 that clumpy periodic firing patterns do not occur. A cyclic binary word is
clumpy if it contains both consecutive zeroes and consecutive ones. At
activity one half, their theorem forces alternation.

The earlier proceedings version is Ziv Scully, Tian-Yi Jiang, and Yan Zhang,
*Firing Patterns in the Parallel Chip-Firing Game*, FPSAC 2014,
[DOI 10.46298/dmtcs.2421](https://doi.org/10.46298/dmtcs.2421).

## Other relevant prior art

- Javier Bitar and Eric Goles, *Parallel Chip Firing Games on Graphs*,
  Theoretical Computer Science 92(2), 291-300 (1992),
  [DOI 10.1016/0304-3975(92)90316-8](https://doi.org/10.1016/0304-3975(92)90316-8).
- Tian-Yi Jiang, *On the Period Lengths of the Parallel Chip-Firing Game*,
  [arXiv:1003.0943v2](https://arxiv.org/abs/1003.0943v2). This includes the
  equal-firing-count return criterion and affine complement.
- Lionel Levine, *Parallel Chip-Firing on the Complete Graph: Devil's
  Staircase and Poincare Rotation Number*, Ergodic Theory and Dynamical
  Systems 31(3), 891-910 (2011),
  [DOI 10.1017/S0143385710000088](https://doi.org/10.1017/S0143385710000088).
- Alan Bu, Yunseo Choi, and Max Xu, *An Exact Bound on the Number of Chips of
  Parallel Chip-Firing Games That Stabilize*, Archiv der Mathematik 119(5),
  471-478 (2022),
  [DOI 10.1007/s00013-022-01777-3](https://doi.org/10.1007/s00013-022-01777-3).
- Luca Dall'Asta, *Exact Solution of the One-Dimensional Deterministic
  Fixed-Energy Sandpile*, Physical Review Letters 96, 058003 (2006),
  [DOI 10.1103/PhysRevLett.96.058003](https://doi.org/10.1103/PhysRevLett.96.058003).

## Provisional novelty assessment

Exact-phrase, arXiv, publisher, and citation searches found no later
independent resolution of the general conjecture. That supports, but does not
establish, novelty.

The most likely location of hidden prior art is the activity-density statement

```text
activity < 1/2  ==>  |sigma| <= 2|E|-|V|,
```

possibly expressed through rotation numbers, motors, fixed-energy sandpiles,
or a potential inequality. Once activity one half is known, the final theorem
is largely a consequence of Jiang-Scully-Zhang and is not the novel core.

## Minimum evidence before claiming priority or submitting

1. Search MathSciNet and zbMATH for work citing Ji-Li-Wang and for general
   activity-density inequalities after August 2024.
2. Ask at least one conjecture author whether the problem remains open and
   whether the selected-prefix lemma is known.
3. Ask a nonclumpiness specialist whether Theorem 6.2 is applied with the
   correct cyclic convention.
4. Compare the selected-prefix proof with Jiang's complement and return
   criteria and Levine's rotation-number framework.
5. Obtain a human line-by-line proof check independent of the Lean encoding.

Until these steps are complete, use `candidate proof` and avoid `first proof`
or an unconditional priority claim.
