# Middle-stair conjecture in parallel chip-firing

[![Lean verification](https://github.com/NathanLannanDotCom/middle-stair-paper/actions/workflows/lean.yml/badge.svg)](https://github.com/NathanLannanDotCom/middle-stair-paper/actions/workflows/lean.yml)

This public repository accompanies a candidate proof of the middle-stair
conjecture for parallel chip-firing. Independent review of both the
mathematics and the novelty claim is requested.

## Read first

- **[Compiled paper (PDF)](output/pdf/middle-stair.pdf)**
- [How to review the argument](review/REVIEWING.md)
- [Proof-to-Lean map](review/PROOF_MAP.md)
- [Prior art and novelty status](review/PRIOR_ART.md)
- [LaTeX source](paper/main.tex) and [bibliography](paper/references.bib)

## Main claim

Let `G=(V,E)` be a finite connected simple graph. If a nonnegative integral
chip configuration `sigma` satisfies

```text
2|E|-|V| < |sigma| < 2|E|,
```

then its least eventual state period under deterministic synchronous
degree-threshold parallel chip-firing is exactly two.

Ji, Li, and Wang state this as Conjecture 2 in
[arXiv:2408.10508v2](https://arxiv.org/abs/2408.10508v2). The proposed new
ingredient is a low-activity density inequality: a returning orbit with
activity below one half has at most `2|E|-|V|` chips. The complement argument
and the final nonclumpiness step use established ideas.

## Review requested

The most useful feedback would address these questions:

1. Is the selected-prefix proof of the density inequality correct?
2. Is the Jiang-Scully-Zhang nonclumpiness theorem applied with the right
   cyclic convention?
3. Is the density inequality already known under another name or as a routine
   consequence of prior work?
4. Does the result merit a paper, a short note, or only communication to the
   conjecture authors?

The [review notes](review/REVIEWING.md) give a short reading order and the
precise claim boundary.

## Verify the Lean development

Requirements are Git, Elan/Lake, and network access for the first dependency
fetch. The Lean toolchain and mathlib dependency are pinned. From a clone of
this repository:

```text
cd formal
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

The terminal declaration is:

```lean
MiddleStair.middle_stair_least_eventual_period_two
```

The project contains no `sorry`, `admit`, or declared project axiom. The axiom
audit reports only `propext`, `Classical.choice`, and `Quot.sound`. GitHub
Actions runs the build and axiom audit on every change to `main` and on pull
requests. Windows users may instead run
[`scripts/verify-formal.ps1`](scripts/verify-formal.ps1).

To rebuild the PDF on Windows, run
[`scripts/build-paper.ps1`](scripts/build-paper.ps1). It uses Tectonic from
`PATH` when available and otherwise downloads the official Tectonic 0.16.9
Windows release into an ignored local directory.

## Repository layout

```text
paper/    manuscript source and bibliography
output/   compiled review PDF
formal/   standalone Lean 4 project containing the theorem dependency closure
review/   review instructions, proof map, and prior-art assessment
scripts/  reproducibility helpers
```

Formal verification establishes correctness relative to the encoded
definitions and imported foundations. It does not establish mathematical
originality, significance, or fidelity to the conventional model; those are
the reasons for specialist review.

## Authors and contact

The manuscript lists OpenAI Codex (GPT-5.6 Sol) first and Nathan Lannan second.
Nathan Lannan has no institutional affiliation and can be contacted at
[nathan@nathanlannan.com](mailto:nathan@nathanlannan.com). Feedback may also be
left through [GitHub Issues](https://github.com/NathanLannanDotCom/middle-stair-paper/issues).

No reuse license has been selected. Public availability permits inspection and
review but does not add a license grant.
