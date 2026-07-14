# The middle stair in parallel chip-firing

This is a private specialist-review bundle for a proposed proof of the
middle-stair conjecture in parallel chip-firing. The central claim is:

> If `G=(V,E)` is a finite connected simple graph and a nonnegative integral
> configuration `sigma` satisfies
> `2|E|-|V| < |sigma| < 2|E|`, then its least eventual state period is two.

Ji, Li, and Wang state this as Conjecture 2 in
[arXiv:2408.10508v2](https://arxiv.org/abs/2408.10508v2). The targeted
literature search recorded here found no later resolution, but priority and
novelty remain unconfirmed pending specialist and database review.

## Start here

- [Compiled paper](output/pdf/middle-stair.pdf)
- [LaTeX source](paper/main.tex)
- [Reviewer guide](handoff/REVIEWER_GUIDE.md)
- [Claim boundary](handoff/CLAIM_BOUNDARY.md)
- [Proof-to-Lean map](handoff/PROOF_TO_LEAN_MAP.md)
- [Novelty and prior art](handoff/NOVELTY_AND_PRIOR_ART.md)
- [Before-sending checklist](BEFORE_SENDING.md)

The paper's technical center is the low-activity density inequality. The
other main ingredients are recurrence and equal firing counts, the established
affine complement, and Jiang-Scully-Zhang nonclumpiness.

## Repository contents

```text
paper/       LaTeX manuscript and bibliography
output/pdf/  review-ready compiled paper
formal/      focused Lean 4 project for the paper theorem
handoff/     reviewer instructions, claim limits, and unsent email drafts
checks/      reproducibility and provenance records
scripts/     PowerShell build and verification scripts
supplement/  work deliberately excluded from the paper
```

The repository deliberately excludes experiments, demos, broad application
claims, and the conditional diamond-tail transient project. They do not
strengthen the central paper.

## Reproduce the Lean result

Requirements: Git, Elan/Lake, and network access for the first dependency
fetch. The toolchain and mathlib revision are pinned.

```powershell
Set-Location formal
lake -KmaxJobs=1 build
lake env lean AxiomAudit.lean
```

On Windows, [scripts/verify-formal.ps1](scripts/verify-formal.ps1) also finds
Lake through `$HOME\.elan\bin` when it is not on `PATH`.

The terminal declaration is:

```lean
MiddleStair.middle_stair_least_eventual_period_two
```

## Rebuild the paper

```powershell
.\scripts\build-paper.ps1
```

The script uses a local Tectonic installation if available. Otherwise it
downloads the pinned official Tectonic 0.16.9 Windows binary into the ignored
`.tools/` directory. The final PDF is written to `output/pdf/`.

## Status

- Mathematical proof: complete candidate, independently checked against Lean.
- Lean: clean build; no `sorry`, `admit`, or project axiom.
- Novelty: plausible but provisional.
- Listed authors: OpenAI Codex (GPT-5.6 Sol), first; Nathan Lannan, second.
- Human affiliation and contact details: not yet supplied.
- Public submission or author contact: not performed by this repository build.
- License: not yet selected; see [LICENSE_STATUS.md](LICENSE_STATUS.md).

Formal verification is evidence of correctness relative to the encoding. It
does not establish originality, significance, or fidelity of every
formalization choice to the published literature. Those are the requested
tasks for the specialist reviewer.
