# Verification record

Run on 13 July 2026, America/New_York.

## Environment

- Lean 4.31.0, toolchain commit `68218e876d2a38b1985b8590fff244a83c321783`
- Lake 5.0.0
- mathlib v4.31.0, commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`
- Tectonic 0.16.9
- Poppler renderer from the bundled Codex PDF runtime
- Windows host

## Lean result

The source project first completed an independent full build of the same
twelve-module closure. The focused handoff project was then replayed against
that exact pinned dependency checkout. The final checks were:

```text
lake --no-build build                 exit 0
lake env lean AxiomAudit.lean         exit 0
```

The terminal theorem is
`MiddleStair.middle_stair_least_eventual_period_two`. The axiom audit reported
only:

```text
propext
Classical.choice
Quot.sound
```

The finite theorem
`MiddleStair.Mischief.reducedCost_nonnegative` depends only on `propext` and
`Quot.sound`.

The build emits style and unused-variable linter warnings. It emits no proof
error. An initial attempt to compile all mathlib dependencies locally without
the release cache hit Windows file-I/O failures under high parallel load; this
was a dependency-build environment issue, not a failure in a paper module. The
repository script therefore runs mathlib's standard `lake exe cache get`
before building.

## Source checks

- Focused formal SHA-256 manifest: pass.
- Search for `sorry`, `admit`, or declared project axioms: no proof holes. A
  prose comment in `Nonclumpy.lean` contains the phrase `project axiom` only to
  say that none is used.
- The import root contains only `Universal` and `TransientCounterexample`.
- Diamond-tail modules are absent from the formal snapshot.

## Paper checks

- Tectonic build: exit 0.
- Undefined citations or references: none.
- Overfull or underfull boxes: none reported.
- PDF pages: 6, US Letter, unencrypted.
- All six pages rendered to 144 dpi PNG and visually inspected.
- No clipping, overlap, broken equations, or unreadable references observed.

Final artifact hashes at the time of this record:

```text
ffd06f39727c5237babaa4ec4f435ad1068ac3317a23efb97e8cdebfaf91d5a6  output/pdf/middle-stair.pdf
af5d34137be90508e51f64b5f3688e18e1cd8e7ee8385e704c12b1c95d1e08e2  paper/main.tex
d2c3bb05a4b731c6a21274f060d09d3f1f2fb2163dd7824048c59dacf334ff61  paper/references.bib
```

## Authorship display check

The title page visibly lists:

1. OpenAI Codex (GPT-5.6 Sol)
2. Nathan Lannan, `nathan@nathanlannan.com`, no institutional affiliation

The footer note records the model slug `gpt-5.6-sol` and the fact that the
exact runtime build identifier was not exposed.
