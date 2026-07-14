# Provenance

Snapshot assembled 13 July 2026 in the America/New_York time zone.

## Source

The mathematical and Lean source was selected from:

```text
D:\mathing\ji-li-wang-middle-stair
```

The review scope was restricted to files touched during the eight hours before
the repository audit. The central theorem modules were modified between
13:26 and 16:21 EDT on 13 July 2026 and therefore fell within that window.

The source repository's formal tree was untracked at the time of packaging, so
its existing Git commit does not identify this theorem. This new repository's
initial commit and the SHA-256 manifest in `checks/FORMAL_SHA256.md` are the
archival identity of the handoff snapshot.

## Selection and changes

The twelve central Lean modules were copied without mathematical changes:

- `Dynamics.lean`
- `PrefixMinimum.lean`
- `Orbit.lean`
- `Density.lean`
- `ComplementOrbit.lean`
- `Activity.lean`
- `Mischief.lean`
- `Nonclumpy.lean`
- `CyclicWrapper.lean`
- `Period.lean`
- `Universal.lean`
- `TransientCounterexample.lean`

The package import root was narrowed to `Universal` and
`TransientCounterexample`, and the axiom audit was narrowed accordingly. The
diamond-tail transient modules were omitted because they are not dependencies
of the paper theorem and their concrete certificate is incomplete.

The paper was rewritten as a focused conventional proof. The literature
metadata was checked against primary sources. The PDF was compiled with
Tectonic 0.16.9 and visually inspected after rendering all six pages to PNG.

## Authorship instruction

Nathan Lannan explicitly requested the byline order:

1. OpenAI Codex (GPT-5.6 Sol)
2. Nathan Lannan

The name `GPT-5.6 Sol` follows the current Codex model documentation; the
exact runtime build identifier was not exposed. See
`AUTHORSHIP_AND_AI_DISCLOSURE.md` for the nontraditional-authorship caveat.

## Actions not taken

No remote repository was created, no public push was made, no preprint was
posted, and no reviewer or conjecture author was contacted.
