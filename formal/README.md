# Focused Lean verification

This directory is a standalone Lean 4 project for the paper theorem and the
three-vertex time-zero counterexample. It intentionally omits the unrelated
diamond-tail transient modules.

## Pinned environment

- Lean 4.31.0
- Lake 5.0.0
- mathlib v4.31.0

The exact mathlib dependency graph is recorded in `lake-manifest.json`.

## Build

```powershell
lake -KmaxJobs=1 build
lake env lean AxiomAudit.lean
```

The second command prints the axiom dependencies of the main declarations.
The expected nonempty set is limited to `propext`, `Classical.choice`, and
`Quot.sound`, the ordinary logical foundations used through Lean/mathlib.

## Main declaration

```lean
theorem MiddleStair.middle_stair_least_eventual_period_two
    (hG : G.Connected) (sigma : Configuration V)
    (hnonnegative : forall v, 0 <= sigma v)
    (hbandLow :
      2 * (G.edgeFinset.card : Int) - (Fintype.card V : Int) < totalChips sigma)
    (hbandHigh : totalChips sigma < 2 * (G.edgeFinset.card : Int)) :
    HasLeastEventualPeriod G sigma 2
```

The import root `MiddleStair.lean` contains only the theorem and its
counterexample dependency closure. `AxiomAudit.lean` contains no theorem
assumptions; `#print axioms` is a diagnostic command.

## Trust boundary

Lean checks that the declarations follow from their encoded definitions and
the imported mathlib foundations. A human reviewer must still check that:

- the encoded update is the intended parallel chip-firing rule;
- the cyclic nonclumpiness formalization matches Jiang-Scully-Zhang;
- the theorem statement matches the conjecture in the literature; and
- the paper proof faithfully explains the formal argument.

See `../handoff/PROOF_TO_LEAN_MAP.md` for the exact correspondence.
