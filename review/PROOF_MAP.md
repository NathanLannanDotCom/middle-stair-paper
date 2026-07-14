# Proof-to-Lean map

All line numbers refer to the focused snapshot in `formal/`. The dependency
order runs from top to bottom.

| Mathematical step | Lean source and declaration |
|---|---|
| Configuration and dynamics | `MiddleStair/Dynamics.lean`: `Configuration` (21), `laplacian` (29), `update` (72), `firingPrefix` (106), `evolve` (111), `complement` (141), `Fires` (170), `firingIndicator` (179), `step` (197) |
| Conservation and recurrence | `MiddleStair/Orbit.lean`: `totalChips` (94), `actualOrbit_eventually_periodic` (193) |
| Common firing count | `MiddleStair/Orbit.lean`: `laplacian_eq_zero_forces_constant` (306), `common_firing_count_of_period` (313), `common_actual_firing_count_bounds` (333) |
| Integral selected-prefix argument | `MiddleStair/PrefixMinimum.lean`: `scaledHeight` (15), `selected_minimum_forces_wait` (27), `edgeCharge` (39), `edgeCharge_scaled_bound` (47), `selected_edge_charge_nonpositive` (61) |
| Low-activity density inequality | `MiddleStair/Density.lean`: `LowActivityPeriodicOrbit` (35), `selected_waits` (129), `initial_le_degree_sub_one_add_laplacian` (167), `edge_charge_nonpositive` (186), `sum_directedCharge_nonpositive` (230), `low_activity_density` (281) |
| Periodic upper box and complement | `MiddleStair/ComplementOrbit.lean`: `returning_actual_cycle_upper` (138), `complement_actualOrbit_returns` (172), `actualFiring_complement` (182), `complementLowActivityOrbit` (276), `totalChips_complement` (307) |
| High-activity density inequality | `MiddleStair/ComplementOrbit.lean`: `high_activity_density_of_returning_actual` (325) |
| Strict band forces half activity | `MiddleStair/Activity.lean`: `returning_cycle_half_activity` (83) |
| Finite local mischief certificate | `MiddleStair/Mischief.lean`: `LocalState` (33), `reducedCost_nonnegative` (159), `sum_weight_nonnegative` (166) |
| Graph-level nonclumpiness | `MiddleStair/Nonclumpy.lean`: `NonclumpyWord` (43), `balanced_nonclumpy_word_alternates` (87), `cyclic_chipFiring_sector_invariant` (409), `cyclic_chipFiring_nonclumpy` (588) |
| Cyclic wrapper and alternation | `MiddleStair/CyclicWrapper.lean`: `cyclicActualWord_nonclumpy` (114), `cyclicActualWord_balanced_of_half` (157), `cyclicActualWord_alternates_of_half` (178), `actualFiring_one_eq_one_sub_zero_of_half` (211) |
| State-period definitions | `MiddleStair/Period.lean`: `HasEventualPeriod` (17), `HasLeastEventualPeriod` (22) |
| Two-step return and exclusion of one | `MiddleStair/Period.lean`: `actualOrbit_two_eq_of_firing_complement` (47), `not_hasEventualPeriod_one_of_middle_band` (64), `hasLeastEventualPeriod_two` (91) |
| Terminal assembly | `MiddleStair/Universal.lean`: `middle_stair_least_eventual_period_two` (23) |
| Necessity of eventuality | `MiddleStair/TransientCounterexample.lean`: four exact transitions (32-62), strict-band check (95), `not_period_two_from_start` (109), `period_two_from_time_two` (115) |

## Terminal dependency sketch

```text
finite recurrence + connected harmonicity
                  |
                  v
          common firing count q
             /             \
            v               v
 selected-prefix bound   affine complement
            \               /
             v             v
        strict band forces 2q=T
                  |
       Jiang-Scully-Zhang nonclumpiness
                  |
        balanced words alternate
                  |
     two-step state return; period 1 excluded
```

## Axiom audit

`formal/AxiomAudit.lean` runs `#print axioms` on the principal declarations.
The observed dependencies are only `propext`, `Classical.choice`, and
`Quot.sound`. The finite reduced-cost step uses `by decide`, so it is checked
by ordinary kernel reduction rather than trusted native code.
