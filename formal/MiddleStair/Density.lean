import MiddleStair.Dynamics
import MiddleStair.PrefixMinimum
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# The graph-wide low-activity density estimate

This file closes the finite summation step in the middle-stair argument.  A
`LowActivityPeriodicOrbit` contains an *actual* parallel chip-firing cycle,
including the common firing count that connectedness supplies from the
Laplacian-kernel argument.  No density estimate or edge-regrouping identity is
stored in the structure.

The proof chooses a minimum phase independently at every vertex.  Phase zero
is represented at the right endpoint of the period when its predecessor is
needed; this is the only wraparound bookkeeping.  The graph-wide regrouping is
performed by symmetrising the directed adjacency sum.  Thus every unoriented
edge contributes the sum of its two directed terms, exactly the edge charge
from `PrefixMinimum.lean`.
-/

namespace MiddleStair

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/--
Data for a nontrivial low-activity periodic orbit.  `commonPrefix` is normally
deduced from `returns` and connectedness; it is recorded here so that the
graph-wide density lemma has a sharply delimited interface.
-/
structure LowActivityPeriodicOrbit where
  initial : Configuration V
  initial_nonnegative : ∀ v, 0 ≤ initial v
  firing : ℕ → Configuration V
  period : ℕ
  period_pos : 0 < period
  commonCount : ℕ
  lowActivity : 2 * commonCount < period
  connected : G.Connected
  actual : ∀ t, t < period →
    firing t = firingIndicator G (evolve G initial firing t)
  returns : evolve G initial firing period = initial
  commonPrefix : ∀ v,
    firingPrefix firing period v = (commonCount : ℤ)

namespace LowActivityPeriodicOrbit

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The denominator-cleared centered prefix height at a vertex and time. -/
def height (O : LowActivityPeriodicOrbit G) (v : V) (t : ℕ) : ℤ :=
  scaledHeight (O.period : ℤ) (O.commonCount : ℤ)
    (firingPrefix O.firing t v) (t : ℤ)

theorem height_period_eq_zero (O : LowActivityPeriodicOrbit G) (v : V) :
    O.height v O.period = O.height v 0 := by
  simp [height, O.commonPrefix, firingPrefix, scaledHeight]
  ring

/-- A phase at which the centered prefix height is least. -/
noncomputable def selectedPhase (O : LowActivityPeriodicOrbit G) (v : V) : Fin O.period := by
  classical
  have huniv : (Finset.univ : Finset (Fin O.period)).Nonempty :=
    ⟨⟨0, O.period_pos⟩, Finset.mem_univ _⟩
  exact Classical.choose
    (Finset.exists_min_image Finset.univ (fun t : Fin O.period => O.height v t.val)
      huniv)

theorem selectedPhase_min (O : LowActivityPeriodicOrbit G) (v : V)
    (t : Fin O.period) :
    O.height v (O.selectedPhase v).val ≤ O.height v t.val := by
  classical
  have huniv : (Finset.univ : Finset (Fin O.period)).Nonempty :=
    ⟨⟨0, O.period_pos⟩, Finset.mem_univ _⟩
  exact (Classical.choose_spec
    (Finset.exists_min_image Finset.univ (fun t : Fin O.period => O.height v t.val)
      huniv)).2 t (Finset.mem_univ t)

/-- The round immediately preceding the selected minimum, with cyclic wrap. -/
noncomputable def selectedTime (O : LowActivityPeriodicOrbit G) (v : V) : ℕ :=
  if (O.selectedPhase v).val = 0 then O.period - 1
  else (O.selectedPhase v).val - 1

theorem selectedTime_lt_period (O : LowActivityPeriodicOrbit G) (v : V) :
    O.selectedTime v < O.period := by
  classical
  simp only [selectedTime]
  split_ifs with h
  · omega
  · have hp := (O.selectedPhase v).isLt
    omega

theorem selected_end_height_eq_phase (O : LowActivityPeriodicOrbit G) (v : V) :
    O.height v (O.selectedTime v + 1) =
      O.height v (O.selectedPhase v).val := by
  classical
  simp only [selectedTime]
  split_ifs with h
  · have hperiod : O.period - 1 + 1 = O.period := by omega
    rw [hperiod, O.height_period_eq_zero]
    simpa [h]
  · have hphase : (O.selectedPhase v).val - 1 + 1 =
        (O.selectedPhase v).val := by omega
    rw [hphase]

/-- The selected minimum is no higher than any phase in the period. -/
theorem selected_end_height_le (O : LowActivityPeriodicOrbit G) (v : V)
    (t : ℕ) (ht : t < O.period) :
    O.height v (O.selectedTime v + 1) ≤ O.height v t := by
  rw [O.selected_end_height_eq_phase]
  exact O.selectedPhase_min v ⟨t, ht⟩

theorem firing_bit (O : LowActivityPeriodicOrbit G) (v : V) (t : ℕ)
    (ht : t < O.period) :
    O.firing t v = 0 ∨ O.firing t v = 1 := by
  rw [O.actual t ht]
  exact firingIndicator_eq_zero_or_one G _ v

theorem prefix_succ_apply (O : LowActivityPeriodicOrbit G) (v : V) (t : ℕ) :
    firingPrefix O.firing (t + 1) v =
      firingPrefix O.firing t v + O.firing t v := by
  simp [firingPrefix]

/-- A selected prefix minimum forces that vertex to wait in the prior round. -/
theorem selected_waits (O : LowActivityPeriodicOrbit G) (v : V) :
    O.firing (O.selectedTime v) v = 0 := by
  have hmin := O.selected_end_height_le v (O.selectedTime v)
    (O.selectedTime_lt_period v)
  have hq : (O.commonCount : ℤ) < (O.period : ℤ) := by
    have hhalfNat := O.lowActivity
    have hqNat : O.commonCount < O.period := by omega
    exact_mod_cast hqNat
  have hbit := O.firing_bit v (O.selectedTime v) (O.selectedTime_lt_period v)
  simp only [height] at hmin
  rw [O.prefix_succ_apply] at hmin
  exact selected_minimum_forces_wait
    (O.period : ℤ) (O.commonCount : ℤ)
    (firingPrefix O.firing (O.selectedTime v) v)
    (O.selectedTime v : ℤ) (O.firing (O.selectedTime v) v)
    hq hbit (by simpa using hmin)

theorem prefix_selected_succ (O : LowActivityPeriodicOrbit G) (v : V) :
    firingPrefix O.firing (O.selectedTime v + 1) v =
      firingPrefix O.firing (O.selectedTime v) v := by
  rw [O.prefix_succ_apply, O.selected_waits]
  simp

/-- The selected vertex is below threshold at its selected time. -/
theorem selected_state_le_degree_sub_one (O : LowActivityPeriodicOrbit G) (v : V) :
    evolve G O.initial O.firing (O.selectedTime v) v ≤
      (G.degree v : ℤ) - 1 := by
  have hactual := congrFun
    (O.actual (O.selectedTime v) (O.selectedTime_lt_period v)) v
  have hwait := O.selected_waits v
  have hnot : ¬ Fires G (evolve G O.initial O.firing (O.selectedTime v)) v := by
    by_contra hfire
    simp only [firingIndicator, hfire, if_true] at hactual
    omega
  simp only [Fires] at hnot
  omega

/-- The fixed initial coordinate is bounded using its own selected time. -/
theorem initial_le_degree_sub_one_add_laplacian
    (O : LowActivityPeriodicOrbit G) (v : V) :
    O.initial v ≤ (G.degree v : ℤ) - 1 +
      laplacian G (firingPrefix O.firing (O.selectedTime v)) v := by
  have hevolve := congrFun
    (evolve_eq_update_prefix G O.initial O.firing (O.selectedTime v)) v
  have hstate := O.selected_state_le_degree_sub_one v
  simp only [update, Pi.sub_apply] at hevolve
  omega

/-- The directed contribution of `v → w` at `v`'s independently selected time. -/
noncomputable def directedCharge (O : LowActivityPeriodicOrbit G) (v w : V) : ℤ :=
  firingPrefix O.firing (O.selectedTime v) v -
    firingPrefix O.firing (O.selectedTime v) w

/--
For one edge, the two directed Laplacian terms form the integral edge charge
and have nonpositive sum.
-/
theorem edge_charge_nonpositive (O : LowActivityPeriodicOrbit G)
    {v w : V} (_hvw : G.Adj v w) :
    O.directedCharge v w + O.directedCharge w v ≤ 0 := by
  have hcrossV := O.selected_end_height_le v (O.selectedTime w)
    (O.selectedTime_lt_period w)
  have hcrossW := O.selected_end_height_le w (O.selectedTime v)
    (O.selectedTime_lt_period v)
  simp only [height] at hcrossV hcrossW
  rw [O.prefix_selected_succ] at hcrossV hcrossW
  have hT : (0 : ℤ) < (O.period : ℤ) := by exact_mod_cast O.period_pos
  have hhalf : 2 * (O.commonCount : ℤ) < (O.period : ℤ) := by
    exact_mod_cast O.lowActivity
  have hedge := selected_edge_charge_nonpositive
    (O.period : ℤ) (O.commonCount : ℤ)
    (O.selectedTime v : ℤ) (O.selectedTime w : ℤ)
    (firingPrefix O.firing (O.selectedTime v) v)
    (firingPrefix O.firing (O.selectedTime v) w)
    (firingPrefix O.firing (O.selectedTime w) w)
    (firingPrefix O.firing (O.selectedTime w) v)
    hT hhalf (by simpa using hcrossV) (by simpa using hcrossW)
  simpa only [directedCharge, edgeCharge, sub_eq_add_neg, add_assoc] using hedge

/-- Swapping the two endpoints preserves the directed adjacency sum. -/
theorem sum_directedCharge_swap (O : LowActivityPeriodicOrbit G) :
    (∑ v, ∑ w ∈ G.neighborFinset v, O.directedCharge v w) =
      ∑ v, ∑ w ∈ G.neighborFinset v, O.directedCharge w v := by
  simp_rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  calc
    (∑ v, ∑ w, if G.Adj v w then O.directedCharge v w else 0) =
        ∑ w, ∑ v, if G.Adj v w then O.directedCharge v w else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ v, ∑ w, if G.Adj v w then O.directedCharge w v else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro w _
      simp only [G.adj_comm]

/--
Graph-wide edge regrouping.  The directed adjacency sum contains both
orientations of every unoriented edge; pairing those orientations and using
`edge_charge_nonpositive` makes the entire selected Laplacian correction
nonpositive.
-/
theorem sum_directedCharge_nonpositive (O : LowActivityPeriodicOrbit G) :
    (∑ v, ∑ w ∈ G.neighborFinset v, O.directedCharge v w) ≤ 0 := by
  let S : ℤ := ∑ v, ∑ w ∈ G.neighborFinset v, O.directedCharge v w
  have hswap : S = ∑ v, ∑ w ∈ G.neighborFinset v, O.directedCharge w v := by
    exact O.sum_directedCharge_swap
  have hpairs :
      (∑ v, ∑ w ∈ G.neighborFinset v,
        (O.directedCharge v w + O.directedCharge w v)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro v hv
    apply Finset.sum_nonpos
    intro w hw
    exact O.edge_charge_nonpositive ((G.mem_neighborFinset v w).mp hw)
  have hpairsEq :
      (∑ v, ∑ w ∈ G.neighborFinset v,
        (O.directedCharge v w + O.directedCharge w v)) =
        S + (∑ v, ∑ w ∈ G.neighborFinset v, O.directedCharge w v) := by
    dsimp only [S]
    simp only [Finset.sum_add_distrib]
  have hdouble : S + S ≤ 0 := by
    calc
      S + S = S + (∑ v, ∑ w ∈ G.neighborFinset v,
          O.directedCharge w v) := congrArg (fun x => S + x) hswap
      _ = ∑ v, ∑ w ∈ G.neighborFinset v,
          (O.directedCharge v w + O.directedCharge w v) := hpairsEq.symm
      _ ≤ 0 := hpairs
  have htwo : 2 * S ≤ 0 := by omega
  omega

/-- The sum of the selected-time Laplacian coordinates is nonpositive. -/
theorem sum_selected_laplacian_nonpositive (O : LowActivityPeriodicOrbit G) :
    (∑ v, laplacian G (firingPrefix O.firing (O.selectedTime v)) v) ≤ 0 := by
  simpa only [laplacian, directedCharge] using O.sum_directedCharge_nonpositive

/-- The degree-minus-one baseline is exactly `2|E| - |V|`. -/
theorem sum_degree_sub_one_eq (_O : LowActivityPeriodicOrbit G) :
    (∑ v : V, ((G.degree v : ℤ) - 1)) =
      2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) := by
  have hdegreeNat := G.sum_degrees_eq_twice_card_edges
  have hdegreeInt :
      (∑ v : V, (G.degree v : ℤ)) =
        2 * (G.edgeFinset.card : ℤ) := by
    exact_mod_cast hdegreeNat
  rw [Finset.sum_sub_distrib, hdegreeInt]
  simp

/--
The full low-activity density lemma: an actual finite connected periodic orbit
with common period firing count `q` and `2q < T` has at most
`2 |E| - |V|` chips.
-/
theorem low_activity_density (O : LowActivityPeriodicOrbit G) :
    (∑ v, O.initial v) ≤
      2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) := by
  calc
    (∑ v, O.initial v) ≤
        ∑ v, ((G.degree v : ℤ) - 1 +
          laplacian G (firingPrefix O.firing (O.selectedTime v)) v) := by
      apply Finset.sum_le_sum
      intro v hv
      exact O.initial_le_degree_sub_one_add_laplacian v
    _ = (∑ v, ((G.degree v : ℤ) - 1)) +
        ∑ v, laplacian G (firingPrefix O.firing (O.selectedTime v)) v := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ v, ((G.degree v : ℤ) - 1)) + 0 := by
      exact add_le_add_right O.sum_selected_laplacian_nonpositive _
    _ = 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) := by
      rw [O.sum_degree_sub_one_eq]
      simp

end LowActivityPeriodicOrbit

end MiddleStair
