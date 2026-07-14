import MiddleStair.Universal
import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# Why the universal theorem must say `eventually`

The strict middle band does not force a configuration to lie on its period-two
cycle at time zero.  This file kernel-checks the smallest counterexample found
by the repository's exhaustive connected-graph search: a three-vertex path
with two chips concentrated at one leaf.  Its transient has length two.
-/

namespace MiddleStair.TransientCounterexample

/-- The path on three vertices, with `0` as its degree-two center. -/
def graph : SimpleGraph (Fin 3) := SimpleGraph.starGraph 0

instance : DecidableRel graph.Adj := by
  dsimp [graph]
  infer_instance

/-- The initial state and the three subsequent distinct states. -/
def state0 : Configuration (Fin 3) := ![0, 0, 2]
def state1 : Configuration (Fin 3) := ![1, 0, 1]
def state2 : Configuration (Fin 3) := ![2, 0, 0]
def state3 : Configuration (Fin 3) := ![0, 1, 1]

private theorem step_ext (sigma tau : Configuration (Fin 3))
    (h : ∀ v, step graph sigma v = tau v) : step graph sigma = tau :=
  funext h

theorem step_state0 : step graph state0 = state1 := by
  apply step_ext
  intro v
  fin_cases v <;>
    simp [state0, state1, graph, step, update, laplacian, firingIndicator, Fires,
      SimpleGraph.starGraph, SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] <;>
    decide

theorem step_state1 : step graph state1 = state2 := by
  apply step_ext
  intro v
  fin_cases v <;>
    simp [state1, state2, graph, step, update, laplacian, firingIndicator, Fires,
      SimpleGraph.starGraph, SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] <;>
    decide

theorem step_state2 : step graph state2 = state3 := by
  apply step_ext
  intro v
  fin_cases v <;>
    simp [state2, state3, graph, step, update, laplacian, firingIndicator, Fires,
      SimpleGraph.starGraph, SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] <;>
    decide

theorem step_state3 : step graph state3 = state2 := by
  apply step_ext
  intro v
  fin_cases v <;>
    simp [state3, state2, graph, step, update, laplacian, firingIndicator, Fires,
      SimpleGraph.starGraph, SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] <;>
    decide

theorem orbit_one : actualOrbit graph state0 1 = state1 := by
  simpa only [actualOrbit_succ, actualOrbit_zero] using step_state0

theorem orbit_two : actualOrbit graph state0 2 = state2 := by
  change step graph (actualOrbit graph state0 1) = state2
  rw [orbit_one]
  exact step_state1

theorem orbit_three : actualOrbit graph state0 3 = state3 := by
  change step graph (actualOrbit graph state0 2) = state3
  rw [orbit_two]
  exact step_state2

theorem orbit_four : actualOrbit graph state0 4 = state2 := by
  change step graph (actualOrbit graph state0 3) = state2
  rw [orbit_three]
  exact step_state3

theorem graph_connected : graph.Connected := by
  exact SimpleGraph.connected_starGraph 0

theorem state0_nonnegative : ∀ v, 0 ≤ state0 v := by
  intro v
  fin_cases v <;> simp [state0]

theorem edge_card : graph.edgeFinset.card = 2 := by
  decide

theorem state0_total : totalChips state0 = 2 := by
  decide

theorem state0_in_strict_middle_band :
    2 * (graph.edgeFinset.card : Int) - (Fintype.card (Fin 3) : Int) <
        totalChips state0 ∧
      totalChips state0 < 2 * (graph.edgeFinset.card : Int) := by
  rw [edge_card, state0_total]
  norm_num

theorem orbit_two_ne_initial : actualOrbit graph state0 2 ≠ state0 := by
  rw [orbit_two]
  intro h
  have h0 := congrFun h (0 : Fin 3)
  norm_num [state2, state0] at h0

/-- Period two does not hold from time zero, despite every theorem hypothesis. -/
theorem not_period_two_from_start :
    ¬ ∀ t : Nat, actualOrbit graph state0 (2 + t) = actualOrbit graph state0 t := by
  intro h
  simpa using orbit_two_ne_initial (h 0)

/-- The same orbit does have period two from time `2` onward. -/
theorem period_two_from_time_two :
    ∀ t : Nat,
      actualOrbit graph state0 (2 + 2 + t) = actualOrbit graph state0 (2 + t) := by
  intro t
  have hrepeat : actualOrbit graph state0 2 = actualOrbit graph state0 4 := by
    rw [orbit_two, orbit_four]
  simpa [Nat.add_assoc] using
    (actualOrbit_eq_of_repeat graph state0 hrepeat t).symm

end MiddleStair.TransientCounterexample
