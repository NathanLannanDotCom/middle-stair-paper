import MiddleStair.Orbit
import MiddleStair.Density

/-!
# Periodic upper bounds and complementary cycles

This file supplies the orbit-level complement argument used in the high-activity
half of the middle-stair theorem.  The upper bound is not assumed: a common
firing count strictly below the period gives each vertex a waiting time, and
the pointwise bound `sigma(v) <= 2 degree(v) - 1` is forward invariant.

The final construction turns a returning actual cycle of count `q` into the
returning complementary actual cycle of count `T-q`.  Applying the independent
low-activity density theorem to that cycle gives the high-activity chip bound.
-/

namespace MiddleStair

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

section UpperBox

/-- The number of firing neighbors in one round is at most the degree. -/
theorem sum_neighbor_firingIndicator_le_degree (sigma : Configuration V) (v : V) :
    (∑ w ∈ G.neighborFinset v, firingIndicator G sigma w) <=
      (G.degree v : Int) := by
  classical
  calc
    (∑ w ∈ G.neighborFinset v, firingIndicator G sigma w) <=
        ∑ _w ∈ G.neighborFinset v, (1 : Int) := by
      apply Finset.sum_le_sum
      intro w hw
      exact firingIndicator_le_one G sigma w
    _ = (G.degree v : Int) := by
      simp [G.card_neighborFinset_eq_degree]

/--
Pointwise forward invariance of the non-abundant bound.  No bounds at other
vertices are assumed; only the binary nature of their firing indicators is
used.
-/
theorem step_upper_at (sigma : Configuration V) (v : V)
    (hupper : sigma v <= 2 * (G.degree v : Int) - 1) :
    step G sigma v <= 2 * (G.degree v : Int) - 1 := by
  classical
  have hincoming := sum_neighbor_firingIndicator_le_degree G sigma v
  rw [step_apply]
  by_cases hv : Fires G sigma v
  · have hfire : firingIndicator G sigma v = 1 := by
      simp [firingIndicator, hv]
    rw [hfire]
    omega
  · have hwait : firingIndicator G sigma v = 0 := by
      simp [firingIndicator, hv]
    have hbelow : sigma v <= (G.degree v : Int) - 1 := by
      simp only [Fires] at hv
      omega
    rw [hwait]
    omega

/-- The pointwise upper bound propagates for any number of actual steps. -/
theorem actualOrbit_upper_at_of_time (sigma : Configuration V) (v : V)
    (t : Nat) (hupper : actualOrbit G sigma t v <=
      2 * (G.degree v : Int) - 1) :
    forall n : Nat, actualOrbit G sigma (t + n) v <=
      2 * (G.degree v : Int) - 1 := by
  intro n
  induction n with
  | zero => simpa using hupper
  | succ n ih =>
      rw [Nat.add_succ, actualOrbit_succ]
      exact step_upper_at G _ v ih

/-- A binary sequence with fewer than `T` ones has a zero before time `T`. -/
theorem exists_zero_of_firingPrefix_eq_of_lt
    (f : Nat -> Configuration V) (v : V) (T q : Nat)
    (hbit : forall t, t < T -> f t v = 0 ∨ f t v = 1)
    (hprefix : firingPrefix f T v = (q : Int)) (hqT : q < T) :
    ∃ t, t < T ∧ f t v = 0 := by
  by_contra hnone
  push Not at hnone
  have hall : forall t, t < T -> f t v = 1 := by
    intro t ht
    rcases hbit t ht with hzero | hone
    · exact False.elim (hnone t ht hzero)
    · exact hone
  have hprefixT : forall n : Nat,
      (forall t, t < n -> f t v = 1) ->
        firingPrefix f n v = (n : Int) := by
    intro n
    induction n with
    | zero =>
        intro _
        simp [firingPrefix]
    | succ n ih =>
        intro hn
        rw [firingPrefix]
        change firingPrefix f n v + f n v = ((n + 1 : Nat) : Int)
        rw [ih (fun t ht => hn t (Nat.lt_succ_of_lt ht)),
          hn n (Nat.lt_succ_self n)]
        push_cast
        ring
  have hT := hprefixT T hall
  have hqTInt : (q : Int) < (T : Int) := by exact_mod_cast hqT
  omega

/-- Every vertex whose common count is below the period waits in that period. -/
theorem exists_actual_wait_of_common_count_lt
    (sigma : Configuration V) (T q : Nat) (v : V)
    (hcommon : firingPrefix (actualFiring G sigma) T v = (q : Int))
    (hqT : q < T) :
    ∃ t, t < T ∧ actualFiring G sigma t v = 0 := by
  apply exists_zero_of_firingPrefix_eq_of_lt
  · intro t ht
    exact firingIndicator_eq_zero_or_one G _ v
  · exact hcommon
  · exact hqT

/-- At an actual waiting time, the state is strictly below threshold. -/
theorem actualOrbit_le_degree_sub_one_of_wait
    (sigma : Configuration V) (t : Nat) (v : V)
    (hwait : actualFiring G sigma t v = 0) :
    actualOrbit G sigma t v <= (G.degree v : Int) - 1 := by
  have hnot : ¬ Fires G (actualOrbit G sigma t) v := by
    intro hfire
    simp [actualFiring, firingIndicator, hfire] at hwait
  simp only [Fires] at hnot
  omega

/--
A returning actual cycle with common count `q<T` lies in the affine complement
box.  Connectedness is not an extra hypothesis here: it is used upstream to
obtain `hcommon`; this theorem records the exact consequence needed later.
-/
theorem returning_actual_cycle_upper
    (sigma : Configuration V) (T q : Nat)
    (hreturn : actualOrbit G sigma T = sigma)
    (hcommon : forall v,
      firingPrefix (actualFiring G sigma) T v = (q : Int))
    (hqT : q < T) :
    forall v, sigma v <= 2 * (G.degree v : Int) - 1 := by
  intro v
  obtain ⟨t, htT, hwait⟩ :=
    exists_actual_wait_of_common_count_lt G sigma T q v (hcommon v) hqT
  have hbelow := actualOrbit_le_degree_sub_one_of_wait G sigma t v hwait
  have hdegree : (0 : Int) <= (G.degree v : Int) := by omega
  have hatTime : actualOrbit G sigma t v <= 2 * (G.degree v : Int) - 1 := by
    omega
  have hforward := actualOrbit_upper_at_of_time G sigma v t hatTime (T - t)
  have hindex : t + (T - t) = T := Nat.add_sub_of_le (Nat.le_of_lt htT)
  rw [hindex, hreturn] at hforward
  exact hforward

end UpperBox

section ComplementedOrbit

/-- The affine complement commutes with every iterate of the actual dynamics. -/
theorem complement_actualOrbit (sigma : Configuration V) : forall n : Nat,
    complement G (actualOrbit G sigma n) =
      actualOrbit G (complement G sigma) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [actualOrbit_succ, actualOrbit_succ, complement_step, ih]

/-- Complementing a returning actual cycle gives another returning cycle. -/
theorem complement_actualOrbit_returns (sigma : Configuration V) (T : Nat)
    (hreturn : actualOrbit G sigma T = sigma) :
    actualOrbit G (complement G sigma) T = complement G sigma := by
  calc
    actualOrbit G (complement G sigma) T =
        complement G (actualOrbit G sigma T) :=
      (complement_actualOrbit G sigma T).symm
    _ = complement G sigma := congrArg (complement G) hreturn

/-- The actual firing vector on the complementary orbit is bitwise complemented. -/
theorem actualFiring_complement (sigma : Configuration V) (n : Nat) :
    actualFiring G (complement G sigma) n =
      fun v => 1 - actualFiring G sigma n v := by
  simp only [actualFiring]
  rw [← complement_actualOrbit G sigma n, firingIndicator_complement]

/-- Prefix sums of bitwise-complemented integer sequences. -/
theorem firingPrefix_one_sub (f : Nat -> Configuration V) (n : Nat) (v : V) :
    firingPrefix (fun t v => 1 - f t v) n v =
      (n : Int) - firingPrefix f n v := by
  induction n with
  | zero => simp [firingPrefix]
  | succ n ih =>
      rw [firingPrefix, firingPrefix]
      simp only [Pi.add_apply]
      rw [ih]
      push_cast
      ring

/-- The complementary actual cycle fires `T` minus the original prefix. -/
theorem firingPrefix_actualFiring_complement
    (sigma : Configuration V) (T : Nat) (v : V) :
    firingPrefix (actualFiring G (complement G sigma)) T v =
      (T : Int) - firingPrefix (actualFiring G sigma) T v := by
  have hfun : actualFiring G (complement G sigma) =
      fun t v => 1 - actualFiring G sigma t v := by
    funext t v
    exact congrFun (actualFiring_complement G sigma t) v
  rw [hfun]
  exact firingPrefix_one_sub (actualFiring G sigma) T v

/-- Restarting an actual orbit at time `mu` identifies tail and restarted firing. -/
theorem tailFiring_eq_actualFiring_restart (sigma : Configuration V) (mu n : Nat) :
    tailFiring G sigma mu n = actualFiring G (actualOrbit G sigma mu) n := by
  simp only [tailFiring, actualFiring]
  rw [← actualOrbit_add]

/--
Connectedness turns a returning actual cycle's integer common count into a
natural common count bounded by the period.  This is the bridge from
`Orbit.lean` to the natural-number interfaces of the density constructions.
-/
theorem exists_common_actual_firing_count_nat
    (hG : G.Connected) (sigma : Configuration V) (T : Nat)
    (hreturn : actualOrbit G sigma T = sigma) :
    ∃ q : Nat,
      (∀ v, firingPrefix (actualFiring G sigma) T v = (q : Int)) ∧ q ≤ T := by
  have hperiod : actualOrbit G sigma (0 + T) = actualOrbit G sigma 0 := by
    simpa using hreturn
  obtain ⟨z, hz, hznonneg, hzle⟩ :=
    common_actual_firing_count_bounds G hG sigma 0 T hperiod
  have htail : tailFiring G sigma 0 = actualFiring G sigma := by
    funext n v
    simp [tailFiring, actualFiring]
  rw [htail] at hz
  refine ⟨z.toNat, ?_, ?_⟩
  · intro v
    have hzv := congrFun hz v
    rw [Int.toNat_of_nonneg hznonneg]
    exact hzv
  · have hcast : ((z.toNat : Nat) : Int) ≤ (T : Int) := by
      simpa [Int.toNat_of_nonneg hznonneg] using hzle
    exact_mod_cast hcast

/-- Package an actual low-activity returning cycle for `low_activity_density`. -/
noncomputable def lowActivityOrbitOfActual
    (hG : G.Connected) (sigma : Configuration V) (T q : Nat)
    (hsigma : ∀ v, 0 ≤ sigma v)
    (hreturn : actualOrbit G sigma T = sigma)
    (hcommon : ∀ v,
      firingPrefix (actualFiring G sigma) T v = (q : Int))
    (hT : 0 < T) (hlow : 2 * q < T) :
    LowActivityPeriodicOrbit G where
  initial := sigma
  initial_nonnegative := hsigma
  firing := actualFiring G sigma
  period := T
  period_pos := hT
  commonCount := q
  lowActivity := hlow
  connected := hG
  actual := by
    intro t ht
    simp only [actualFiring]
    rw [← actualOrbit_eq_evolve]
  returns := by
    rw [← actualOrbit_eq_evolve]
    exact hreturn
  commonPrefix := hcommon

/--
The complementary returning cycle packaged for the low-activity density lemma.
The original common count is `q`; the complementary count is exactly `T-q`.
-/
noncomputable def complementLowActivityOrbit
    (hG : G.Connected) (sigma : Configuration V) (T q : Nat)
    (hreturn : actualOrbit G sigma T = sigma)
    (hcommon : forall v,
      firingPrefix (actualFiring G sigma) T v = (q : Int))
    (hqT : q < T) (hhigh : T < 2 * q) :
    LowActivityPeriodicOrbit G where
  initial := complement G sigma
  initial_nonnegative := by
    intro v
    exact complement_nonnegative_at G sigma v
      (returning_actual_cycle_upper G sigma T q hreturn hcommon hqT v)
  firing := actualFiring G (complement G sigma)
  period := T
  period_pos := Nat.zero_lt_of_lt hqT
  commonCount := T - q
  lowActivity := by omega
  connected := hG
  actual := by
    intro t ht
    simp only [actualFiring]
    rw [← actualOrbit_eq_evolve]
  returns := by
    rw [← actualOrbit_eq_evolve]
    exact complement_actualOrbit_returns G sigma T hreturn
  commonPrefix := by
    intro v
    rw [firingPrefix_actualFiring_complement G sigma T v, hcommon v]
    exact (Nat.cast_sub (R := Int) (Nat.le_of_lt hqT)).symm

/-- Total chips in the affine complement. -/
theorem totalChips_complement (sigma : Configuration V) :
    totalChips (complement G sigma) =
      4 * (G.edgeFinset.card : Int) - (Fintype.card V : Int) - totalChips sigma := by
  have hdegreeNat := G.sum_degrees_eq_twice_card_edges
  have hdegreeInt :
      (∑ v : V, (G.degree v : Int)) =
        2 * (G.edgeFinset.card : Int) := by
    exact_mod_cast hdegreeNat
  simp only [totalChips, complement, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hdegreeInt]
  ring

/--
High-activity density bound obtained solely by complementing the actual cycle
and applying `low_activity_density` to the resulting low-activity cycle.
-/
theorem high_activity_density_of_returning_actual
    (hG : G.Connected) (sigma : Configuration V) (T q : Nat)
    (hreturn : actualOrbit G sigma T = sigma)
    (hcommon : forall v,
      firingPrefix (actualFiring G sigma) T v = (q : Int))
    (hqT : q < T) (hhigh : T < 2 * q) :
    2 * (G.edgeFinset.card : Int) <= totalChips sigma := by
  let O := complementLowActivityOrbit G hG sigma T q hreturn hcommon hqT hhigh
  have hlow := LowActivityPeriodicOrbit.low_activity_density O
  have hlow' : totalChips (complement G sigma) <=
      2 * (G.edgeFinset.card : Int) - (Fintype.card V : Int) := by
    simpa only [totalChips, O, complementLowActivityOrbit] using hlow
  rw [totalChips_complement G sigma] at hlow'
  omega

end ComplementedOrbit

end MiddleStair
