import MiddleStair.ComplementOrbit

/-!
# The sharp activity dichotomy in the middle band

This file joins the connected-Laplacian common-count theorem to the
minimum-phase density estimate and its complemented high-activity version.
Its main theorem is deliberately about an arbitrary returning actual cycle:
under the strict middle-stair chip bounds, its common firing count is exactly
half of its period.  No non-clumpiness theorem is used here.
-/

namespace MiddleStair

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/--
If a vertex fires `T` times in `T>0` rounds, then it fires in round zero.
The proof uses only the zero-one bound; it does not smuggle in periodicity.
-/
theorem actualFiring_zero_eq_one_of_prefix_eq_time
    (sigma : Configuration V) (v : V) : forall T : Nat,
    0 < T ->
    firingPrefix (actualFiring G sigma) T v = (T : Int) ->
    actualFiring G sigma 0 v = 1 := by
  intro T
  induction T with
  | zero =>
      intro hT
      omega
  | succ n ih =>
      intro hT hsum
      rw [firingPrefix] at hsum
      change firingPrefix (actualFiring G sigma) n v +
        actualFiring G sigma n v = ((n + 1 : Nat) : Int) at hsum
      by_cases hn : n = 0
      · subst n
        simpa [firingPrefix] using hsum
      · have hprefix_le : firingPrefix (actualFiring G sigma) n v <= (n : Int) := by
          have hbound := tailFiringPrefix_le_time G sigma 0 n v
          have htail : tailFiring G sigma 0 = actualFiring G sigma := by
            funext k w
            simp [tailFiring, actualFiring]
          rw [htail] at hbound
          exact hbound
        have hbit_le : actualFiring G sigma n v <= 1 := by
          exact firingIndicator_le_one G _ v
        have hprefix_eq : firingPrefix (actualFiring G sigma) n v = (n : Int) := by
          push_cast at hsum
          omega
        exact ih (Nat.pos_of_ne_zero hn) hprefix_eq

/-- A full-firing first round forces at least the degree sum in total chips. -/
theorem totalChips_ge_twice_edges_of_full_common_count
    (sigma : Configuration V) (T : Nat) (hT : 0 < T)
    (hcommon : forall v,
      firingPrefix (actualFiring G sigma) T v = (T : Int)) :
    2 * (G.edgeFinset.card : Int) <= totalChips sigma := by
  have hcoordinate : forall v, (G.degree v : Int) <= sigma v := by
    intro v
    have hbit := actualFiring_zero_eq_one_of_prefix_eq_time G sigma v T hT (hcommon v)
    have hfire : Fires G sigma v := by
      by_contra hnot
      simp [actualFiring, firingIndicator, hnot] at hbit
    exact hfire
  have hsum : (∑ v : V, (G.degree v : Int)) <= ∑ v, sigma v := by
    exact Finset.sum_le_sum fun v _ => hcoordinate v
  have hdegreeNat := G.sum_degrees_eq_twice_card_edges
  have hdegreeInt :
      (∑ v : V, (G.degree v : Int)) =
        2 * (G.edgeFinset.card : Int) := by
    exact_mod_cast hdegreeNat
  simpa only [totalChips, hdegreeInt] using hsum

/--
Every positive returning period in the strict middle band has common activity
exactly `1/2`.  The witness `q` is a natural count and all endpoint exclusions
are proved from the strict chip inequalities.
-/
theorem returning_cycle_half_activity
    (hG : G.Connected) (sigma : Configuration V) (T : Nat)
    (hnonnegative : forall v, 0 <= sigma v)
    (hT : 0 < T) (hreturn : actualOrbit G sigma T = sigma)
    (hbandLow :
      2 * (G.edgeFinset.card : Int) - (Fintype.card V : Int) < totalChips sigma)
    (hbandHigh : totalChips sigma < 2 * (G.edgeFinset.card : Int)) :
    exists q : Nat,
      (forall v, firingPrefix (actualFiring G sigma) T v = (q : Int)) /\
      0 < q /\ q < T /\ 2 * q = T := by
  have hreturn0 : actualOrbit G sigma (0 + T) = actualOrbit G sigma 0 := by
    simpa using hreturn
  obtain ⟨qz, hcommonTail, hqz0, hqzT⟩ :=
    common_actual_firing_count_bounds G hG sigma 0 T hreturn0
  have htail : tailFiring G sigma 0 = actualFiring G sigma := by
    funext n v
    simp [tailFiring, actualFiring]
  rw [htail] at hcommonTail
  let q : Nat := qz.toNat
  have hqcast : (q : Int) = qz := by
    exact Int.toNat_of_nonneg hqz0
  have hcommon : forall v,
      firingPrefix (actualFiring G sigma) T v = (q : Int) := by
    intro v
    rw [congrFun hcommonTail v, hqcast]
  have hq_le : q <= T := by
    have hq_le_int : (q : Int) <= (T : Int) := by
      rw [hqcast]
      exact hqzT
    exact_mod_cast hq_le_int
  have hq_pos : 0 < q := by
    by_contra hnot
    have hqzero : q = 0 := Nat.eq_zero_of_not_pos hnot
    let O := lowActivityOrbitOfActual G hG sigma T q hnonnegative hreturn hcommon hT (by omega)
    have hdensity := LowActivityPeriodicOrbit.low_activity_density O
    have hdensity' : totalChips sigma <=
        2 * (G.edgeFinset.card : Int) - (Fintype.card V : Int) := by
      simpa only [totalChips, O, lowActivityOrbitOfActual] using hdensity
    omega
  have hq_lt : q < T := by
    by_contra hnot
    have hqeq : q = T := by omega
    have hfull : forall v,
        firingPrefix (actualFiring G sigma) T v = (T : Int) := by
      intro v
      simpa [hqeq] using hcommon v
    have hlarge := totalChips_ge_twice_edges_of_full_common_count G sigma T hT hfull
    omega
  have hhalf : 2 * q = T := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlow | hhigh
    · let O := lowActivityOrbitOfActual G hG sigma T q hnonnegative hreturn hcommon hT hlow
      have hdensity := LowActivityPeriodicOrbit.low_activity_density O
      have hdensity' : totalChips sigma <=
          2 * (G.edgeFinset.card : Int) - (Fintype.card V : Int) := by
        simpa only [totalChips, O, lowActivityOrbitOfActual] using hdensity
      omega
    · have hlarge := high_activity_density_of_returning_actual
          G hG sigma T q hreturn hcommon hq_lt hhigh
      omega
  exact ⟨q, hcommon, hq_pos, hq_lt, hhalf⟩

end MiddleStair
