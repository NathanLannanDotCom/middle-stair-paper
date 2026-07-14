import MiddleStair.Activity

/-!
# Eventual and least state periods

These definitions distinguish a returning cycle, an eventual (not necessarily
least) period, and the least positive eventual state period.  This prevents the
final theorem from silently proving only activity period or firing-word period.
-/

namespace MiddleStair

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `p` is an eventual state period of the deterministic orbit. -/
def HasEventualPeriod (sigma : Configuration V) (p : Nat) : Prop :=
  exists mu : Nat, forall t : Nat,
    actualOrbit G sigma (mu + p + t) = actualOrbit G sigma (mu + t)

/-- `p` is the least positive eventual state period. -/
def HasLeastEventualPeriod (sigma : Configuration V) (p : Nat) : Prop :=
  0 < p /\ HasEventualPeriod G sigma p /\
    forall r : Nat, 0 < r -> HasEventualPeriod G sigma r -> p <= r

/-- A repeated pair of states gives an eventual period from that time onward. -/
theorem hasEventualPeriod_of_returning_tail
    (sigma : Configuration V) (mu p : Nat)
    (hreturn : actualOrbit G sigma (mu + p) = actualOrbit G sigma mu) :
    HasEventualPeriod G sigma p := by
  refine ⟨mu, ?_⟩
  intro t
  exact (actualOrbit_eq_of_repeat G sigma hreturn.symm t).symm

/-- Restarting at a witness for an eventual period produces a returning orbit. -/
theorem restarted_orbit_returns_of_eventualPeriod
    (sigma : Configuration V) (p : Nat)
    (hperiod : HasEventualPeriod G sigma p) :
    exists mu : Nat,
      actualOrbit G (actualOrbit G sigma mu) p = actualOrbit G sigma mu := by
  obtain ⟨mu, hmu⟩ := hperiod
  refine ⟨mu, ?_⟩
  rw [← actualOrbit_add]
  simpa using hmu 0

/-- Complementary firing in the first two rounds returns the state in two steps. -/
theorem actualOrbit_two_eq_of_firing_complement
    (sigma : Configuration V)
    (halternates : forall v,
      actualFiring G sigma 1 v = 1 - actualFiring G sigma 0 v) :
    actualOrbit G sigma 2 = sigma := by
  change update G (update G sigma (firingIndicator G sigma))
      (firingIndicator G (step G sigma)) = sigma
  apply update_two_rounds_of_sum_one
  funext v
  have hv := halternates v
  change firingIndicator G (step G sigma) v =
      1 - firingIndicator G sigma v at hv
  change firingIndicator G sigma v + firingIndicator G (step G sigma) v = 1
  rw [hv]
  ring

/-- The strict middle band admits no eventual fixed state. -/
theorem not_hasEventualPeriod_one_of_middle_band
    (hG : G.Connected) (sigma : Configuration V)
    (hnonnegative : forall v, 0 <= sigma v)
    (hbandLow :
      2 * (G.edgeFinset.card : Int) - (Fintype.card V : Int) < totalChips sigma)
    (hbandHigh : totalChips sigma < 2 * (G.edgeFinset.card : Int)) :
    ¬ HasEventualPeriod G sigma 1 := by
  intro hone
  obtain ⟨mu, hreturn⟩ := restarted_orbit_returns_of_eventualPeriod G sigma 1 hone
  let tau := actualOrbit G sigma mu
  have htau_nonnegative : forall v, 0 <= tau v := by
    exact actualOrbit_nonnegative G sigma hnonnegative mu
  have htotal : totalChips tau = totalChips sigma := by
    exact totalChips_actualOrbit G sigma mu
  have hlow_tau :
      2 * (G.edgeFinset.card : Int) - (Fintype.card V : Int) < totalChips tau := by
    rw [htotal]
    exact hbandLow
  have hhigh_tau : totalChips tau < 2 * (G.edgeFinset.card : Int) := by
    rw [htotal]
    exact hbandHigh
  obtain ⟨q, _hcommon, _hqpos, _hqlt, hhalf⟩ :=
    returning_cycle_half_activity G hG tau 1 htau_nonnegative (by omega)
      hreturn hlow_tau hhigh_tau
  omega

/-- Once period two exists and period one is impossible, two is the least period. -/
theorem hasLeastEventualPeriod_two
    (sigma : Configuration V)
    (htwo : HasEventualPeriod G sigma 2)
    (hnotone : ¬ HasEventualPeriod G sigma 1) :
    HasLeastEventualPeriod G sigma 2 := by
  refine ⟨by omega, htwo, ?_⟩
  intro r hr hperiod
  by_contra hnot
  have hrone : r = 1 := by omega
  subst r
  exact hnotone hperiod

end MiddleStair
