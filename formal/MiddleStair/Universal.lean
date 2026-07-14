import MiddleStair.CyclicWrapper
import MiddleStair.Period

/-!
# The universal middle-stair theorem

This file is the end-to-end assembly.  Starting from an arbitrary legal
nonnegative configuration, it enters a returning tail, proves that every
return period has common activity one half, invokes the closed formalization
of Jiang--Scully--Zhang non-clumpiness to obtain alternating firing, and then
proves that two is the least eventual *state* period.
-/

namespace MiddleStair

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/--
Universal Ji--Li--Wang middle-stair theorem: every legal integer
configuration in the strict middle band has least eventual state period two.
-/
theorem middle_stair_least_eventual_period_two
    (hG : G.Connected) (sigma : Configuration V)
    (hnonnegative : forall v, 0 <= sigma v)
    (hbandLow :
      2 * (G.edgeFinset.card : Int) - (Fintype.card V : Int) < totalChips sigma)
    (hbandHigh : totalChips sigma < 2 * (G.edgeFinset.card : Int)) :
    HasLeastEventualPeriod G sigma 2 := by
  obtain ⟨mu, T, hT, hperiod⟩ :=
    actualOrbit_eventually_periodic G sigma hnonnegative
  let tau := actualOrbit G sigma mu
  have hreturn_original :
      actualOrbit G sigma (mu + T) = actualOrbit G sigma mu := by
    simpa using hperiod 0
  have hreturn : actualOrbit G tau T = tau := by
    dsimp only [tau]
    rw [← actualOrbit_add]
    exact hreturn_original
  have htau_nonnegative : forall v, 0 <= tau v := by
    exact actualOrbit_nonnegative G sigma hnonnegative mu
  have htotal : totalChips tau = totalChips sigma := by
    exact totalChips_actualOrbit G sigma mu
  have hbandLow_tau :
      2 * (G.edgeFinset.card : Int) - (Fintype.card V : Int) < totalChips tau := by
    rw [htotal]
    exact hbandLow
  have hbandHigh_tau : totalChips tau < 2 * (G.edgeFinset.card : Int) := by
    rw [htotal]
    exact hbandHigh
  obtain ⟨q, hcommon, hqpos, _hqT, hhalf⟩ :=
    returning_cycle_half_activity G hG tau T htau_nonnegative hT hreturn
      hbandLow_tau hbandHigh_tau
  have hcommon_fun :
      firingPrefix (actualFiring G tau) T = fun _ => (q : Int) := by
    funext v
    exact hcommon v
  have hhalf_int : 2 * (q : Int) = (T : Int) := by
    exact_mod_cast hhalf
  have halternates : forall v,
      actualFiring G tau 1 v = 1 - actualFiring G tau 0 v := by
    exact actualFiring_one_eq_one_sub_zero_of_half
      G hT tau hreturn (q : Int) hcommon_fun hhalf_int
  have hreturn_two : actualOrbit G tau 2 = tau :=
    actualOrbit_two_eq_of_firing_complement G tau halternates
  have hreturn_two_original :
      actualOrbit G sigma (mu + 2) = actualOrbit G sigma mu := by
    rw [actualOrbit_add]
    exact hreturn_two
  have htwo : HasEventualPeriod G sigma 2 :=
    hasEventualPeriod_of_returning_tail G sigma mu 2 hreturn_two_original
  have hnotone : ¬ HasEventualPeriod G sigma 1 :=
    not_hasEventualPeriod_one_of_middle_band G hG sigma hnonnegative hbandLow hbandHigh
  exact hasLeastEventualPeriod_two G sigma htwo hnotone

end MiddleStair
