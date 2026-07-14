import MiddleStair.Nonclumpy
import MiddleStair.Orbit
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Applying the cyclic non-clumpiness theorem to an actual orbit

This file contains only the plumbing needed to turn a returning `Nat`-indexed
parallel chip-firing orbit into a cyclic family indexed by `Fin T`.  In
particular, the wrap from the last time to time zero is proved from the return
hypothesis rather than assumed.  At half activity the resulting cyclic firing
words are balanced, hence the closed graph theorem in `Nonclumpy` forces them
to alternate.
-/

namespace MiddleStair

open scoped BigOperators

section PrefixSums

variable {V : Type*}

/-- Pointwise firing prefixes are ordinary sums over `range n`. -/
theorem firingPrefix_apply_eq_sum_range (f : ℕ → Configuration V) (n : ℕ) (v : V) :
    firingPrefix f n v = ∑ k ∈ Finset.range n, f k v := by
  induction n with
  | zero => simp [firingPrefix]
  | succ n ih =>
      rw [firingPrefix]
      change firingPrefix f n v + f n v = _
      rw [ih, Finset.sum_range_succ]

end PrefixSums

section CyclicOrbit

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The actual orbit restricted to one proposed period. -/
noncomputable def cyclicActualState (σ : Configuration V) (T : ℕ) :
    Fin T → Configuration V := fun i => actualOrbit G σ i.1

/-- Boolean firing words on one proposed period. -/
noncomputable def cyclicActualWord (σ : Configuration V) (T : ℕ) :
    V → Fin T → Bool := by
  classical
  exact fun v i => decide (Fires G (actualOrbit G σ i.1) v)

@[simp] theorem cyclicActualWord_eq_true_iff (σ : Configuration V) (T : ℕ)
    (v : V) (i : Fin T) :
    cyclicActualWord G σ T v i = true ↔ Fires G (cyclicActualState G σ T i) v := by
  simp [cyclicActualWord, cyclicActualState]

/-- The integer bit of the cyclic word is the repository's firing indicator. -/
theorem bit_cyclicActualWord (σ : Configuration V) (T : ℕ) (v : V) (i : Fin T) :
    Mischief.bit (cyclicActualWord G σ T v i) = actualFiring G σ i.1 v := by
  classical
  by_cases h : Fires G (actualOrbit G σ i.1) v <;>
    simp [cyclicActualWord, actualFiring, firingIndicator, Mischief.bit, h]

/--
The `Fin T` family really is cyclic: ordinary successors use the recursive
orbit equation, while the last-to-zero edge uses the return hypothesis.
-/
theorem cyclicActualState_step {T : ℕ} (hT : 0 < T) (σ : Configuration V)
    (hreturn : actualOrbit G σ T = σ) :
    ∀ i : Fin T,
      cyclicActualState G σ T (finRotate T i) =
        update G (cyclicActualState G σ T i)
          (fun v => Mischief.bit (cyclicActualWord G σ T v i)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
  intro i
  by_cases hi : i = Fin.last n
  · subst i
    rw [finRotate_last]
    change σ = update G (actualOrbit G σ n)
      (fun v => Mischief.bit (cyclicActualWord G σ (n + 1) v (Fin.last n)))
    calc
      σ = actualOrbit G σ (n + 1) := hreturn.symm
      _ = step G (actualOrbit G σ n) := by rw [actualOrbit_succ]
      _ = update G (actualOrbit G σ n)
          (fun v => Mischief.bit
            (cyclicActualWord G σ (n + 1) v (Fin.last n))) := by
        simp only [step]
        congr 1
        funext v
        rw [bit_cyclicActualWord]
        rfl
  · change actualOrbit G σ (finRotate (n + 1) i).1 =
      update G (actualOrbit G σ i.1)
        (fun v => Mischief.bit (cyclicActualWord G σ (n + 1) v i))
    rw [show (finRotate (n + 1) i).1 = i.1 + 1 from coe_finRotate_of_ne_last hi]
    rw [actualOrbit_succ]
    simp only [step]
    congr 1
    funext v
    rw [bit_cyclicActualWord]
    rfl

/-- The graph-level sector theorem specialized to a returning actual orbit. -/
theorem cyclicActualSector_invariant {T : ℕ} (hT : 0 < T)
    (σ : Configuration V) (hreturn : actualOrbit G σ T = σ) :
    ∀ v i,
      canonicalSector (finRotate T) (cyclicActualWord G σ T v) (finRotate T i) =
        canonicalSector (finRotate T) (cyclicActualWord G σ T v) i := by
  apply cyclic_chipFiring_sector_invariant G (finRotate T)
    (cyclicActualState G σ T) (cyclicActualWord G σ T)
  · exact cyclicActualWord_eq_true_iff G σ T
  · exact cyclicActualState_step G hT σ hreturn

/-- The closed JSZ theorem supplies non-clumpiness for each actual firing word. -/
theorem cyclicActualWord_nonclumpy {T : ℕ} (hT : 0 < T)
    (σ : Configuration V) (hreturn : actualOrbit G σ T = σ) :
    ∀ v, NonclumpyWord (finRotate T) (cyclicActualWord G σ T v) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
  exact cyclic_chipFiring_nonclumpy G
    (cyclicActualState G σ (n + 1)) (cyclicActualWord G σ (n + 1))
    (cyclicActualWord_eq_true_iff G σ (n + 1))
    (cyclicActualState_step G (Nat.succ_pos n) σ hreturn)

/-- Summing a cyclic Boolean firing word gives the usual prefix firing count. -/
theorem sum_bit_cyclicActualWord (σ : Configuration V) (T : ℕ) (v : V) :
    (∑ i : Fin T, Mischief.bit (cyclicActualWord G σ T v i)) =
      firingPrefix (actualFiring G σ) T v := by
  rw [firingPrefix_apply_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  exact bit_cyclicActualWord G σ T v i

/-- The cardinality of the `true` positions is the integer bit sum. -/
theorem int_card_onePositions_eq_sum_bit {T : ℕ} (word : Fin T → Bool) :
    ((onePositions word).card : ℤ) = ∑ i, Mischief.bit (word i) := by
  classical
  simp [onePositions, Mischief.bit]

/-- The cardinality of the `false` positions is the complementary bit sum. -/
theorem int_card_zeroPositions_eq_sum_one_sub_bit {T : ℕ} (word : Fin T → Bool) :
    ((zeroPositions word).card : ℤ) = ∑ i, (1 - Mischief.bit (word i)) := by
  classical
  have hpart :
      (zeroPositions word).card + (onePositions word).card = T := by
    simpa [zeroPositions, onePositions] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin T))) (p := fun i => word i = false))
  have hpartZ :
      ((zeroPositions word).card : ℤ) + ((onePositions word).card : ℤ) = T := by
    exact_mod_cast hpart
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  rw [← int_card_onePositions_eq_sum_bit]
  omega

/-- A common count equal to half the period makes every cyclic word balanced. -/
theorem cyclicActualWord_balanced_of_half {T : ℕ} (σ : Configuration V) (q : ℤ)
    (hcommon : firingPrefix (actualFiring G σ) T = fun _ => q)
    (hhalf : 2 * q = (T : ℤ)) :
    ∀ v, BalancedWord (cyclicActualWord G σ T v) := by
  intro v
  have hsum : (∑ i : Fin T,
      Mischief.bit (cyclicActualWord G σ T v i)) = q := by
    rw [sum_bit_cyclicActualWord G σ T v, congrFun hcommon v]
  apply Nat.cast_injective (R := ℤ)
  rw [int_card_zeroPositions_eq_sum_one_sub_bit,
    int_card_onePositions_eq_sum_bit]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  rw [hsum]
  omega

/--
Every cyclic firing word of a returning half-activity orbit alternates.  This
is the all-times cyclic form, including the last-to-zero edge.
-/
theorem cyclicActualWord_alternates_of_half {T : ℕ} (hT : 0 < T)
    (σ : Configuration V) (hreturn : actualOrbit G σ T = σ) (q : ℤ)
    (hcommon : firingPrefix (actualFiring G σ) T = fun _ => q)
    (hhalf : 2 * q = (T : ℤ)) :
    ∀ v i,
      cyclicActualWord G σ T v (finRotate T i) =
        !(cyclicActualWord G σ T v i) := by
  intro v
  exact balanced_nonclumpy_word_alternates (finRotate T)
    (cyclicActualWord G σ T v)
    (cyclicActualWord_balanced_of_half G σ q hcommon hhalf v)
    (cyclicActualWord_nonclumpy G hT σ hreturn v)

/-- Integer-valued actual firing indicators alternate on every cyclic edge. -/
theorem cyclicActualFiring_alternates_of_half {T : ℕ} (hT : 0 < T)
    (σ : Configuration V) (hreturn : actualOrbit G σ T = σ) (q : ℤ)
    (hcommon : firingPrefix (actualFiring G σ) T = fun _ => q)
    (hhalf : 2 * q = (T : ℤ)) :
    ∀ v i,
      actualFiring G σ (finRotate T i).1 v =
        1 - actualFiring G σ i.1 v := by
  intro v i
  have halt := cyclicActualWord_alternates_of_half G hT σ hreturn q hcommon hhalf v i
  calc
    actualFiring G σ (finRotate T i).1 v =
        Mischief.bit (cyclicActualWord G σ T v (finRotate T i)) :=
      (bit_cyclicActualWord G σ T v (finRotate T i)).symm
    _ = Mischief.bit (!(cyclicActualWord G σ T v i)) := by rw [halt]
    _ = 1 - Mischief.bit (cyclicActualWord G σ T v i) := by
      cases cyclicActualWord G σ T v i <;> rfl
    _ = 1 - actualFiring G σ i.1 v := by rw [bit_cyclicActualWord]

/-- In particular, the firing vectors at rounds zero and one are complements. -/
theorem actualFiring_one_eq_one_sub_zero_of_half {T : ℕ} (hT : 0 < T)
    (σ : Configuration V) (hreturn : actualOrbit G σ T = σ) (q : ℤ)
    (hcommon : firingPrefix (actualFiring G σ) T = fun _ => q)
    (hhalf : 2 * q = (T : ℤ)) :
    ∀ v, actualFiring G σ 1 v = 1 - actualFiring G σ 0 v := by
  have hTz : (0 : ℤ) < (T : ℤ) := by exact_mod_cast hT
  have hTtwo : 2 ≤ T := by omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
  have hn : 0 < n := by omega
  let i0 : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
  have hnotlast : i0 ≠ Fin.last n := by
    intro heq
    have hval := congrArg Fin.val heq
    change (0 : ℕ) = n at hval
    omega
  have hrotate : (finRotate (n + 1) i0).1 = 1 := by
    simpa [i0] using coe_finRotate_of_ne_last hnotlast
  intro v
  have hcyclic := cyclicActualFiring_alternates_of_half G hT σ hreturn q
    hcommon hhalf v i0
  rw [hrotate] at hcyclic
  change actualFiring G σ 1 v = 1 - actualFiring G σ 0 v at hcyclic
  exact hcyclic

end CyclicOrbit

end MiddleStair
