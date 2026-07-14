import MiddleStair.Dynamics
import MiddleStair.Mischief
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.FixedPoints

/-!
# Cyclic binary words and the non-clumpiness interface

This file proves the finite combinatorial consequence used at the end of the
middle-stair argument.  It is deliberately formulated for an arbitrary finite
set equipped with a permutation: cyclic successor on `Fin T` is one instance.

The graph-dynamical theorem that periodic parallel chip-firing words are
non-clumpy is proved below from the finite Jiang--Scully--Zhang mischief
certificate in `MiddleStair.Mischief`.  It is not imported as a hypothesis or
project axiom.
-/

namespace MiddleStair

section CyclicWords

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positions carrying a one in a finite binary word. -/
def onePositions (word : ι → Bool) : Finset ι :=
  Finset.univ.filter fun i => word i = true

/-- Positions carrying a zero in a finite binary word. -/
def zeroPositions (word : ι → Bool) : Finset ι :=
  Finset.univ.filter fun i => word i = false

/-- A finite binary word is balanced when it has equally many zeros and ones. -/
def BalancedWord (word : ι → Bool) : Prop :=
  (zeroPositions word).card = (onePositions word).card

/-- The cyclic/permutation word has no adjacent copy of the bit `b`. -/
def NoAdjacentBit (next : Equiv.Perm ι) (word : ι → Bool) (b : Bool) : Prop :=
  ∀ i, ¬(word i = b ∧ word (next i) = b)

/-- A word is non-clumpy when it lacks cyclic `00` or lacks cyclic `11`. -/
def NonclumpyWord (next : Equiv.Perm ι) (word : ι → Bool) : Prop :=
  NoAdjacentBit next word false ∨ NoAdjacentBit next word true

private theorem next_zeroPositions_eq_onePositions_of_no_zero_pair
    (next : Equiv.Perm ι) (word : ι → Bool)
    (hbalanced : BalancedWord word)
    (hno : NoAdjacentBit next word false) :
    (zeroPositions word).image next = onePositions word := by
  have hsubset : (zeroPositions word).image next ⊆ onePositions word := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    have hxzero : word x = false := (Finset.mem_filter.mp hx).2
    have hnext : word (next x) = true := by
      cases h : word (next x) with
      | false => exact False.elim (hno x ⟨hxzero, h⟩)
      | true => rfl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnext⟩
  have hcard : ((zeroPositions word).image next).card =
      (onePositions word).card := by
    rw [Finset.card_image_of_injective _ next.injective]
    exact hbalanced
  exact Finset.eq_of_subset_of_card_le hsubset hcard.ge

private theorem next_onePositions_eq_zeroPositions_of_no_one_pair
    (next : Equiv.Perm ι) (word : ι → Bool)
    (hbalanced : BalancedWord word)
    (hno : NoAdjacentBit next word true) :
    (onePositions word).image next = zeroPositions word := by
  have hsubset : (onePositions word).image next ⊆ zeroPositions word := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    have hxone : word x = true := (Finset.mem_filter.mp hx).2
    have hnext : word (next x) = false := by
      cases h : word (next x) with
      | false => rfl
      | true => exact False.elim (hno x ⟨hxone, h⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnext⟩
  have hcard : ((onePositions word).image next).card =
      (zeroPositions word).card := by
    rw [Finset.card_image_of_injective _ next.injective]
    exact hbalanced.symm
  exact Finset.eq_of_subset_of_card_le hsubset hcard.ge

/-- A balanced cyclic non-clumpy binary word alternates pointwise. -/
theorem balanced_nonclumpy_word_alternates
    (next : Equiv.Perm ι) (word : ι → Bool)
    (hbalanced : BalancedWord word) (hnonclumpy : NonclumpyWord next word) :
    ∀ i, word (next i) = !word i := by
  rcases hnonclumpy with hnozero | hnoone
  · have hsets :=
      next_zeroPositions_eq_onePositions_of_no_zero_pair next word hbalanced hnozero
    intro i
    cases hi : word i with
    | false =>
        have hnext : word (next i) = true := by
          cases hn : word (next i) with
          | false => exact False.elim (hnozero i ⟨hi, hn⟩)
          | true => rfl
        simp [hnext]
    | true =>
        have hnext : word (next i) = false := by
          cases hn : word (next i) with
          | false => rfl
          | true =>
              have hmem : next i ∈ onePositions word :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
              rw [← hsets] at hmem
              rcases Finset.mem_image.mp hmem with ⟨j, hj, hji⟩
              have hji' : j = i := next.injective hji
              subst j
              have hjzero : word i = false := (Finset.mem_filter.mp hj).2
              simp_all
        simp [hnext]
  · have hsets :=
      next_onePositions_eq_zeroPositions_of_no_one_pair next word hbalanced hnoone
    intro i
    cases hi : word i with
    | false =>
        have hnext : word (next i) = true := by
          cases hn : word (next i) with
          | true => rfl
          | false =>
              have hmem : next i ∈ zeroPositions word :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
              rw [← hsets] at hmem
              rcases Finset.mem_image.mp hmem with ⟨j, hj, hji⟩
              have hji' : j = i := next.injective hji
              subst j
              have hjone : word i = true := (Finset.mem_filter.mp hj).2
              simp_all
        simp [hnext]
    | true =>
        have hnext : word (next i) = false := by
          cases hn : word (next i) with
          | false => rfl
          | true => exact False.elim (hnoone i ⟨hi, hn⟩)
        simp [hnext]

end CyclicWords

section Sectors

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
The sector recurrence, viewed as a monotone endomorphism of Boolean labelings.
At a repeated bit the label is forced to that bit; along an alternating run
the label is copied backwards from the next position.
-/
def sectorOperator (next : Equiv.Perm ι) (word : ι → Bool) :
    (ι → Bool) →o (ι → Bool) where
  toFun sector i :=
    if word (next.symm i) = word i then word i else sector (next i)
  monotone' := by
    intro a b hab i
    dsimp
    split
    · exact le_rfl
    · exact hab (next i)

/-- A canonical sector labeling, obtained without an existence hypothesis. -/
noncomputable def canonicalSector (next : Equiv.Perm ι) (word : ι → Bool) :
    ι → Bool :=
  (sectorOperator next word).lfp

/-- The Boolean form of the two local sector constraints used by `Mischief.valid`. -/
def SectorValid (next : Equiv.Perm ι) (word sector : ι → Bool) : Prop :=
  ∀ i,
    (if word (next.symm i) == word i then
        word (next.symm i) == sector i
      else sector i == sector (next i)) = true

theorem canonicalSector_fixed (next : Equiv.Perm ι) (word : ι → Bool) :
    sectorOperator next word (canonicalSector next word) =
      canonicalSector next word :=
  (sectorOperator next word).map_lfp

/-- The least fixed point supplies a valid sector decomposition for every word. -/
theorem canonicalSector_valid (next : Equiv.Perm ι) (word : ι → Bool) :
    SectorValid next word (canonicalSector next word) := by
  intro i
  have hfix := congrFun (canonicalSector_fixed next word) i
  by_cases h : word (next.symm i) = word i
  · have hi : word i = canonicalSector next word i := by
      simpa [sectorOperator, h] using hfix
    simp [h, hi]
  · have hi : canonicalSector next word (next i) =
        canonicalSector next word i := by
      simpa [sectorOperator, h] using hfix
    simp [h, hi]

theorem canonicalSector_eq_of_prev_eq (next : Equiv.Perm ι) (word : ι → Bool)
    (i : ι) (h : word (next.symm i) = word i) :
    canonicalSector next word i = word i := by
  have hfix := congrFun (canonicalSector_fixed next word) i
  simpa [sectorOperator, h] using hfix.symm

/-- The number of sector switches, represented as an integer sum of zero-one terms. -/
def sectorSwitchSum (next : Equiv.Perm ι) (sector : ι → Bool) : ℤ :=
  ∑ i, Mischief.sectorSwitch (sector i) (sector (next i))

/-- The per-vertex expression obtained after summing directed mischief over neighbors. -/
def sectorEnergy (next : Equiv.Perm ι) (sector : ι → Bool)
    (d : ℤ) (A : ι → ℤ) : ℤ :=
  ∑ i, (
    Mischief.sign (sector i) * (A (next.symm i) - A i) -
      d * Mischief.sectorSwitch (sector i) (sector (next i)))

/--
The short global-potential estimate.  Notice that no uniform box bound on `A`
is assumed.  At a `0 → 1` sector switch validity forces the current firing bit
to be zero, so only the waiting upper bound is used.  At a `1 → 0` switch it
forces the firing bit to be one, so only the firing lower bound is used.
-/
theorem sectorEnergy_le_neg_switchSum
    (next : Equiv.Perm ι) (word sector : ι → Bool) (d : ℤ) (A : ι → ℤ)
    (hvalid : SectorValid next word sector)
    (hfire : ∀ i, word i = true → 0 ≤ A i)
    (hwait : ∀ i, word i = false → A i ≤ d - 1) :
    sectorEnergy next sector d A ≤ -sectorSwitchSum next sector := by
  have hsign :
      (∑ i, Mischief.sign (sector (next i)) * A i) =
        ∑ i, Mischief.sign (sector i) * A (next.symm i) := by
    simpa using Equiv.sum_comp next
      (fun i => Mischief.sign (sector i) * A (next.symm i))
  have hbit :
      (∑ i, Mischief.bit (sector (next i))) =
        ∑ i, Mischief.bit (sector i) := by
    exact Equiv.sum_comp next (fun i => Mischief.bit (sector i))
  have hpoint : ∀ i,
      (Mischief.sign (sector (next i)) - Mischief.sign (sector i)) * A i -
          d * Mischief.sectorSwitch (sector i) (sector (next i)) ≤
        (d - 1) *
            (Mischief.bit (sector (next i)) - Mischief.bit (sector i)) -
          Mischief.sectorSwitch (sector i) (sector (next i)) := by
    intro i
    have hv := hvalid i
    cases hn : word i
    · have hA := hwait i hn
      have hA2 : 2 * A i ≤ 2 * (d - 1) := by linarith
      cases hp : word (next.symm i) <;>
      cases hs : sector i <;>
      cases hsn : sector (next i) <;>
      simp [SectorValid, hp, hn, hs, hsn, Mischief.sign, Mischief.bit,
        Mischief.sectorSwitch] at hv ⊢ <;>
      linarith [hA2]
    · have hA := hfire i hn
      cases hp : word (next.symm i) <;>
      cases hs : sector i <;>
      cases hsn : sector (next i) <;>
      simp [SectorValid, hp, hn, hs, hsn, Mischief.sign, Mischief.bit,
        Mischief.sectorSwitch] at hv ⊢ <;>
      linarith [hA]
  calc
    sectorEnergy next sector d A =
        ∑ i, (
          (Mischief.sign (sector (next i)) - Mischief.sign (sector i)) * A i -
            d * Mischief.sectorSwitch (sector i) (sector (next i))) := by
      simp only [sectorEnergy]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      rw [← hsign]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ ≤ ∑ i, (
        (d - 1) *
            (Mischief.bit (sector (next i)) - Mischief.bit (sector i)) -
          Mischief.sectorSwitch (sector i) (sector (next i))) := by
      exact Finset.sum_le_sum fun i _ => hpoint i
    _ = -sectorSwitchSum next sector := by
      simp only [sectorSwitchSum]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum, hbit]
      ring

end Sectors

section GraphBridge

variable {V ι : Type*} [Fintype V] [DecidableEq V]
variable [Fintype ι] [DecidableEq ι]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The Jiang--Scully--Zhang local state attached to two firing words at one time. -/
def pairLocalState (next : Equiv.Perm ι) (word sector : V → ι → Bool)
    (v w : V) (i : ι) : Mischief.LocalState :=
  Mischief.encode
    (word v (next.symm i)) (word v i) (sector v i) (sector v (next i))
    (word w (next.symm i)) (word w i) (sector w i) (sector w (next i))

/-- One directed half of a local mischief weight. -/
def directedMischief (next : Equiv.Perm ι) (word sector : V → ι → Bool)
    (v w : V) (i : ι) : ℤ :=
  Mischief.sign (sector v i) *
      (Mischief.bit (word v i) - Mischief.bit (word w (next.symm i))) -
    Mischief.sectorSwitch (sector v i) (sector v (next i))

theorem pairLocalState_valid
    (next : Equiv.Perm ι) (word sector : V → ι → Bool)
    (hvalid : ∀ v, SectorValid next (word v) (sector v))
    (v w : V) (i : ι) :
    Mischief.valid (pairLocalState next word sector v w i) = true := by
  have hv := hvalid v i
  have hw := hvalid w i
  simpa [pairLocalState, Mischief.valid] using
    (Bool.and_eq_true_iff.mpr ⟨hv, hw⟩)

theorem pairLocalState_follows
    (next : Equiv.Perm ι) (word sector : V → ι → Bool)
    (v w : V) (i : ι) :
    Mischief.follows (pairLocalState next word sector v w i)
      (pairLocalState next word sector v w (next i)) = true := by
  simp [pairLocalState, Mischief.follows]

theorem pairLocalState_weight
    (next : Equiv.Perm ι) (word sector : V → ι → Bool)
    (v w : V) (i : ι) :
    Mischief.weight (pairLocalState next word sector v w i) =
      directedMischief next word sector v w i +
        directedMischief next word sector w v i := by
  simp [pairLocalState, directedMischief, Mischief.weight]
  ring

/-- Mischief of every pair of valid cyclic words is nonnegative. -/
theorem pairMischief_nonnegative
    (next : Equiv.Perm ι) (word sector : V → ι → Bool)
    (hvalid : ∀ v, SectorValid next (word v) (sector v))
    (v w : V) :
    0 ≤ ∑ i, Mischief.weight (pairLocalState next word sector v w i) := by
  exact Mischief.sum_weight_nonnegative next
    (pairLocalState next word sector v w)
    (pairLocalState_valid next word sector hvalid v w)
    (pairLocalState_follows next word sector v w)

/-- Reversing all oriented edges preserves their total weight. -/
theorem sum_neighbor_swap (F : V → V → ℤ) :
    (∑ v, ∑ w ∈ G.neighborFinset v, F v w) =
      ∑ v, ∑ w ∈ G.neighborFinset v, F w v := by
  classical
  simp_rw [G.neighborFinset_eq_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : G.Adj v w
  · simp [h, G.adj_comm]
  · simp [h, G.adj_comm]

/-- The ordered-edge mischief total is twice its directed half. -/
theorem total_pairMischief_eq_two_directed
    (next : Equiv.Perm ι) (word sector : V → ι → Bool) :
    (∑ v, ∑ w ∈ G.neighborFinset v,
        ∑ i, Mischief.weight (pairLocalState next word sector v w i)) =
      2 * (∑ v, ∑ w ∈ G.neighborFinset v,
        ∑ i, directedMischief next word sector v w i) := by
  simp_rw [pairLocalState_weight, Finset.sum_add_distrib]
  have hswap := sum_neighbor_swap G
    (fun v w => ∑ i, directedMischief next word sector v w i)
  rw [← hswap]
  ring

/-- The directed total is the sum of the per-vertex sector energies. -/
theorem total_directedMischief_eq_sectorEnergy
    (next : Equiv.Perm ι) (word sector : V → ι → Bool) (A : V → ι → ℤ)
    (hrec : ∀ v i,
      (G.degree v : ℤ) * Mischief.bit (word v i) -
          ∑ w ∈ G.neighborFinset v, Mischief.bit (word w (next.symm i)) =
        A v (next.symm i) - A v i) :
    (∑ v, ∑ w ∈ G.neighborFinset v,
        ∑ i, directedMischief next word sector v w i) =
      ∑ v, sectorEnergy next (sector v) (G.degree v : ℤ) (A v) := by
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [directedMischief, sectorEnergy]
  calc
    (∑ w ∈ G.neighborFinset v,
        (Mischief.sign (sector v i) *
            (Mischief.bit (word v i) -
              Mischief.bit (word w (next.symm i))) -
          Mischief.sectorSwitch (sector v i) (sector v (next i)))) =
        Mischief.sign (sector v i) *
            ((G.degree v : ℤ) * Mischief.bit (word v i) -
              ∑ w ∈ G.neighborFinset v,
                Mischief.bit (word w (next.symm i))) -
          (G.degree v : ℤ) *
            Mischief.sectorSwitch (sector v i) (sector v (next i)) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      simp [G.card_neighborFinset_eq_degree]
      rw [Finset.mul_sum]
      ring
    _ = Mischief.sign (sector v i) *
          (A v (next.symm i) - A v i) -
        (G.degree v : ℤ) *
          Mischief.sectorSwitch (sector v i) (sector v (next i)) := by
      rw [hrec v i]

/--
Closed graph-level JSZ bridge.  A cyclic family of states following the actual
threshold rule has no switches in its canonical sector decomposition.
-/
theorem cyclic_chipFiring_sector_invariant
    (next : Equiv.Perm ι) (state : ι → Configuration V)
    (word : V → ι → Bool)
    (hthreshold : ∀ v i, word v i = true ↔ Fires G (state i) v)
    (hstep : ∀ i,
      state (next i) =
        update G (state i) (fun v => Mischief.bit (word v i))) :
    ∀ v i,
      canonicalSector next (word v) (next i) =
        canonicalSector next (word v) i := by
  let sector : V → ι → Bool := fun v => canonicalSector next (word v)
  let A : V → ι → ℤ := fun v i =>
    state i v - (G.degree v : ℤ) * Mischief.bit (word v i)
  have hvalid : ∀ v, SectorValid next (word v) (sector v) := by
    intro v
    exact canonicalSector_valid next (word v)
  have hrec : ∀ v i,
      (G.degree v : ℤ) * Mischief.bit (word v i) -
          ∑ w ∈ G.neighborFinset v, Mischief.bit (word w (next.symm i)) =
        A v (next.symm i) - A v i := by
    intro v i
    have hs := congrFun (hstep (next.symm i)) v
    simp only [next.apply_symm_apply, update, Pi.sub_apply, laplacian] at hs
    have hsum :
        (∑ w ∈ G.neighborFinset v,
            (Mischief.bit (word v (next.symm i)) -
              Mischief.bit (word w (next.symm i)))) =
          (G.degree v : ℤ) * Mischief.bit (word v (next.symm i)) -
            ∑ w ∈ G.neighborFinset v,
              Mischief.bit (word w (next.symm i)) := by
      rw [Finset.sum_sub_distrib]
      simp [G.card_neighborFinset_eq_degree]
    rw [hsum] at hs
    dsimp [A]
    linarith
  have hfire : ∀ v i, word v i = true → 0 ≤ A v i := by
    intro v i hi
    have hFires : Fires G (state i) v := (hthreshold v i).mp hi
    simp only [Fires] at hFires
    simp [A, hi, Mischief.bit]
    linarith
  have hwait : ∀ v i, word v i = false → A v i ≤ (G.degree v : ℤ) - 1 := by
    intro v i hi
    have hnot : ¬ Fires G (state i) v := by
      intro hFires
      have hone : word v i = true := (hthreshold v i).mpr hFires
      simp_all
    simp only [Fires, not_le] at hnot
    simp [A, hi, Mischief.bit]
    omega
  have hmischief :
      0 ≤ ∑ v, ∑ w ∈ G.neighborFinset v,
        ∑ i, Mischief.weight (pairLocalState next word sector v w i) := by
    exact Finset.sum_nonneg fun v _ =>
      Finset.sum_nonneg fun w _ =>
        pairMischief_nonnegative next word sector hvalid v w
  have htwo := total_pairMischief_eq_two_directed G next word sector
  have henergy := total_directedMischief_eq_sectorEnergy G next word sector A hrec
  have henergy_nonneg :
      0 ≤ ∑ v, sectorEnergy next (sector v) (G.degree v : ℤ) (A v) := by
    rw [htwo, henergy] at hmischief
    linarith
  have henergy_le :
      (∑ v, sectorEnergy next (sector v) (G.degree v : ℤ) (A v)) ≤
        -∑ v, sectorSwitchSum next (sector v) := by
    calc
      (∑ v, sectorEnergy next (sector v) (G.degree v : ℤ) (A v)) ≤
          ∑ v, -sectorSwitchSum next (sector v) := by
        exact Finset.sum_le_sum fun v _ =>
          sectorEnergy_le_neg_switchSum next (word v) (sector v)
            (G.degree v : ℤ) (A v) (hvalid v) (hfire v) (hwait v)
      _ = -∑ v, sectorSwitchSum next (sector v) := by
        rw [Finset.sum_neg_distrib]
  have hswitch_nonneg : 0 ≤ ∑ v, sectorSwitchSum next (sector v) := by
    exact Finset.sum_nonneg fun v _ =>
      Finset.sum_nonneg fun i _ => by
        by_cases h : sector v i = sector v (next i) <;>
          simp [Mischief.sectorSwitch, h]
  have hswitch_zero : ∑ v, sectorSwitchSum next (sector v) = 0 := by
    apply le_antisymm
    · linarith
    · exact hswitch_nonneg
  have hvzero : ∀ v, sectorSwitchSum next (sector v) = 0 := by
    have hfun := (Fintype.sum_eq_zero_iff_of_nonneg fun v =>
      Finset.sum_nonneg fun i _ => by
        by_cases h : sector v i = sector v (next i) <;>
          simp [Mischief.sectorSwitch, h]).mp hswitch_zero
    exact fun v => congrFun hfun v
  intro v i
  have hizero :
      Mischief.sectorSwitch (sector v i) (sector v (next i)) = 0 := by
    have hnonneg : ∀ j, 0 ≤
        Mischief.sectorSwitch (sector v j) (sector v (next j)) := by
      intro j
      by_cases h : sector v j = sector v (next j) <;>
        simp [Mischief.sectorSwitch, h]
    have hsum : (∑ j,
        Mischief.sectorSwitch (sector v j) (sector v (next j))) = 0 := by
      simpa [sectorSwitchSum] using hvzero v
    have hfun := (Fintype.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
    exact congrFun hfun i
  have heq : sector v i = sector v (next i) := by
    simpa [Mischief.sectorSwitch] using hizero
  exact heq.symm

end GraphBridge

section FinCycle

/-- A function invariant under `finRotate` is constant on the finite cycle. -/
theorem finRotate_invariant_constant {n : ℕ} {α : Type*}
    (s : Fin (n + 1) → α)
    (hinvariant : ∀ i, s (finRotate (n + 1) i) = s i) :
    ∀ i j, s i = s j := by
  intro i j
  have hiterate : ∀ k : ℕ, s ((finRotate (n + 1))^[k] i) = s i := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        rw [hinvariant]
        exact ih
  let k : Fin (n + 1) := j - i
  have hrotate : (finRotate (n + 1))^[k.val] i = j := by
    rw [← finCycle_eq_finRotate_iterate]
    simp [k]
  calc
    s i = s ((finRotate (n + 1))^[k.val] i) := (hiterate k.val).symm
    _ = s j := congrArg s hrotate

/--
On one finite cyclic time axis, an invariant valid sector labeling rules out a
word containing both a cyclic `00` and a cyclic `11`.
-/
theorem nonclumpy_of_canonicalSector_invariant {n : ℕ}
    (word : Fin (n + 1) → Bool)
    (hinvariant : ∀ i,
      canonicalSector (finRotate (n + 1)) word (finRotate (n + 1) i) =
        canonicalSector (finRotate (n + 1)) word i) :
    NonclumpyWord (finRotate (n + 1)) word := by
  by_contra hclumpy
  have hboth := not_or.mp (show ¬
    (NoAdjacentBit (finRotate (n + 1)) word false ∨
      NoAdjacentBit (finRotate (n + 1)) word true) by
        simpa [NonclumpyWord] using hclumpy)
  have hzero : ∃ i,
      word i = false ∧ word (finRotate (n + 1) i) = false := by
    simpa [NoAdjacentBit] using hboth.1
  have hone : ∃ i,
      word i = true ∧ word (finRotate (n + 1) i) = true := by
    simpa [NoAdjacentBit] using hboth.2
  obtain ⟨i₀, hi₀, hnext₀⟩ := hzero
  obtain ⟨i₁, hi₁, hnext₁⟩ := hone
  let sector := canonicalSector (finRotate (n + 1)) word
  have hs₀ : sector (finRotate (n + 1) i₀) = false := by
    change canonicalSector (finRotate (n + 1)) word
      (finRotate (n + 1) i₀) = false
    calc
      canonicalSector (finRotate (n + 1)) word (finRotate (n + 1) i₀) =
          word (finRotate (n + 1) i₀) :=
        canonicalSector_eq_of_prev_eq _ _ _ (by
          rw [Equiv.symm_apply_apply, hi₀, hnext₀])
      _ = false := hnext₀
  have hs₁ : sector (finRotate (n + 1) i₁) = true := by
    change canonicalSector (finRotate (n + 1)) word
      (finRotate (n + 1) i₁) = true
    calc
      canonicalSector (finRotate (n + 1)) word (finRotate (n + 1) i₁) =
          word (finRotate (n + 1) i₁) :=
        canonicalSector_eq_of_prev_eq _ _ _ (by
          rw [Equiv.symm_apply_apply, hi₁, hnext₁])
      _ = true := hnext₁
  have hconstant := finRotate_invariant_constant sector hinvariant
  have := hconstant (finRotate (n + 1) i₀) (finRotate (n + 1) i₁)
  rw [hs₀, hs₁] at this
  contradiction

/-- Closed non-clumpiness theorem for a finite cyclic threshold orbit. -/
theorem cyclic_chipFiring_nonclumpy {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (state : Fin (n + 1) → Configuration V)
    (word : V → Fin (n + 1) → Bool)
    (hthreshold : ∀ v i, word v i = true ↔ Fires G (state i) v)
    (hstep : ∀ i,
      state (finRotate (n + 1) i) =
        update G (state i) (fun v => Mischief.bit (word v i))) :
    ∀ v, NonclumpyWord (finRotate (n + 1)) (word v) := by
  have hinvariant := cyclic_chipFiring_sector_invariant G
    (finRotate (n + 1)) state word hthreshold hstep
  intro v
  exact nonclumpy_of_canonicalSector_invariant (word v) (hinvariant v)

end FinCycle

section ReturningCycle

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The Boolean firing word of a supplied actual `evolve` cycle. -/
noncomputable def evolveFiringWord (σ : Configuration V) (f : ℕ → Configuration V)
    {T : ℕ} (v : V) (i : Fin T) : Bool := by
  classical
  exact if Fires G (evolve G σ f i.val) v then true else false

theorem bit_evolveFiringWord (σ : Configuration V) (f : ℕ → Configuration V)
    {T : ℕ} (v : V) (i : Fin T) :
    Mischief.bit (evolveFiringWord G σ f v i) =
      firingIndicator G (evolve G σ f i.val) v := by
  classical
  by_cases h : Fires G (evolve G σ f i.val) v <;>
    simp [evolveFiringWord, Mischief.bit, firingIndicator, h]

/--
Repository-native non-clumpiness theorem.  The hypotheses are exactly an
actual supplied threshold trajectory and its return after the positive period;
no sector labeling, chip bound, activity inequality, or non-clumpiness premise
is assumed.
-/
theorem returning_evolve_firing_words_nonclumpy_succ
    (σ : Configuration V) (f : ℕ → Configuration V) (n : ℕ)
    (actual : ∀ t, t < n + 1 →
      f t = firingIndicator G (evolve G σ f t))
    (returns : evolve G σ f (n + 1) = σ) :
    ∀ v, NonclumpyWord (finRotate (n + 1))
      (evolveFiringWord G σ f v) := by
  apply cyclic_chipFiring_nonclumpy G
    (state := fun i : Fin (n + 1) => evolve G σ f i.val)
    (word := fun v => evolveFiringWord G σ f v)
  · intro v i
    simp [evolveFiringWord]
  · intro i
    have hf :
        (fun v => Mischief.bit (evolveFiringWord G σ f v i)) = f i.val := by
      rw [actual i.val i.isLt]
      funext v
      exact bit_evolveFiringWord G σ f v i
    rw [hf]
    by_cases hi : i = Fin.last n
    · subst i
      rw [finRotate_last]
      simpa [evolve] using returns.symm
    · have hval := coe_finRotate_of_ne_last hi
      change evolve G σ f (finRotate (n + 1) i).val =
        update G (evolve G σ f i.val) (f i.val)
      rw [hval]
      rfl

theorem returning_evolve_firing_words_nonclumpy
    (σ : Configuration V) (f : ℕ → Configuration V) (T : ℕ)
    (hT : 0 < T)
    (actual : ∀ t, t < T →
      f t = firingIndicator G (evolve G σ f t))
    (returns : evolve G σ f T = σ) :
    ∀ v, NonclumpyWord (finRotate T) (evolveFiringWord G σ f v) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
  exact returning_evolve_firing_words_nonclumpy_succ G σ f n actual returns

end ReturningCycle

end MiddleStair
