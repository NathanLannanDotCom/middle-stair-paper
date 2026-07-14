import MiddleStair.Dynamics
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Actual parallel chip-firing orbits

This file supplies the orbit-level facts which are deliberately absent from
`MiddleStair.Dynamics`: legality of the deterministic threshold update,
conservation of chips, eventual periodicity on a finite graph, and equality
of the firing counts on a connected periodic orbit.

Configurations remain integer-valued.  Legality is expressed by a pointwise
nonnegativity hypothesis and is proved to be invariant under `step`.
-/

namespace MiddleStair

open scoped BigOperators

section OneStep

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Pointwise expansion of the combinatorial Laplacian. -/
theorem laplacian_apply_eq_degree_mul_sub_sum (f : Configuration V) (v : V) :
    laplacian G f v =
      (G.degree v : ℤ) * f v - ∑ w ∈ G.neighborFinset v, f w := by
  simp only [laplacian, Finset.sum_sub_distrib]
  simp [G.card_neighborFinset_eq_degree]

/-- The local Laplacian used here is the usual Laplacian matrix action. -/
theorem laplacian_eq_lapMatrix_mulVec (f : Configuration V) :
    laplacian G f = Matrix.mulVec (G.lapMatrix ℤ) f := by
  funext v
  rw [laplacian_apply_eq_degree_mul_sub_sum, G.lapMatrix_mulVec_apply]

theorem firingIndicator_nonnegative (σ : Configuration V) (v : V) :
    0 ≤ firingIndicator G σ v := by
  rcases firingIndicator_eq_zero_or_one G σ v with h | h <;> omega

theorem firingIndicator_le_one (σ : Configuration V) (v : V) :
    firingIndicator G σ v ≤ 1 := by
  rcases firingIndicator_eq_zero_or_one G σ v with h | h <;> omega

/-- A useful local normal form for the deterministic update. -/
theorem step_apply (σ : Configuration V) (v : V) :
    step G σ v = σ v - (G.degree v : ℤ) * firingIndicator G σ v +
      ∑ w ∈ G.neighborFinset v, firingIndicator G σ w := by
  rw [step, update]
  simp only [Pi.sub_apply, laplacian_apply_eq_degree_mul_sub_sum]
  ring

/-- A legal (nonnegative) integer configuration stays legal for one step. -/
theorem step_nonnegative (σ : Configuration V)
    (hσ : ∀ v, 0 ≤ σ v) : ∀ v, 0 ≤ step G σ v := by
  classical
  intro v
  rw [step_apply]
  have hsum : 0 ≤ ∑ w ∈ G.neighborFinset v, firingIndicator G σ w :=
    Finset.sum_nonneg fun w _ => firingIndicator_nonnegative G σ w
  by_cases hv : Fires G σ v
  · have hfire : firingIndicator G σ v = 1 := by
      simp [firingIndicator, hv]
    rw [hfire]
    have hthreshold : (G.degree v : ℤ) ≤ σ v := hv
    omega
  · have hwait : firingIndicator G σ v = 0 := by
      simp [firingIndicator, hv]
    rw [hwait]
    have := hσ v
    omega

/-- Every Laplacian vector has coordinate sum zero. -/
theorem sum_laplacian_eq_zero (f : Configuration V) :
    ∑ v, laplacian G f v = 0 := by
  rw [laplacian_eq_lapMatrix_mulVec]
  have hleft : Matrix.vecMul (fun _ : V => (1 : ℤ)) (G.lapMatrix ℤ) = 0 := by
    calc
      Matrix.vecMul (fun _ : V => (1 : ℤ)) (G.lapMatrix ℤ) =
          Matrix.vecMul (fun _ : V => (1 : ℤ)) (Matrix.transpose (G.lapMatrix ℤ)) := by
            rw [G.isSymm_lapMatrix ℤ |>.eq]
      _ = Matrix.mulVec (G.lapMatrix ℤ) (fun _ : V => (1 : ℤ)) :=
        Matrix.vecMul_transpose _ _
      _ = 0 := G.lapMatrix_mulVec_const_eq_zero
  have hdot : dotProduct (fun _ : V => (1 : ℤ))
      (Matrix.mulVec (G.lapMatrix ℤ) f) = 0 := by
    rw [Matrix.dotProduct_mulVec, hleft]
    simp [dotProduct]
  simpa [dotProduct] using hdot

/-- Total chip count. -/
def totalChips (σ : Configuration V) : ℤ := ∑ v, σ v

/-- One deterministic parallel step conserves the total number of chips. -/
theorem totalChips_step (σ : Configuration V) :
    totalChips (step G σ) = totalChips σ := by
  simp only [totalChips, step, update, Pi.sub_apply, Finset.sum_sub_distrib]
  rw [sum_laplacian_eq_zero]
  simp

end OneStep

section Orbit

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The actual deterministic threshold orbit. -/
noncomputable def actualOrbit (σ : Configuration V) : ℕ → Configuration V
  | 0 => σ
  | n + 1 => step G (actualOrbit σ n)

@[simp] theorem actualOrbit_zero (σ : Configuration V) : actualOrbit G σ 0 = σ := rfl

@[simp] theorem actualOrbit_succ (σ : Configuration V) (n : ℕ) :
    actualOrbit G σ (n + 1) = step G (actualOrbit G σ n) := rfl

/-- Restarting after `m` steps gives the same tail. -/
theorem actualOrbit_add (σ : Configuration V) (m n : ℕ) :
    actualOrbit G σ (m + n) = actualOrbit G (actualOrbit G σ m) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, actualOrbit_succ, ih, actualOrbit_succ]

/-- Nonnegativity is an invariant of the actual orbit. -/
theorem actualOrbit_nonnegative (σ : Configuration V)
    (hσ : ∀ v, 0 ≤ σ v) : ∀ n v, 0 ≤ actualOrbit G σ n v := by
  intro n
  induction n with
  | zero => simpa using hσ
  | succ n ih => simpa using step_nonnegative G (actualOrbit G σ n) ih

/-- Total chips are conserved along the whole actual orbit. -/
theorem totalChips_actualOrbit (σ : Configuration V) (n : ℕ) :
    totalChips (actualOrbit G σ n) = totalChips σ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [actualOrbit_succ, totalChips_step, ih]

/-- Configurations whose coordinates lie in the finite integer interval `[0,S]`. -/
def boundedConfigurations (S : ℤ) : Set (Configuration V) :=
  {τ | ∀ v, τ v ∈ Set.Icc (0 : ℤ) S}

theorem boundedConfigurations_finite (S : ℤ) :
    (boundedConfigurations (V := V) S).Finite := by
  simpa [boundedConfigurations] using
    (Set.Finite.pi' fun _ : V => Set.finite_Icc (0 : ℤ) S)

/-- Every coordinate of a legal orbit is at most its conserved total. -/
theorem actualOrbit_le_total (σ : Configuration V)
    (hσ : ∀ v, 0 ≤ σ v) (n : ℕ) (v : V) :
    actualOrbit G σ n v ≤ totalChips σ := by
  have hnonneg := actualOrbit_nonnegative G σ hσ n
  have hle : actualOrbit G σ n v ≤ ∑ w, actualOrbit G σ n w := by
    exact Finset.single_le_sum (fun w _ => hnonneg w) (Finset.mem_univ v)
  rw [← totalChips_actualOrbit G σ n]
  exact hle

theorem actualOrbit_mem_boundedConfigurations (σ : Configuration V)
    (hσ : ∀ v, 0 ≤ σ v) (n : ℕ) :
    actualOrbit G σ n ∈ boundedConfigurations (V := V) (totalChips σ) := by
  intro v
  exact ⟨actualOrbit_nonnegative G σ hσ n v, actualOrbit_le_total G σ hσ n v⟩

/-- Pigeonhole principle: a legal orbit repeats a state. -/
theorem exists_actualOrbit_repeat (σ : Configuration V)
    (hσ : ∀ v, 0 ≤ σ v) :
    ∃ i j : ℕ, i < j ∧ actualOrbit G σ i = actualOrbit G σ j := by
  classical
  let B := boundedConfigurations (V := V) (totalChips σ)
  have hB : B.Finite := boundedConfigurations_finite (V := V) (totalChips σ)
  letI : Finite B := hB.to_subtype
  let F : ℕ → B := fun n => ⟨actualOrbit G σ n,
    actualOrbit_mem_boundedConfigurations G σ hσ n⟩
  obtain ⟨i, j, hij, hF⟩ := Finite.exists_ne_map_eq_of_infinite F
  have horient : i < j ∨ j < i := Nat.lt_or_gt_of_ne hij
  cases horient with
  | inl hlt =>
      exact ⟨i, j, hlt, congrArg Subtype.val hF⟩
  | inr hgt =>
      exact ⟨j, i, hgt, (congrArg Subtype.val hF).symm⟩

/-- Equality of two orbit states propagates deterministically down both tails. -/
theorem actualOrbit_eq_of_repeat (σ : Configuration V) {i j : ℕ}
    (hij : actualOrbit G σ i = actualOrbit G σ j) (t : ℕ) :
    actualOrbit G σ (i + t) = actualOrbit G σ (j + t) := by
  rw [actualOrbit_add, actualOrbit_add, hij]

/-- Every legal orbit is eventually periodic with a positive period. -/
theorem actualOrbit_eventually_periodic (σ : Configuration V)
    (hσ : ∀ v, 0 ≤ σ v) :
    ∃ μ T : ℕ, 0 < T ∧
      ∀ t : ℕ, actualOrbit G σ (μ + T + t) = actualOrbit G σ (μ + t) := by
  obtain ⟨i, j, hij, heq⟩ := exists_actualOrbit_repeat G σ hσ
  refine ⟨i, j - i, Nat.sub_pos_of_lt hij, ?_⟩
  intro t
  have hindex : i + (j - i) + t = j + t := by omega
  rw [hindex]
  exact (actualOrbit_eq_of_repeat G σ heq t).symm

/-- The actual firing vector along the orbit. -/
noncomputable def actualFiring (σ : Configuration V) (n : ℕ) : Configuration V :=
  firingIndicator G (actualOrbit G σ n)

/-- Firing sequence on the tail beginning at time `μ`. -/
noncomputable def tailFiring (σ : Configuration V) (μ n : ℕ) : Configuration V :=
  firingIndicator G (actualOrbit G σ (μ + n))

/-- The recursive actual orbit agrees exactly with `evolve` and its supplied firing vectors. -/
theorem actualOrbit_eq_evolve (σ : Configuration V) :
    ∀ n, actualOrbit G σ n = evolve G σ (actualFiring G σ) n
  | 0 => rfl
  | n + 1 => by
      rw [actualOrbit_succ, evolve, ← actualOrbit_eq_evolve]
      rfl

/-- Every orbit tail is an `evolve` trajectory from its initial tail state. -/
theorem actualOrbit_tail_eq_evolve (σ : Configuration V) (μ : ℕ) :
    ∀ n, actualOrbit G σ (μ + n) =
      evolve G (actualOrbit G σ μ) (tailFiring G σ μ) n
  | 0 => rfl
  | n + 1 => by
      rw [Nat.add_succ, actualOrbit_succ, evolve, ← actualOrbit_tail_eq_evolve]
      rfl

/-- Actual firing counts are nonnegative. -/
theorem tailFiringPrefix_nonnegative (σ : Configuration V) (μ : ℕ) :
    ∀ n v, 0 ≤ firingPrefix (tailFiring G σ μ) n v
  | 0, v => by simp [firingPrefix]
  | n + 1, v => by
      rw [firingPrefix]
      change 0 ≤ firingPrefix (tailFiring G σ μ) n v + tailFiring G σ μ n v
      have hprefix := tailFiringPrefix_nonnegative σ μ n v
      have hbit : 0 ≤ tailFiring G σ μ n v := by
        exact firingIndicator_nonnegative G _ v
      omega

/-- In `n` rounds no vertex can fire more than `n` times. -/
theorem tailFiringPrefix_le_time (σ : Configuration V) (μ : ℕ) :
    ∀ n v, firingPrefix (tailFiring G σ μ) n v ≤ (n : ℤ)
  | 0, v => by simp [firingPrefix]
  | n + 1, v => by
      rw [firingPrefix]
      change firingPrefix (tailFiring G σ μ) n v + tailFiring G σ μ n v ≤
        ((n + 1 : ℕ) : ℤ)
      have hprefix := tailFiringPrefix_le_time σ μ n v
      have hbit : tailFiring G σ μ n v ≤ 1 := by
        exact firingIndicator_le_one G _ v
      push_cast
      omega

/--
A complete periodic-tail representation: after a transient, the actual states
and actual firing vectors are periodic and the tail is represented by `evolve`.
-/
theorem exists_periodic_orbit_representation (σ : Configuration V)
    (hσ : ∀ v, 0 ≤ σ v) :
    ∃ μ T : ℕ, 0 < T ∧
      (∀ n, actualOrbit G σ (μ + n) =
        evolve G (actualOrbit G σ μ) (tailFiring G σ μ) n) ∧
      evolve G (actualOrbit G σ μ) (tailFiring G σ μ) T = actualOrbit G σ μ ∧
      (∀ n, tailFiring G σ μ (T + n) = tailFiring G σ μ n) := by
  obtain ⟨μ, T, hT, hperiod⟩ := actualOrbit_eventually_periodic G σ hσ
  refine ⟨μ, T, hT, actualOrbit_tail_eq_evolve G σ μ, ?_, ?_⟩
  · rw [← actualOrbit_tail_eq_evolve]
    simpa using hperiod 0
  · intro n
    simp only [tailFiring]
    congr 1
    simpa [Nat.add_assoc] using hperiod n

end Orbit

section Harmonic

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Cast compatibility between the integer and real Laplacian matrices. -/
theorem lapMatrix_mulVec_intCast (f : Configuration V) :
    Matrix.mulVec (G.lapMatrix ℝ) (fun v => (f v : ℝ)) =
      fun v => ((Matrix.mulVec (G.lapMatrix ℤ) f) v : ℝ) := by
  funext v
  rw [G.lapMatrix_mulVec_apply, G.lapMatrix_mulVec_apply]
  push_cast
  rfl

/-- An integer harmonic function is constant along every reachable pair. -/
theorem laplacian_eq_zero_forces_eq_of_reachable (f : Configuration V)
    (hf : laplacian G f = 0) {v w : V} (hvw : G.Reachable v w) :
    f v = f w := by
  have hmatrixZ : Matrix.mulVec (G.lapMatrix ℤ) f = 0 := by
    rw [← laplacian_eq_lapMatrix_mulVec]
    exact hf
  have hmatrixR : Matrix.mulVec (G.lapMatrix ℝ) (fun x => (f x : ℝ)) = 0 := by
    rw [lapMatrix_mulVec_intCast, hmatrixZ]
    funext x
    simp
  have hreal := (G.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp hmatrixR) v w hvw
  exact_mod_cast hreal

/-- On a connected graph, an integer harmonic function is constant. -/
theorem laplacian_eq_zero_forces_constant (hG : G.Connected) (f : Configuration V)
    (hf : laplacian G f = 0) : ∃ q : ℤ, f = fun _ => q := by
  let v₀ : V := Classical.choice hG.nonempty
  refine ⟨f v₀, funext fun v => ?_⟩
  exact laplacian_eq_zero_forces_eq_of_reachable G f hf (hG v v₀)

/-- A returning supplied trajectory has one common firing count on a connected graph. -/
theorem common_firing_count_of_period (hG : G.Connected)
    (σ : Configuration V) (f : ℕ → Configuration V) (T : ℕ)
    (hperiod : evolve G σ f T = σ) :
    ∃ q : ℤ, firingPrefix f T = fun _ => q := by
  apply laplacian_eq_zero_forces_constant G hG
  exact laplacian_prefix_eq_zero_of_period G σ f T hperiod

/--
Common firing count for an actual deterministic periodic tail.  No activity
equality is assumed: it follows from connectedness and the Laplacian kernel.
-/
theorem common_actual_firing_count (hG : G.Connected)
    (σ : Configuration V) (μ T : ℕ)
    (hperiod : actualOrbit G σ (μ + T) = actualOrbit G σ μ) :
    ∃ q : ℤ, firingPrefix (tailFiring G σ μ) T = fun _ => q := by
  apply common_firing_count_of_period G hG (actualOrbit G σ μ) (tailFiring G σ μ) T
  rw [← actualOrbit_tail_eq_evolve]
  exact hperiod

/-- The common count is an integer between zero and the period length. -/
theorem common_actual_firing_count_bounds (hG : G.Connected)
    (σ : Configuration V) (μ T : ℕ)
    (hperiod : actualOrbit G σ (μ + T) = actualOrbit G σ μ) :
    ∃ q : ℤ, firingPrefix (tailFiring G σ μ) T = (fun _ => q) ∧
      0 ≤ q ∧ q ≤ (T : ℤ) := by
  obtain ⟨q, hq⟩ := common_actual_firing_count G hG σ μ T hperiod
  let v₀ : V := Classical.choice hG.nonempty
  have hqv : firingPrefix (tailFiring G σ μ) T v₀ = q := congrFun hq v₀
  refine ⟨q, hq, ?_, ?_⟩
  · rw [← hqv]
    exact tailFiringPrefix_nonnegative G σ μ T v₀
  · rw [← hqv]
    exact tailFiringPrefix_le_time G σ μ T v₀

/-- On an actual period, every vertex has the same rational activity `q/T`. -/
theorem common_actual_activity (hG : G.Connected)
    (σ : Configuration V) (μ T : ℕ) (_hT : 0 < T)
    (hperiod : actualOrbit G σ (μ + T) = actualOrbit G σ μ) :
    ∃ q : ℤ, firingPrefix (tailFiring G σ μ) T = (fun _ => q) ∧
      ∀ v, (firingPrefix (tailFiring G σ μ) T v : ℚ) / T = (q : ℚ) / T := by
  obtain ⟨q, hq⟩ := common_actual_firing_count G hG σ μ T hperiod
  refine ⟨q, hq, ?_⟩
  intro v
  rw [congrFun hq v]

end Harmonic

end MiddleStair
