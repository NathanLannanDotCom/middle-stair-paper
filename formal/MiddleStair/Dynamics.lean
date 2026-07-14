import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic

/-!
# Parallel chip-firing dynamics

This file formalizes the algebraic core used by the middle-stair argument:
the graph Laplacian, synchronous updates, prefix telescoping, complementary
firing, and the affine periodic complement.

Configurations are integer-valued here.  Nonnegativity is a separate orbit
invariant in the paper; using `ℤ` makes every subtraction in the Laplacian
literal and prevents hidden truncated subtraction.
-/

namespace MiddleStair

open scoped BigOperators

abbrev Configuration (V : Type*) := V → ℤ

section Laplacian

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The combinatorial graph Laplacian, with the sign convention `D - A`. -/
def laplacian (f : Configuration V) : Configuration V := fun v =>
  ∑ w ∈ G.neighborFinset v, (f v - f w)

@[simp] theorem laplacian_zero : laplacian G (0 : Configuration V) = 0 := by
  ext v
  simp [laplacian]

@[simp] theorem laplacian_const (c : ℤ) :
    laplacian G (fun _ => c) = 0 := by
  ext v
  simp [laplacian]

theorem laplacian_add (f g : Configuration V) :
    laplacian G (f + g) = laplacian G f + laplacian G g := by
  ext v
  simp only [laplacian, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem laplacian_neg (f : Configuration V) :
    laplacian G (-f) = -laplacian G f := by
  ext v
  simp only [laplacian, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem laplacian_sub (f g : Configuration V) :
    laplacian G (f - g) = laplacian G f - laplacian G g := by
  rw [sub_eq_add_neg, laplacian_add, laplacian_neg, sub_eq_add_neg]

/-- Complementary binary firing has the opposite Laplacian. -/
theorem laplacian_one_sub (f : Configuration V) :
    laplacian G (fun v => 1 - f v) = -laplacian G f := by
  have hfun : (fun v => 1 - f v) = (fun _ => (1 : ℤ)) - f := by
    rfl
  rw [hfun, laplacian_sub, laplacian_const]
  simp

/-- One synchronous parallel chip-firing update for a supplied firing vector. -/
def update (σ f : Configuration V) : Configuration V :=
  σ - laplacian G f

@[simp] theorem update_zero (σ : Configuration V) : update G σ 0 = σ := by
  simp [update]

theorem update_add (σ f g : Configuration V) :
    update G σ (f + g) = update G (update G σ f) g := by
  ext v
  simp only [update, Pi.sub_apply, laplacian_add, Pi.add_apply]
  ring

/-- If the two firing vectors add to one, two updates return to the state. -/
theorem update_two_rounds_of_sum_one (σ f g : Configuration V)
    (hfg : f + g = fun _ => (1 : ℤ)) :
    update G (update G σ f) g = σ := by
  rw [← update_add, hfg]
  exact update_zero G σ

/-- The special case in which the second firing vector is the pointwise complement. -/
theorem update_then_complementary_firing (σ f : Configuration V) :
    update G (update G σ f) (fun v => 1 - f v) = σ := by
  apply update_two_rounds_of_sum_one
  funext v
  simp

end Laplacian

section Prefixes

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Prefix sum of a time-indexed firing sequence. -/
def firingPrefix (f : ℕ → Configuration V) : ℕ → Configuration V
  | 0 => 0
  | n + 1 => firingPrefix f n + f n

/-- State obtained after applying the first `n` synchronous firing vectors. -/
def evolve (σ : Configuration V) (f : ℕ → Configuration V) : ℕ → Configuration V
  | 0 => σ
  | n + 1 => update G (evolve σ f n) (f n)

/-- Telescoping identity `σₙ = σ₀ - L u(n)`. -/
theorem evolve_eq_update_prefix (σ : Configuration V) (f : ℕ → Configuration V) :
    ∀ n, evolve G σ f n = update G σ (firingPrefix f n)
  | 0 => by simp [evolve, firingPrefix]
  | n + 1 => by
      rw [evolve, evolve_eq_update_prefix, firingPrefix, ← update_add]

/-- A repeated state forces the accumulated firing prefix to be harmonic. -/
theorem laplacian_prefix_eq_zero_of_period
    (σ : Configuration V) (f : ℕ → Configuration V) (T : ℕ)
    (hperiod : evolve G σ f T = σ) :
    laplacian G (firingPrefix f T) = 0 := by
  rw [evolve_eq_update_prefix] at hperiod
  ext v
  have hv := congrFun hperiod v
  simp only [update, Pi.sub_apply] at hv
  exact sub_eq_self.mp hv

end Prefixes

section Complement

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The affine chip complement used on a nonfixed periodic orbit. -/
def complement (σ : Configuration V) : Configuration V := fun v =>
  2 * (G.degree v : ℤ) - 1 - σ v

@[simp] theorem complement_involutive (σ : Configuration V) :
    complement G (complement G σ) = σ := by
  ext v
  simp [complement]

theorem complement_nonnegative_at (σ : Configuration V) (v : V)
    (hupper : σ v ≤ 2 * (G.degree v : ℤ) - 1) :
    0 ≤ complement G σ v := by
  simp only [complement]
  omega

theorem complement_upper_at (σ : Configuration V) (v : V)
    (hlower : 0 ≤ σ v) :
    complement G σ v ≤ 2 * (G.degree v : ℤ) - 1 := by
  simp only [complement]
  omega

/-- Algebraic conjugacy for any supplied firing vector. -/
theorem complement_update (σ f : Configuration V) :
    complement G (update G σ f) =
      update G (complement G σ) (fun v => 1 - f v) := by
  ext v
  simp only [complement, update, Pi.sub_apply, laplacian_one_sub, Pi.neg_apply]
  ring

/-- A vertex fires when its chip count reaches its degree. -/
def Fires (σ : Configuration V) (v : V) : Prop :=
  (G.degree v : ℤ) ≤ σ v

theorem fires_complement_iff (σ : Configuration V) (v : V) :
    Fires G (complement G σ) v ↔ ¬ Fires G σ v := by
  simp only [Fires, complement]
  omega

/-- Integer-valued indicator of the threshold firing predicate. -/
noncomputable def firingIndicator (σ : Configuration V) : Configuration V := by
  classical
  exact fun v => if Fires G σ v then 1 else 0

theorem firingIndicator_eq_zero_or_one (σ : Configuration V) (v : V) :
    firingIndicator G σ v = 0 ∨ firingIndicator G σ v = 1 := by
  classical
  simp only [firingIndicator]
  split <;> simp

theorem firingIndicator_complement (σ : Configuration V) :
    firingIndicator G (complement G σ) = fun v => 1 - firingIndicator G σ v := by
  classical
  funext v
  simp only [firingIndicator, fires_complement_iff]
  by_cases h : Fires G σ v <;> simp [h]

/-- The actual deterministic parallel chip-firing step. -/
noncomputable def step (σ : Configuration V) : Configuration V :=
  update G σ (firingIndicator G σ)

/-- On integer configurations, the affine complement conjugates actual steps. -/
theorem complement_step (σ : Configuration V) :
    complement G (step G σ) = step G (complement G σ) := by
  classical
  rw [step, step, complement_update, firingIndicator_complement]

end Complement

end MiddleStair
