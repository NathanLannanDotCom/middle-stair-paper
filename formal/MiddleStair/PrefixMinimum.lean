import Mathlib.Tactic

/-!
# Scaled prefix-minimum bookkeeping

The paper writes `h(t) = u(t) - (q/T)t`.  We instead multiply throughout by
the positive period `T`.  This keeps the formal statement entirely integral:
`H(t) = T*u(t) - q*t`.  The main theorem below is the delicate, different-time
edge-charge rounding step in the low-activity density lemma.
-/

namespace MiddleStair

/-- Denominator-cleared prefix height. -/
def scaledHeight (T q u t : ℤ) : ℤ := T * u - q * t

/-- A common period increment makes scaled height periodic. -/
theorem scaledHeight_period_shift (T q u t : ℤ) :
    scaledHeight T q (u + q) (t + T) = scaledHeight T q u t := by
  simp only [scaledHeight]
  ring

/--
A minimum compared with the preceding time selects a waiting round.  The bit
`f` is the prefix increment from `τ` to `τ+1`.
-/
theorem selected_minimum_forces_wait
    (T q u τ f : ℤ)
    (hq : q < T)
    (hbit : f = 0 ∨ f = 1)
    (hmin : scaledHeight T q (u + f) (τ + 1) ≤ scaledHeight T q u τ) :
    f = 0 := by
  rcases hbit with rfl | rfl
  · rfl
  · simp only [scaledHeight] at hmin
    nlinarith

/-- The integer edge charge assembled from the two endpoint-selected times. -/
def edgeCharge (uvAtV uwAtV uwAtW uvAtW : ℤ) : ℤ :=
  uvAtV - uwAtV + uwAtW - uvAtW

/--
Adding the two cross-time minimum inequalities gives the exact scaled bound
`T*K ≤ 2*q`.  The four prefix values are ordered as their names indicate:
`uvAtV = u_v(τ_v)`, `uwAtV = u_w(τ_v)`, and so on.
-/
theorem edgeCharge_scaled_bound
    (T q τv τw uvAtV uwAtV uwAtW uvAtW : ℤ)
    (hcrossV :
      scaledHeight T q uvAtV (τv + 1) ≤ scaledHeight T q uvAtW τw)
    (hcrossW :
      scaledHeight T q uwAtW (τw + 1) ≤ scaledHeight T q uwAtV τv) :
    T * edgeCharge uvAtV uwAtV uwAtW uvAtW ≤ 2 * q := by
  simp only [scaledHeight, edgeCharge] at *
  nlinarith

/--
The strict low-activity hypothesis `2*q < T`, positivity of the period, and
integrality round the edge charge down to a nonpositive integer.
-/
theorem selected_edge_charge_nonpositive
    (T q τv τw uvAtV uwAtV uwAtW uvAtW : ℤ)
    (hT : 0 < T)
    (hhalf : 2 * q < T)
    (hcrossV :
      scaledHeight T q uvAtV (τv + 1) ≤ scaledHeight T q uvAtW τw)
    (hcrossW :
      scaledHeight T q uwAtW (τw + 1) ≤ scaledHeight T q uwAtV τv) :
    edgeCharge uvAtV uwAtV uwAtW uvAtW ≤ 0 := by
  have hscaled := edgeCharge_scaled_bound T q τv τw uvAtV uwAtV uwAtW uvAtW
    hcrossV hcrossW
  by_contra hnot
  have hcharge : 1 ≤ edgeCharge uvAtV uwAtV uwAtW uvAtW := by omega
  nlinarith

/-- A reusable denominator-free form of integer rounding below one. -/
theorem integer_rounding_below_one (T q K : ℤ)
    (hT : 0 < T) (hhalf : 2 * q < T) (hscaled : T * K ≤ 2 * q) :
    K ≤ 0 := by
  by_contra hnot
  have hK : 1 ≤ K := by omega
  nlinarith

end MiddleStair
