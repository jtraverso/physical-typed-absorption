/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Mathlib
@[expose] public section
noncomputable section
namespace TypedTriangle.RawReference

/-- Formula-only threshold; no asymptotic or existential constant occurs. -/
def polynomialSqrtCut (d : ℕ) (c : ℝ) : ℝ :=
  max 1 (4 * ((2*d+2).factorial : ℝ) / c^(2*d+2))

theorem polynomial_sqrt_budget_at_explicit_cut (d : ℕ) (c : ℝ) (hc : 0 < c)
    (x : ℝ) (hx : polynomialSqrtCut d c ≤ x) :
    (x^d + 2)*Real.exp (-c*Real.sqrt x) < 1 := by
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 ≤ x := by linarith
  have hxp : 0 < x^d := pow_pos (by linarith) _
  have hxd : 1 ≤ x^d := one_le_pow₀ hx1
  have hcp : 0 < c^(2*d+2) := pow_pos hc _
  have hfac : (0:ℝ) < (2*d+2).factorial := by positivity
  have hCut : 4 * ((2*d+2).factorial : ℝ) ≤ c^(2*d+2) * x := by
    have hh : 4 * ((2*d+2).factorial : ℝ) / c^(2*d+2) ≤ x :=
      (le_max_right _ _).trans hx
    simpa only [mul_comm] using (div_le_iff₀ hcp).mp hh
  have hsqrt : (Real.sqrt x)^(2*d+2) = x^d*x := by
    rw [show 2*d+2=2*(d+1) by omega, pow_mul, Real.sq_sqrt hx0, pow_succ]
  have hTerm : 4*x^d ≤ (c*Real.sqrt x)^(2*d+2) / ((2*d+2).factorial : ℝ) := by
    apply (le_div_iff₀ hfac).mpr
    rw [mul_pow,hsqrt]
    nlinarith [mul_le_mul_of_nonneg_right hCut hxp.le]
  have hExp := Real.pow_div_factorial_le_exp (c*Real.sqrt x)
    (mul_nonneg hc.le (Real.sqrt_nonneg x)) (2*d+2)
  have hStrict : x^d+2 < Real.exp (c*Real.sqrt x) := by
    have hFour := hTerm.trans hExp
    linarith
  rw [neg_mul, Real.exp_neg]
  exact (mul_inv_lt_iff₀ (Real.exp_pos _)).mpr (by simpa using hStrict)

theorem polynomial_sqrt_budget_explicit (d : ℕ) (c : ℝ) (hc : 0 < c) :
    ∀ x : ℝ, polynomialSqrtCut d c ≤ x →
      (x^d+2)*Real.exp (-c*Real.sqrt x) < 1 :=
  fun x hx => polynomial_sqrt_budget_at_explicit_cut d c hc x hx

theorem six_tests_sqrt_budget (c : ℝ) (hc : 0 < c) (n : ℕ)
    (hn : ⌈max 1 (4 * (Nat.factorial 14 : ℝ) / c^14)⌉₊ ≤ n) :
    ((n:ℝ)^6+2)*Real.exp (-c*Real.sqrt n) < 1 := by
  apply polynomial_sqrt_budget_at_explicit_cut 6 c hc n
  change max 1 (4 * (Nat.factorial 14 : ℝ) / c^14) ≤ (n : ℝ)
  exact (Nat.le_ceil _).trans (by exact_mod_cast hn)

#print axioms polynomial_sqrt_budget_at_explicit_cut
#print axioms polynomial_sqrt_budget_explicit
#print axioms six_tests_sqrt_budget
end TypedTriangle.RawReference
