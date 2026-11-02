/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.Pseudorandom.ExplicitAsymptotics
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.TowerBounds

/-- Integer arithmetic only; the exponent is a natural number. -/
def analyticCutBound (M : ℕ) : ℕ := (2 * M * M) ^ (2 * M)

theorem powerCut_le_nat_pow {c A : ℝ} {B E : ℕ}
    (hc : 0 < c) (hB : 1 ≤ B) (hA : A ≤ (B : ℝ))
    (hE : c⁻¹ ≤ (E : ℝ)) :
    Pseudorandom.Explicit.powerCut c A ≤ ((B ^ E : ℕ) : ℝ) := by
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hbase : max A 0 ≤ (B : ℝ) := max_le hA (by linarith only [hB'])
  have hr := Real.rpow_le_rpow (le_max_right A 0) hbase (inv_pos.mpr hc).le
  have he := Real.rpow_le_rpow_of_exponent_le hB' hE
  rw [Real.rpow_natCast] at he
  rw [Pseudorandom.Explicit.powerCut, Nat.cast_pow]
  exact max_le (one_le_pow₀ hB') (hr.trans he)

theorem powerCut_le_analyticCutBound {c A : ℝ} {M : ℕ}
    (hM : 1 ≤ M) (hc : 0 < c) (hA : A ≤ (M : ℝ))
    (hInv : c⁻¹ ≤ (M : ℝ)) :
    Pseudorandom.Explicit.powerCut c A ≤ (analyticCutBound M : ℝ) := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hb : (1 : ℕ) ≤ 2 * M * M := by nlinarith only [hM]
  apply powerCut_le_nat_pow hc hb
  · push_cast
    nlinarith only [hA, hm, sq_nonneg (M : ℝ)]
  · push_cast
    linarith only [hInv, hm]

theorem logCut_le_analyticCutBound {c A : ℝ} {M : ℕ}
    (hM : 1 ≤ M) (hc : 0 < c) (hA : A ≤ (M : ℝ))
    (hInv : c⁻¹ ≤ (M : ℝ)) :
    Pseudorandom.Explicit.logCut c A ≤ (analyticCutBound M : ℝ) := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hm0 : (0 : ℝ) ≤ M := by positivity
  have hb : (1 : ℕ) ≤ 2 * M * M := by nlinarith only [hM]
  have hmax : max A 0 ≤ (M : ℝ) := max_le hA hm0
  unfold Pseudorandom.Explicit.logCut analyticCutBound
  apply powerCut_le_nat_pow (by linarith only [hc]) hb
  · push_cast
    rw [div_eq_mul_inv]
    calc
      2 * max A 0 * c⁻¹ ≤ 2 * (M : ℝ) * M := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hmax (by norm_num)) hInv
          (inv_nonneg.mpr hc.le) (by positivity)
      _ = _ := by ring
  · push_cast
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    nlinarith only [hInv]

/-- An elementary exponential majorant with a natural exponent. -/
theorem exp_le_three_pow {x : ℝ} {M : ℕ} (hx : x ≤ (M : ℝ)) :
    Real.exp x ≤ ((3 ^ M : ℕ) : ℝ) := by
  calc
    Real.exp x ≤ Real.exp (M : ℝ) := Real.exp_le_exp.mpr hx
    _ = Real.exp 1 ^ M := by rw [← Real.exp_nat_mul]; simp only [mul_one]
    _ ≤ (3 : ℝ) ^ M := pow_le_pow_left₀ (Real.exp_nonneg _) Real.exp_one_lt_three.le M
    _ = _ := by norm_cast

#print axioms powerCut_le_nat_pow
#print axioms powerCut_le_analyticCutBound
#print axioms logCut_le_analyticCutBound
#print axioms exp_le_three_pow
end TypedTriangle.TowerBounds
