module
public import RequestProject.TypedTriangle.TowerAnalyticCuts
public import RequestProject.Pseudorandom.ExplicitTheorem12
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.TowerBounds
open Pseudorandom.Explicit

/-- A uniform integer bound for the nibble used by EGJ at uniformity three. -/
def nibbleThreeBound : ℕ := analyticCutBound 1000000

theorem nibbleCut_three_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Pseudorandom.Nibble.nibbleCut 3 (1/20) (1/20) (δ/9000) ≤
      (nibbleThreeBound : ℝ) := by
  have he := exp_le_three_pow (x := 3) (M := 3) (by norm_num)
  norm_num only [Nat.reducePow, Nat.cast_ofNat] at he
  have hep : 0 ≤ Real.exp 3 := (Real.exp_pos _).le
  have hl : Real.log 3 ≤ 3 := Real.log_le_self (by norm_num)
  have hl0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hprod : Real.exp 3 * Real.log 3 ≤ 81 :=
    by
      have hh := mul_le_mul he hl hl0 (by norm_num : (0:ℝ) ≤ 27)
      nlinarith only [hh]
  have pc (x A : ℝ) (hx : 1/20 ≤ x) (hA : A ≤ 1000000) :
      powerCut x A ≤ (nibbleThreeBound : ℝ) := by
    apply powerCut_le_analyticCutBound (by norm_num : 1 ≤ (1000000 : ℕ))
      (by linarith only [hx]) hA
    apply (inv_le_iff_one_le_mul₀ (by linarith only [hx] : 0 < x)).2
    norm_num
    linarith only [hx]
  have lc (x A : ℝ) (hx : 1/20 ≤ x) (hA : A ≤ 1000000) :
      logCut x A ≤ (nibbleThreeBound : ℝ) := by
    apply logCut_le_analyticCutBound (by norm_num : 1 ≤ (1000000 : ℕ))
      (by linarith only [hx]) hA
    apply (inv_le_iff_one_le_mul₀ (by linarith only [hx] : 0 < x)).2
    norm_num
    linarith only [hx]
  have hb : (2 : ℝ) ≤ (nibbleThreeBound : ℝ) := by
    have hh := pc 1 2 (by norm_num) (by norm_num)
    have heq : powerCut (1:ℝ) 2 = 2 := by norm_num [powerCut]
    rw [heq] at hh
    exact hh
  unfold Pseudorandom.Nibble.nibbleCut
  dsimp only
  refine max_le hb (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_)))))))
  all_goals first | apply lc | apply pc
  all_goals norm_num only [Nat.cast_ofNat, Nat.reduceSub]
  all_goals nlinarith only [hδ0, hδ1, he, hep, hl, hl0, hprod]

/-- All variable exponent gaps in `facts12Cut` are paid by this integer. -/
def egjThreeInputBound (M : ℕ) : ℕ :=
  max (1000000 + 2 * nibbleThreeBound) (405000 * (M + 1)^2)

def egjThreeBound (M : ℕ) : ℕ := analyticCutBound (egjThreeInputBound M)

theorem egjCut_three_le {δ : ℝ} {M : ℕ}
    (hM : 1 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hInv : δ⁻¹ ≤ (M : ℝ)) :
    egjCut δ 3 ≤ (egjThreeBound M : ℝ) := by
  let ε : ℝ := δ / 450
  let B : ℕ := egjThreeInputBound M
  have he0 : 0 < ε := by dsimp only [ε]; positivity
  have he1 : ε ≤ 1/450 := by dsimp only [ε]; linarith only [hδ1]
  have heδ : δ = 450 * ε := by dsimp only [ε]; ring
  have he2 : ε^2 ≤ ε/450 := by nlinarith only [he0, he1]
  have hei : ε⁻¹ ≤ 450 * (M : ℝ) := by
    dsimp only [ε]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    nlinarith only [hInv]
  have hesq : (ε⁻¹)^2 ≤ (450 * (M : ℝ))^2 :=
    (sq_le_sq₀ (inv_nonneg.mpr he0.le) (by positivity)).2 hei
  have hBconst : (1000000 : ℝ) + 2 * (nibbleThreeBound : ℝ) ≤ B := by
    exact_mod_cast (le_max_left (1000000 + 2*nibbleThreeBound)
      (405000*(M+1)^2))
  have hBscale : 405000 * ((M : ℝ)+1)^2 ≤ B := by
    exact_mod_cast (le_max_right (1000000 + 2*nibbleThreeBound)
      (405000*(M+1)^2))
  have hBn : (0 : ℝ) ≤ nibbleThreeBound := Nat.cast_nonneg _
  have hB1 : 1 ≤ B := by
    have hh : (1 : ℝ) ≤ B := by linarith only [hBconst, hBn]
    exact_mod_cast hh
  have gap_inv (x : ℝ) (hx : ε^2/2 ≤ x) : x⁻¹ ≤ (B : ℝ) := by
    have hy : 0 < ε^2/2 := by positivity
    have hx0 : 0 < x := hy.trans_le hx
    calc
      x⁻¹ ≤ (ε^2/2)⁻¹ := (inv_le_inv₀ hx0 hy).2 hx
      _ = 2 * (ε⁻¹)^2 := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, inv_pow]
      _ ≤ 405000 * (M : ℝ)^2 := by nlinarith only [hesq]
      _ ≤ (B : ℝ) := by
        nlinarith only [hBscale, (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have pc (x A : ℝ) (hx : ε^2/2 ≤ x) (hA : A ≤ (B : ℝ)) :
      powerCut x A ≤ (egjThreeBound M : ℝ) :=
    powerCut_le_analyticCutBound hB1 (lt_of_lt_of_le (by positivity) hx) hA (gap_inv x hx)
  have lc (x A : ℝ) (hx : ε^2/2 ≤ x) (hA : A ≤ (B : ℝ)) :
      logCut x A ≤ (egjThreeBound M : ℝ) :=
    logCut_le_analyticCutBound hB1 (lt_of_lt_of_le (by positivity) hx) hA (gap_inv x hx)
  have htwo : (2 : ℝ) ≤ (egjThreeBound M : ℝ) := by
    have hh := pc 1 2 (by nlinarith only [he0, he1, he2])
      (by linarith only [hBconst, hBn])
    have heq : powerCut (1:ℝ) 2 = 2 := by norm_num [powerCut]
    rw [heq] at hh
    exact hh
  have hn : Pseudorandom.Nibble.nibbleCut 3 (1/20) (1/20) (ε/20) ≤
      (nibbleThreeBound : ℝ) := by
    convert nibbleCut_three_le hδ0.le hδ1 using 1 <;> dsimp only [ε] <;> ring
  have hl : Real.log 576 ≤ 576 := Real.log_le_self (by norm_num)
  have hp (x : ℝ) (hx : x ≤ 1) : (2 : ℝ)^x ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hx
  have hpρ := hp (1/20) (by norm_num)
  have hpσ := hp (ε/20) (by linarith only [he1])
  have hegj : egjCut δ 3 = facts12Cut 3 δ ε (30*ε) (63*ε)
      (1/20) (1/20) (ε/20)
      (Pseudorandom.Nibble.nibbleCut 3 (1/20) (1/20) (ε/20)) := by
    unfold egjCut
    congr 2 <;> dsimp only [ε] <;> norm_num <;> ring
  rw [hegj]
  unfold facts12Cut
  refine max_le htwo (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_))))))))))))
  all_goals first | apply lc | apply pc
  all_goals norm_num only [Nat.cast_ofNat, Nat.reduceSub]
  all_goals nlinarith only [he0, he1, he2, heδ, hBconst, hBn, hn, hl, hpρ, hpσ]

#print axioms nibbleCut_three_le
#print axioms egjCut_three_le
end TypedTriangle.TowerBounds
