module
public import RequestProject.TypedTriangle.TowerAnalyticPacking
public import RequestProject.TypedTriangle.ExplicitNativeWeightedPacking
public import RequestProject.TypedTriangle.ExplicitApproxNibble
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.TowerBounds
open Pseudorandom.Explicit

theorem nibbleCut_four_le {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1/100) :
    Pseudorandom.Nibble.nibbleCut 4 (3/80) (3/80) σ ≤
      (nibbleThreeBound : ℝ) := by
  have he := exp_le_three_pow (x := 4) (M := 4) (by norm_num)
  norm_num only [Nat.reducePow, Nat.cast_ofNat] at he
  have hep : 0 ≤ Real.exp 4 := (Real.exp_pos _).le
  have hl : Real.log 4 ≤ 4 := Real.log_le_self (by norm_num)
  have hl0 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hprod : Real.exp 4 * Real.log 4 ≤ 324 :=
    by
      have hh := mul_le_mul he hl hl0 (by norm_num : (0:ℝ) ≤ 81)
      nlinarith only [hh]
  have pc (x A : ℝ) (hx : 1/30 ≤ x) (hA : A ≤ 1000000) :
      powerCut x A ≤ (nibbleThreeBound : ℝ) := by
    apply powerCut_le_analyticCutBound (by norm_num : 1 ≤ (1000000 : ℕ))
      (by linarith only [hx]) hA
    apply (inv_le_iff_one_le_mul₀ (by linarith only [hx] : 0 < x)).2
    norm_num
    linarith only [hx]
  have lc (x A : ℝ) (hx : 1/30 ≤ x) (hA : A ≤ 1000000) :
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
  all_goals nlinarith only [hσ0, hσ1, he, hep, hl, hl0, hprod]

/-- EGJ is invoked at uniformity four by the actual cloned packing. -/
def egjFourInputBound : ℕ := 30000000 + 2 * nibbleThreeBound
def egjFourBound : ℕ := analyticCutBound egjFourInputBound

theorem egjCut_four_le : egjCut (1/4) 4 ≤ (egjFourBound : ℝ) := by
  let B : ℕ := egjFourInputBound
  have hBn : (0 : ℝ) ≤ nibbleThreeBound := Nat.cast_nonneg _
  have hB : (30000000 : ℝ) + 2 * (nibbleThreeBound : ℝ) = B := by
    simp only [B, egjFourInputBound, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have hB1 : 1 ≤ B := by
    have hh : (1 : ℝ) ≤ B := by linarith only [hB, hBn]
    exact_mod_cast hh
  have pc (x A : ℝ) (hx : 1/20480000 ≤ x) (hA : A ≤ (B : ℝ)) :
      powerCut x A ≤ (egjFourBound : ℝ) := by
    apply powerCut_le_analyticCutBound hB1 (by linarith only [hx]) hA
    apply (inv_le_iff_one_le_mul₀ (by linarith only [hx] : 0 < x)).2
    have hxm : 1 ≤ 20480000 * x := by linarith only [hx]
    have hxb : 20480000 ≤ (B : ℝ) := by linarith only [hB, hBn]
    exact hxm.trans (mul_le_mul_of_nonneg_right hxb (by linarith only [hx]))
  have lc (x A : ℝ) (hx : 1/20480000 ≤ x) (hA : A ≤ (B : ℝ)) :
      logCut x A ≤ (egjFourBound : ℝ) := by
    apply logCut_le_analyticCutBound hB1 (by linarith only [hx]) hA
    apply (inv_le_iff_one_le_mul₀ (by linarith only [hx] : 0 < x)).2
    have hxm : 1 ≤ 20480000 * x := by linarith only [hx]
    have hxb : 20480000 ≤ (B : ℝ) := by linarith only [hB, hBn]
    exact hxm.trans (mul_le_mul_of_nonneg_right hxb (by linarith only [hx]))
  have hb : (2 : ℝ) ≤ (egjFourBound : ℝ) := by
    have hh := pc 1 2 (by norm_num) (by linarith only [hB, hBn])
    have heq : powerCut (1:ℝ) 2 = 2 := by norm_num [powerCut]
    rw [heq] at hh
    exact hh
  have hn := nibbleCut_four_le (σ := 3/256000) (by norm_num) (by norm_num)
  have hl : Real.log 1024 ≤ 1024 := Real.log_le_self (by norm_num)
  have hp (x : ℝ) (hx : x ≤ 1) : (2 : ℝ)^x ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hx
  have hpρ := hp (3/80) (by norm_num)
  have hpσ := hp (3/256000) (by norm_num)
  unfold egjCut facts12Cut
  dsimp only
  refine max_le hb (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_))))))))))))
  all_goals first | apply lc | apply pc
  all_goals norm_num only [Nat.cast_ofNat, Nat.reduceSub]
  all_goals nlinarith only [hBn, hB, hn, hl, hpρ, hpσ]

def cloneInputBound (M : ℕ) : ℕ :=
  max 5120000 (max egjFourBound (4*M*M+2))

def cloneBound (M : ℕ) : ℕ := analyticCutBound (cloneInputBound M)

theorem cloneCut_le {M q : ℕ} {C c η D₀ : ℝ}
    (hM : 1 ≤ M) (hC0 : 0 ≤ C) (hc : 0 < c) (hη : 0 < η)
    (hC : C ≤ (M : ℝ)) (hcInv : c⁻¹ ≤ (M : ℝ))
    (hηInv : η⁻¹ ≤ (M : ℝ)) (hq : q ≤ M)
    (hD : D₀ ≤ (egjFourBound : ℝ)) :
    WeightedClone.Explicit.cloneCut C c η D₀ q ≤ (cloneBound M : ℝ) := by
  let B := cloneInputBound M
  have hBconst : (5120000 : ℝ) ≤ B := by
    exact_mod_cast (le_max_left 5120000 (max egjFourBound (4*M*M+2)))
  have hBD : (egjFourBound : ℝ) ≤ B := by
    exact_mod_cast ((le_max_left egjFourBound (4*M*M+2)).trans
      (le_max_right 5120000 (max egjFourBound (4*M*M+2))))
  have hBs : (4 : ℝ) * M * M + 2 ≤ B := by
    exact_mod_cast ((le_max_right egjFourBound (4*M*M+2)).trans
      (le_max_right 5120000 (max egjFourBound (4*M*M+2))))
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hq' : (q : ℝ) ≤ M := by exact_mod_cast hq
  have hB1 : 1 ≤ B := by exact_mod_cast (by linarith only [hBconst] : (1:ℝ) ≤ B)
  have pc (x A : ℝ) (hx : 1/5120000 ≤ x) (hA : A ≤ (B : ℝ)) :
      powerCut x A ≤ (cloneBound M : ℝ) := by
    apply powerCut_le_analyticCutBound hB1 (by linarith only [hx]) hA
    apply (inv_le_iff_one_le_mul₀ (by linarith only [hx] : 0 < x)).2
    have hh : 1 ≤ 5120000*x := by linarith only [hx]
    exact hh.trans (mul_le_mul_of_nonneg_right hBconst (by linarith only [hx]))
  have lc (x A : ℝ) (hx : 1/5120000 ≤ x) (hA : A ≤ (B : ℝ)) :
      logCut x A ≤ (cloneBound M : ℝ) := by
    apply logCut_le_analyticCutBound hB1 (by linarith only [hx]) hA
    apply (inv_le_iff_one_le_mul₀ (by linarith only [hx] : 0 < x)).2
    have hh : 1 ≤ 5120000*x := by linarith only [hx]
    exact hh.trans (mul_le_mul_of_nonneg_right hBconst (by linarith only [hx]))
  have hBB : (B : ℝ) ≤ (cloneBound M : ℝ) := by
    have hh := pc 1 B (by norm_num) le_rfl
    have hb0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    have hb1 : (1 : ℝ) ≤ B := by exact_mod_cast hB1
    simpa only [powerCut, inv_one, Real.rpow_one,
      max_eq_left hb0, max_eq_right hb1] using hh
  have hOne : (1 : ℝ) ≤ (cloneBound M : ℝ) := by
    exact (by linarith only [hBconst] : (1:ℝ) ≤ B).trans hBB
  have hCB : C ≤ (B : ℝ) := by nlinarith only [hC, hm, hBs]
  have hLast : 4*C/η ≤ (B : ℝ) := by
    have hh := mul_le_mul hC hηInv (inv_nonneg.mpr hη.le) (Nat.cast_nonneg M)
    rw [div_eq_mul_inv]
    nlinarith only [hh, hBs]
  unfold WeightedClone.Explicit.cloneCut
  refine max_le hOne (max_le (hCB.trans hBB) (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (hLast.trans hBB)))))))))
  all_goals first | apply lc | apply pc
  all_goals norm_num only [Nat.cast_ofNat]
  all_goals try simp only [div_eq_mul_inv, one_mul]
  all_goals nlinarith only [hC, hcInv, hηInv, hq', hD, hBD, hBconst, hBs, hm]

theorem nativePackingCut_le {M q : ℕ} {C c η : ℝ}
    (hM : 1 ≤ M) (hC0 : 0 ≤ C) (hc : 0 < c) (hη : 0 < η)
    (hC : C ≤ (M : ℝ)) (hcInv : c⁻¹ ≤ (M : ℝ))
    (hηInv : η⁻¹ ≤ (M : ℝ)) (hq : q ≤ M) :
    NativeNibble.Explicit.nativePackingCut C c η q ≤ cloneBound M := by
  have hh := cloneCut_le hM hC0 hc hη hC hcInv hηInv hq egjCut_four_le
  have hOne : 1 ≤ cloneBound M := by
    have h1 : (1 : ℝ) ≤ WeightedClone.Explicit.cloneCut C c η (egjCut (1/4) 4) q :=
      le_max_left _ _
    exact_mod_cast h1.trans hh
  exact max_le hOne (Nat.ceil_le.mpr hh)

def approxPackingBound (M : ℕ) : ℕ := cloneBound (16*M)

theorem approxPackingCut_le {M : ℕ} {b η : ℝ}
    (hM : 1 ≤ M) (hb : b ≤ (M : ℝ)) (hη : 0 < η)
    (hηInv : η⁻¹ ≤ (M : ℝ)) :
    PartitionedTriangleAbsorption.Nibble.Explicit.approxPackingCut b η ≤ approxPackingBound M := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hC : max 1 b ≤ ((16*M : ℕ) : ℝ) := by push_cast; exact max_le (by linarith only [hm]) (by linarith only [hb, hm])
  have hcInv : (η/16)⁻¹ ≤ ((16*M : ℕ) : ℝ) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    push_cast
    nlinarith only [hηInv]
  have heInv : (η/8)⁻¹ ≤ ((16*M : ℕ) : ℝ) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    push_cast
    nlinarith only [hηInv, hm]
  have hh := cloneCut_le (M := 16*M) (q := 1) (by omega)
    (by positivity : 0 ≤ max 1 b) (by positivity : 0 < η/16)
    (by positivity : 0 < η/8) hC hcInv heInv (by omega) egjCut_four_le
  have hOne : 1 ≤ cloneBound (16*M) := by
    have h1 : (1 : ℝ) ≤ WeightedClone.Explicit.cloneCut (max 1 b) (η/16) (η/8)
        (egjCut (1/4) 4) 1 := le_max_left _ _
    exact_mod_cast h1.trans hh
  exact max_le hOne (Nat.ceil_le.mpr hh)

#print axioms nibbleCut_four_le
#print axioms egjCut_four_le
#print axioms cloneCut_le
#print axioms nativePackingCut_le
#print axioms approxPackingCut_le
end TypedTriangle.TowerBounds
