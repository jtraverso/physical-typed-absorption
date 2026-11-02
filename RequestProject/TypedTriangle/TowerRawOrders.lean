module
public import RequestProject.TypedTriangle.TowerRawSample
public import RequestProject.TypedTriangle.TowerGeometryPreparation
public import RequestProject.TypedTriangle.ExplicitOuterInnerRawPreparedVortex
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.TowerBounds
open Vortex.ExplicitRaw

def rawGeometryShapeBound (M K A : ℕ) : ℕ :=
  max ((A*(M+1))^4) (max (32^4) (max (4*K) (((2*(M+1))*compressionPowerMajorant M)*K)))
def rawRequiredGeometryBound (M : ℕ) : ℕ := rawGeometryShapeBound M ((M*M^M)*4) 8
def outerRawRequiredGeometryBound (M : ℕ) : ℕ := rawGeometryShapeBound M (M*M^M) 4
def rawMinimumOrderBound (M : ℕ) : ℕ :=
  max (max (preparationOrderMajorant (M*4)) M) (max 1 (rawRequiredGeometryBound M+1))
def outerRawMinimumOrderBound (M : ℕ) : ℕ :=
  max (max (preparationOrderMajorant (M*4)) M) (max 1 (outerRawRequiredGeometryBound M+1))
def rawRootOrderBound (M : ℕ) : ℕ := 2*rawMinimumOrderBound M
def rawGlobalInputBound (M : ℕ) : ℕ := max M (max (M*2) (2*M))
def globalRawStepOrderBound (M : ℕ) : ℕ :=
  max (max (rawNativeSampleOrderBound (rawGlobalInputBound M)) ((8*(M+1))^4))
    (max (2*M*M) 1)
def rawTerminalInputBound (M : ℕ) : ℕ := max M (2*rawMinimumOrderBound M)
def rawTerminalOrderBound (M : ℕ) : ℕ :=
  max (globalRawStepOrderBound (rawTerminalInputBound M)) (rawMinimumOrderBound M)
def outerRawAutoInputBound (M : ℕ) : ℕ := max M (max (4*M) (2*M))
def outerRawRootOrderBound (M T : ℕ) : ℕ :=
  let B := outerRawMinimumOrderBound M
  2*max (rawAutomaticOrderBound (outerRawAutoInputBound M) T) (max B (2*B*M))+2
def nativeOuterInputBound (M : ℕ) : ℕ := max M (8*M)
def nativeOuterRootOrderBound (M : ℕ) : ℕ :=
  max (outerRawRootOrderBound M (rawOuterTestRateBound (nativeOuterInputBound M)))
    (nativeRouteOrderMajorant (nativeOuterInputBound M))
def outerInnerInputBound (M : ℕ) : ℕ := max M (max 16 (rawRootOrderBound M))
def outerInnerRootOrderBound (M : ℕ) : ℕ := nativeOuterRootOrderBound (outerInnerInputBound M)

private theorem rawHeight_magnitude {M h : ℕ} (hh : h ≤ M) :
    Magnitude (M+1) ((h : ℝ)+1) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (Magnitude.natCast (n := h+1) (by omega) (Nat.add_le_add_right hh 1))

private theorem rawGeometryShape_magnitude {M K A h : ℕ} {κ : ℝ}
    (hκ : Magnitude K κ) (hA : 1 ≤ A) (hh : h ≤ M) :
    Magnitude (rawGeometryShapeBound M K A)
      (max (((A : ℝ)*((h : ℝ)+1))^4)
        (max ((32 : ℝ)^4) (max (4/κ) (2*(1+(h : ℝ))*2^Nat.choose h 2/κ)))) := by
  have hTwo : Magnitude 2 (2 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hFour : Magnitude 4 (4 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have h32 : Magnitude 32 (32 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hCoef : Magnitude A (A : ℝ) := Magnitude.natCast hA le_rfl
  have hH := rawHeight_magnitude hh
  have hH' : Magnitude (M+1) (1+(h : ℝ)) := by
    rw [add_comm (1 : ℝ) (h : ℝ)]
    exact hH
  exact ((hCoef.mul hH).pow 4).max ((h32.pow 4).max
    ((hFour.div hκ).max (((hTwo.mul hH').mul (hingePower_magnitude hh)).div hκ)))

theorem rawRequiredGeometry_magnitude {M h : ℕ} {α q : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hh : h ≤ M) :
    Magnitude (rawRequiredGeometryBound M) (rawRequiredGeometry α q h) := by
  have hM : 1 ≤ M := by have := hq.bound_pos; omega
  have hFour : Magnitude 4 (4 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hQ := (hq.pow h).mono (Nat.pow_le_pow_right hM hh)
  exact rawGeometryShape_magnitude ((hα.mul hQ).div hFour) (by decide : 1 ≤ 8) hh

theorem outerRawRequiredGeometry_magnitude {M h : ℕ} {α q : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hh : h ≤ M) :
    Magnitude (outerRawRequiredGeometryBound M) (outerRawRequiredGeometry α q h) := by
  have hM : 1 ≤ M := by have := hq.bound_pos; omega
  have hQ := (hq.pow h).mono (Nat.pow_le_pow_right hM hh)
  exact rawGeometryShape_magnitude (hα.mul hQ) (by decide : 1 ≤ 4) hh

theorem rawMinimumOrder_le {M h N R : ℕ} {α q : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hh : h ≤ M) (hN : N ≤ M) (hR : R ≤ M) :
    rawMinimumOrder α q h N R ≤ rawMinimumOrderBound M := by
  have hFour : Magnitude 4 (4 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hM : M ≤ M*4 := by omega
  have hPrep := preparationOrder_le_majorant (hα.div hFour) (hh.trans hM) (hN.trans hM)
  exact max_le_max (max_le_max hPrep hR)
    (max_le_max le_rfl (Nat.add_le_add_right (rawRequiredGeometry_magnitude hα hq hh).ceil_le 1))

theorem outerRawMinimumOrder_le {M h N R : ℕ} {α q : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hh : h ≤ M) (hN : N ≤ M) (hR : R ≤ M) :
    outerRawMinimumOrder α q h N R ≤ outerRawMinimumOrderBound M := by
  have hFour : Magnitude 4 (4 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hM : M ≤ M*4 := by omega
  have hPrep := preparationOrder_le_majorant (hα.div hFour) (hh.trans hM) (hN.trans hM)
  exact max_le_max (max_le_max hPrep hR)
    (max_le_max le_rfl (Nat.add_le_add_right (outerRawRequiredGeometry_magnitude hα hq hh).ceil_le 1))

theorem rawRootOrder_le {M h N R : ℕ} {α q : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hh : h ≤ M) (hN : N ≤ M) (hR : R ≤ M) :
    rawRootOrder α q h N R ≤ rawRootOrderBound M :=
  Nat.mul_le_mul_left 2 (rawMinimumOrder_le hα hq hh hN hR)

private theorem rawRatio_le {M B n : ℕ} {q : ℝ}
    (hq : Magnitude M q) (hn : n ≤ B) :
    2*(n : ℝ)/q ≤ ((2*B*M : ℕ) : ℝ) := by
  have hProd := mul_le_mul (Nat.cast_le.mpr hn : (n : ℝ) ≤ B) hq.inv_upper
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hq.pos.le) (Nat.cast_nonneg B)
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    2*(n : ℝ)/q = 2*((n : ℝ)*(1/q)) := by ring
    _ ≤ 2*((B : ℝ)*M) := mul_le_mul_of_nonneg_left hProd (by norm_num)
    _ = 2*(B : ℝ)*M := by ring

theorem globalRawStepOrder_le {M h n : ℕ} {α C q : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hq : Magnitude M q)
    (hh : h ≤ M) (hn : n ≤ M) :
    globalRawStepOrder α C q h n ≤ (globalRawStepOrderBound M : ℝ) := by
  let S := rawGlobalInputBound M
  have h0 : M ≤ S := by dsimp only [S, rawGlobalInputBound]; omega
  have h1 : M*2 ≤ S := by dsimp only [S, rawGlobalInputBound]; omega
  have h2' : 2*M ≤ S := by dsimp only [S, rawGlobalInputBound]; omega
  have hTwo : Magnitude 2 (2 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hEight : Magnitude 8 (8 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hSample := rawNativeSampleOrder_magnitude ((hα.div hTwo).mono h1) (hq.mono h0)
    ((hTwo.mul hC).mono h2') (hh.trans h0)
  have hHeight := ((hEight.mul (rawHeight_magnitude hh)).pow 4).upper
  simpa only [S, globalRawStepOrder, globalRawStepOrderBound, Nat.cast_max, Nat.cast_one] using
    max_le_max (max_le_max hSample.upper hHeight)
      (max_le_max (rawRatio_le hq hn) (le_rfl : (1 : ℝ) ≤ 1))

theorem rawTerminalOrder_le {M h N R : ℕ} {α C q : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hq : Magnitude M q)
    (hh : h ≤ M) (hN : N ≤ M) (hR : R ≤ M) :
    rawTerminalOrder α C q h N R ≤ (rawTerminalOrderBound M : ℝ) := by
  let S := rawTerminalInputBound M
  have h0 : M ≤ S := by dsimp only [S, rawTerminalInputBound]; omega
  have hMin := rawMinimumOrder_le hα hq hh hN hR
  have hArg : 2*rawMinimumOrder α q h N R ≤ S :=
    (Nat.mul_le_mul_left 2 hMin).trans (le_max_right _ _)
  have hGlobal := globalRawStepOrder_le (hα.mono h0) (hC.mono h0) (hq.mono h0) (hh.trans h0) hArg
  simpa only [rawTerminalOrder, rawTerminalOrderBound, Nat.cast_max] using
    max_le_max hGlobal (Nat.cast_le.mpr hMin : (rawMinimumOrder α q h N R : ℝ) ≤ rawMinimumOrderBound M)

theorem outerRawRootOrder_le {M T h N R : ℕ} {α C q θ : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hq : Magnitude M q) (hθ : Magnitude T θ)
    (hh : h ≤ M) (hN : N ≤ M) (hR : R ≤ M) :
    outerRawRootOrder α C q θ h N R ≤ outerRawRootOrderBound M T := by
  let S := outerRawAutoInputBound M
  have h0 : M ≤ S := by dsimp only [S, outerRawAutoInputBound]; omega
  have h1 : 4*M ≤ S := by dsimp only [S, outerRawAutoInputBound]; omega
  have h2' : 2*M ≤ S := by dsimp only [S, outerRawAutoInputBound]; omega
  have hFour : Magnitude 4 (4 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hTwo : Magnitude 2 (2 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hAuto := rawAutomaticOrder_magnitude ((hFour.mul hα).mono h1) (hq.mono h0)
    ((hTwo.mul hC).mono h2') hθ (hh.trans h0)
  have hMin := outerRawMinimumOrder_le hα hq hh hN hR
  have hUpper : max (automaticRawOrder (4*α) q (2*C) θ h)
      (max (outerRawMinimumOrder α q h N R : ℝ) (2*(outerRawMinimumOrder α q h N R : ℝ)/q)) ≤
      (max (rawAutomaticOrderBound S T)
        (max (outerRawMinimumOrderBound M) (2*outerRawMinimumOrderBound M*M)) : ℕ) := by
    simpa only [Nat.cast_max] using max_le_max hAuto.upper
      (max_le_max (Nat.cast_le.mpr hMin : (outerRawMinimumOrder α q h N R : ℝ) ≤ outerRawMinimumOrderBound M)
        (rawRatio_le hq hMin))
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.ceil_le.mpr hUpper)) 2

theorem nativeOuterRootOrder_le {M h N R : ℕ} {α C q : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hq : Magnitude M q)
    (hh : h ≤ M) (hN : N ≤ M) (hR : R ≤ M) :
    nativeOuterRootOrder α C q h N R ≤ nativeOuterRootOrderBound M := by
  let S := nativeOuterInputBound M
  have h0 : M ≤ S := by dsimp only [S, nativeOuterInputBound]; omega
  have h1 : 8*M ≤ S := by dsimp only [S, nativeOuterInputBound]; omega
  have hEight : Magnitude 8 (8 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hα' := (hEight.mul hα).mono h1
  have hRate := rawOuterTestRate_magnitude hα' (hq.mono h0) (hh.trans h0)
  exact max_le_max (outerRawRootOrder_le hα hC hq hRate hh hN hR)
    (nativeRouteOrder_le_majorant hα' (hh.trans h0))

theorem outerInnerRootOrder_le {M h Ni No R : ℕ} {α C qi qo : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hqi : Magnitude M qi) (hqo : Magnitude M qo)
    (hh : h ≤ M) (hNi : Ni ≤ M) (hNo : No ≤ M) (hR : R ≤ M) :
    outerInnerRootOrder α C qi qo h Ni R No ≤ outerInnerRootOrderBound M := by
  let S := outerInnerInputBound M
  have h0 : M ≤ S := by dsimp only [S, outerInnerInputBound]; omega
  have hRoot := rawRootOrder_le hα hqi hh hNi hR
  have hFuture : max 16 (rawRootOrder α qi h Ni R) ≤ S :=
    (max_le_max_left 16 hRoot).trans (le_max_right _ _)
  exact nativeOuterRootOrder_le (hα.mono h0) (hC.mono h0) (hqo.mono h0)
    (hh.trans h0) (hNo.trans h0) hFuture

#print axioms rawRequiredGeometry_magnitude
#print axioms outerRawRequiredGeometry_magnitude
#print axioms rawMinimumOrder_le
#print axioms outerRawMinimumOrder_le
#print axioms rawRootOrder_le
#print axioms globalRawStepOrder_le
#print axioms rawTerminalOrder_le
#print axioms outerRawRootOrder_le
#print axioms nativeOuterRootOrder_le
#print axioms outerInnerRootOrder_le
end TypedTriangle.TowerBounds
