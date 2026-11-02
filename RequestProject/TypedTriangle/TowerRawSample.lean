module
public import RequestProject.TypedTriangle.TowerGeometryPaths
public import RequestProject.TypedTriangle.ExplicitAutomaticNativePaths
public import RequestProject.TypedTriangle.ExplicitNativeOuterTests
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.TowerBounds
open Finset RawReference.Explicit Vortex.ExplicitRaw

def rawHingeRateBound (M : ℕ) : ℕ :=
  (M^2 * M^(2*(M+2))) * ((4*(compressionPowerMajorant (M+6))^2)*(M+2))
def rawGeometryRateBound (M : ℕ) : ℕ :=
  max (M^2*4) (max ((M^2*M^2)*4) (rawHingeRateBound M))
def rawNativeTailBound (M : ℕ) : ℕ :=
  (nativeDensityMajorant M * M^(2*nativeInteriorMajorant M)) * (16*(nativeInteriorMajorant M)^2)
def rawTestRateBound (M T : ℕ) : ℕ :=
  max (rawGeometryRateBound M) (max (M^2*(8*M)) T)
def rawPolynomialBound (R : ℕ) : ℕ := max 1 ((4*Nat.factorial 14)*R^14)
def rawAutomaticOrderBound (M T : ℕ) : ℕ :=
  max 1 (max (rawPolynomialBound (rawTestRateBound M T)) 3)
def rawNativeSampleOrderBound (M : ℕ) : ℕ :=
  max (rawAutomaticOrderBound M (rawNativeTailBound M)) (max (nativeRouteOrderMajorant M) 1)
def rawOuterTestRateBound (M : ℕ) : ℕ :=
  max (((M*2)^2*M^2)*16)
    (((nativeDensityMajorant M*2)*M^(2*nativeInteriorMajorant M)) * (16*(nativeInteriorMajorant M)^2))

theorem rawHingeRate_magnitude {M j : ℕ} {α q : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hj : j ≤ M) :
    Magnitude (rawHingeRateBound M) (hingeGeometryRate α q j) := by
  have hM : 1 ≤ M := by have := hq.bound_pos; omega
  have hFour : Magnitude 4 (4 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hQ := (hq.pow (2*(j+2))).mono
    (Nat.pow_le_pow_right hM (by omega : 2*(j+2) ≤ 2*(M+2)))
  have hP := hingePower_magnitude (Nat.add_le_add_right hj 6)
  have hJ : Magnitude (M+2) ((j : ℝ)+2) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (Magnitude.natCast (n := j+2) (by omega) (by omega : j+2 ≤ M+2))
  exact ((hα.pow 2).mul hQ).div ((hFour.mul (hP.pow 2)).mul hJ)

theorem rawHingeMinimum_magnitude {M h : ℕ} {α q : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hh : h ≤ M) :
    Magnitude (rawHingeRateBound M) (hingeGeometryMinimum α q h) := by
  classical
  unfold hingeGeometryMinimum
  obtain ⟨j, _, heq⟩ := Finset.exists_mem_eq_inf'
    (s := (univ : Finset (Fin (h+1)))) ⟨0, mem_univ _⟩
    (fun j => hingeGeometryRate α q (j : ℕ))
  rw [heq]
  exact rawHingeRate_magnitude hα hq (by have := j.isLt; omega)

theorem rawGeometryRate_magnitude {M h : ℕ} {α q : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hh : h ≤ M) :
    Magnitude (rawGeometryRateBound M) (geometryRate α q h) := by
  have hFour : Magnitude 4 (4 : ℝ) := Magnitude.natCast (by decide) le_rfl
  exact ((hq.pow 2).div hFour).min
    ((((hα.pow 2).mul (hq.pow 2)).div hFour).min (rawHingeMinimum_magnitude hα hq hh))

private theorem rawNativeCount_magnitude {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (nativeInteriorMajorant M) (nativeInteriorCount α h : ℝ) := by
  have hm : 1 ≤ nativeInteriorCount α h := by
    unfold nativeInteriorCount S07V24.Explicit.pathInteriorCount
    omega
  exact Magnitude.natCast hm (nativeInteriorCount_le_majorant hα hh)

theorem rawNativeTail_magnitude {M h : ℕ} {α q : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hh : h ≤ M) :
    Magnitude (rawNativeTailBound M) (nativePathTailRate α q h) := by
  have hM : 1 ≤ M := by have := hq.bound_pos; omega
  have h16 : Magnitude 16 (16 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hCount := nativeInteriorCount_le_majorant hα hh
  have hQ := (hq.pow (2*nativeInteriorCount α h)).mono
    (Nat.pow_le_pow_right hM (Nat.mul_le_mul_left 2 hCount))
  exact ((nativeDensity_magnitude hα hh).mul hQ).div
    (h16.mul ((rawNativeCount_magnitude hα hh).pow 2))

theorem rawTestRate_magnitude {M T h : ℕ} {α q b θ : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hb : Magnitude M b)
    (hθ : Magnitude T θ) (hh : h ≤ M) :
    Magnitude (rawTestRateBound M T) (rawTestRate α q b θ h) := by
  have h8 : Magnitude 8 (8 : ℝ) := Magnitude.natCast (by decide) le_rfl
  exact (rawGeometryRate_magnitude hα hq hh).min (((hq.pow 2).div (h8.mul hb)).min hθ)

theorem rawPolynomial_magnitude {R : ℕ} {c : ℝ} (hc : Magnitude R c) :
    Magnitude (rawPolynomialBound R) (RawReference.polynomialSqrtCut 6 c) := by
  have hFour : Magnitude 4 (4 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hFactorial : Magnitude (Nat.factorial 14) (Nat.factorial 14 : ℝ) :=
    Magnitude.natCast (Nat.factorial_pos _) le_rfl
  exact Magnitude.one.max ((hFour.mul hFactorial).div (hc.pow 14))

theorem rawAutomaticOrder_magnitude {M T h : ℕ} {α q b θ : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hb : Magnitude M b)
    (hθ : Magnitude T θ) (hh : h ≤ M) :
    Magnitude (rawAutomaticOrderBound M T) (automaticRawOrder α q b θ h) := by
  have hThree : Magnitude 3 (3 : ℝ) := Magnitude.natCast (by decide) le_rfl
  exact Magnitude.one.max ((rawPolynomial_magnitude (rawTestRate_magnitude hα hq hb hθ hh)).max hThree)

theorem rawNativeSampleOrder_magnitude {M h : ℕ} {α q b : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hb : Magnitude M b) (hh : h ≤ M) :
    Magnitude (rawNativeSampleOrderBound M) (nativeSampleOrder α q b h) := by
  have hRoute : Magnitude (nativeRouteOrderMajorant M) (nativeRouteOrder α h : ℝ) := by
    have hn : 1 ≤ nativeRouteOrder α h := by unfold nativeRouteOrder S07V25.n1Of; omega
    exact Magnitude.natCast hn (nativeRouteOrder_le_majorant hα hh)
  exact (rawAutomaticOrder_magnitude hα hq hb (rawNativeTail_magnitude hα hq hh) hh).max
    (hRoute.max Magnitude.one)

theorem rawOuterTestRate_magnitude {M h : ℕ} {α q : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hh : h ≤ M) :
    Magnitude (rawOuterTestRateBound M) (nativeOuterTestRate α q h) := by
  have hM : 1 ≤ M := by have := hq.bound_pos; omega
  have hTwo : Magnitude 2 (2 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have h16 : Magnitude 16 (16 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hCount := nativeInteriorCount_le_majorant hα hh
  have hQ := (hq.pow (2*nativeInteriorCount α h)).mono
    (Nat.pow_le_pow_right hM (Nat.mul_le_mul_left 2 hCount))
  have hPool := (((hα.div hTwo).pow 2).mul (hq.pow 2)).div h16
  have hPath := (((nativeDensity_magnitude hα hh).div hTwo).mul hQ).div
    (h16.mul ((rawNativeCount_magnitude hα hh).pow 2))
  exact hPool.min hPath

#print axioms rawHingeRate_magnitude
#print axioms rawHingeMinimum_magnitude
#print axioms rawGeometryRate_magnitude
#print axioms rawTestRate_magnitude
#print axioms rawNativeTail_magnitude
#print axioms rawPolynomial_magnitude
#print axioms rawAutomaticOrder_magnitude
#print axioms rawNativeSampleOrder_magnitude
#print axioms rawOuterTestRate_magnitude
end TypedTriangle.TowerBounds
