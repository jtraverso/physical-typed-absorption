module
public import RequestProject.TypedTriangle.TowerGeometrySample
public import RequestProject.TypedTriangle.ExplicitNativeAvailablePaths
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TypedTriangle.TowerBounds
open S07V24.Explicit Vortex.ExplicitRaw

def oddPathMajorant (M : ℕ) : ℕ := 2*(4*((M+1)^2*(M+1)^5))+1
def pathDensityMajorant (M : ℕ) : ℕ := (M+1)^(oddPathMajorant M+3)*4
def oddPathOrderMajorant (M : ℕ) : ℕ :=
  4*(oddPathMajorant M+2)^2*((M+1)^(oddPathMajorant M+3))+1

theorem oddPathK_le_majorant {M : ℕ} {c κ : ℝ}
    (hc : Magnitude M c) (hκ : Magnitude M κ) : oddPathK c κ ≤ oddPathMajorant M := by
  have hc' := clipped_magnitude hc
  have hk' := clipped_magnitude hκ
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hb := h4.div ((hk'.pow 2).mul (hc'.pow 5))
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hb.ceil_le) 1

theorem pathDensity_magnitude {M : ℕ} {c κ : ℝ}
    (hc : Magnitude M c) (hκ : Magnitude M κ) :
    Magnitude (pathDensityMajorant M) (pathDensity c κ) := by
  have hc' := clipped_magnitude hc
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hpow : (M+1)^(oddPathK c κ+3) ≤ (M+1)^(oddPathMajorant M+3) :=
    Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right (oddPathK_le_majorant hc hκ) 3)
  exact ((hc'.pow (oddPathK c κ+3)).div h4).mono (Nat.mul_le_mul_right 4 hpow)

theorem oddPathOrder_le_majorant {M : ℕ} {c κ : ℝ}
    (hc : Magnitude M c) (hκ : Magnitude M κ) :
    oddPathOrder c κ ≤ oddPathOrderMajorant M := by
  have hk := oddPathK_le_majorant hc hκ
  have hc' := clipped_magnitude hc
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hn : Magnitude (oddPathMajorant M+2) ((oddPathK c κ+2:ℕ):ℝ) :=
    Magnitude.natCast (by omega) (by omega)
  have hb := (h4.mul (hn.pow 2)).div (hc'.pow (oddPathK c κ+3))
  have hp : (M+1)^(oddPathK c κ+3) ≤ (M+1)^(oddPathMajorant M+3) :=
    Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right hk 3)
  have hcceil : ⌈4*((oddPathK c κ:ℝ)+2)^2/(min c 1)^(oddPathK c κ+3)⌉₊ ≤
      4*(oddPathMajorant M+2)^2*((M+1)^(oddPathMajorant M+3)) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,compressionClipMajorant] using
      hb.ceil_le.trans (Nat.mul_le_mul_left (4*(oddPathMajorant M+2)^2) hp)
  exact Nat.add_le_add_right hcceil 1

def nativeRhoMajorant (M : ℕ) : ℕ := max 1 (M*(8*compressionPowerMajorant M))
def nativeKappaMajorant (M : ℕ) : ℕ := nativeRhoMajorant M^2*2
def nativePathInputMajorant (M : ℕ) : ℕ := M+nativeKappaMajorant M+1
def nativeInteriorMajorant (M : ℕ) : ℕ := oddPathMajorant (nativePathInputMajorant M)+1
def nativeDensityMajorant (M : ℕ) : ℕ := pathDensityMajorant (nativePathInputMajorant M)
def nativeAvoidMajorant (M : ℕ) : ℕ := nativeDensityMajorant M*(4*nativeInteriorMajorant M)
def nativeRouteOrderMajorant (M : ℕ) : ℕ :=
  max (oddPathOrderMajorant (nativePathInputMajorant M)) (3*M+1)

theorem nativeKappa_magnitude {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (nativeKappaMajorant M) (S07V25.kappaOf α h) := by
  have h8 : Magnitude 8 (8:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hρ : Magnitude (nativeRhoMajorant M) (S07V25.rhoOf α h) :=
    Magnitude.one.min (hα.div (h8.mul (hingePower_magnitude hh)))
  exact (hρ.pow 2).div h2

theorem nativeInteriorCount_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : nativeInteriorCount α h ≤ nativeInteriorMajorant M := by
  let U := nativePathInputMajorant M
  have hα' : Magnitude U α := hα.mono (by dsimp [U,nativePathInputMajorant]; omega)
  have hk : Magnitude U (S07V25.kappaOf α h) := (nativeKappa_magnitude hα hh).mono
    (by dsimp [U,nativePathInputMajorant]; omega)
  exact Nat.add_le_add_right (oddPathK_le_majorant hα' hk) 1

theorem nativeDensity_magnitude {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (nativeDensityMajorant M) (nativeDensity α h) := by
  let U := nativePathInputMajorant M
  have hα' : Magnitude U α := hα.mono (by dsimp [U,nativePathInputMajorant]; omega)
  have hk : Magnitude U (S07V25.kappaOf α h) := (nativeKappa_magnitude hα hh).mono
    (by dsimp [U,nativePathInputMajorant]; omega)
  exact pathDensity_magnitude hα' hk

theorem nativeAvoidBudget_magnitude {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (nativeAvoidMajorant M) (nativeAvoidBudget α h) := by
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hm : 1 ≤ nativeInteriorCount α h := by
    unfold nativeInteriorCount pathInteriorCount
    omega
  have hnat : Magnitude (nativeInteriorMajorant M) ((nativeInteriorCount α h:ℕ):ℝ) :=
    Magnitude.natCast hm (nativeInteriorCount_le_majorant hα hh)
  exact (nativeDensity_magnitude hα hh).div (h4.mul hnat)

theorem nativeRouteOrder_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : nativeRouteOrder α h ≤ nativeRouteOrderMajorant M := by
  let U := nativePathInputMajorant M
  have hα' : Magnitude U α := hα.mono (by dsimp [U,nativePathInputMajorant]; omega)
  have hk : Magnitude U (S07V25.kappaOf α h) := (nativeKappa_magnitude hα hh).mono
    (by dsimp [U,nativePathInputMajorant]; omega)
  have h3 : Magnitude 3 (3:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact max_le_max (oddPathOrder_le_majorant hα' hk) (Nat.add_le_add_right (h3.div hα).ceil_le 1)

#print axioms nativeAvoidBudget_magnitude
#print axioms nativeRouteOrder_le_majorant
end TypedTriangle.TowerBounds
