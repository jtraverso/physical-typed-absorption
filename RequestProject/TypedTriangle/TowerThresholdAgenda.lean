module
public import RequestProject.TypedTriangle.TowerThresholdInputs
public import RequestProject.TypedTriangle.TowerReferenceAgenda
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.TowerBounds
open Vortex Vortex.Explicit Vortex.ExplicitRaw

theorem ThresholdInputBounds.mono {M N h : ℕ} {α C : ℝ}
    (b : ThresholdInputBounds M α C h) (hMN : M ≤ N) : ThresholdInputBounds N α C h :=
  ⟨b.density.mono hMN,b.seedConstant.mono hMN,b.hingeOrder.trans hMN,b.hingeOrder_six,
    b.tolerance.mono hMN,b.rank.trans hMN,b.torsion.trans hMN,b.length.trans hMN,
    b.innerCount.trans hMN,b.innerCount_pos,b.innerDensity.mono hMN,b.outerCount.trans hMN,
    b.outerCount_pos,b.outerDensity.mono hMN,b.outerAvoid.mono hMN,b.complement.mono hMN,
    b.stock.mono hMN,b.protection.mono hMN,b.cleanOrder.trans hMN⟩

def thresholdDensityScale (M : ℕ) : ℕ := M+8*M+1
def thresholdGlobalScale (M : ℕ) : ℕ :=
  let U := thresholdDensityScale M
  U+futureDensityMajorant U+1
def thresholdRadiusScale (M : ℕ) : ℕ :=
  let V := thresholdGlobalScale M
  V+globalInnerRateMajorant V+assemblyStateMajorant V+2*globalDebtMajorant V+1
def thresholdProfileScale (M : ℕ) : ℕ :=
  let W := thresholdRadiusScale M
  W+innerRadiusMajorant W+innerScheduleMajorant W+1
def thresholdAgendaMajorant (M : ℕ) : ℕ :=
  let P := thresholdProfileScale M
  P+paidCostMajorant P+referenceLoadMajorant P+referenceAvoidMajorant P+
    referenceThresholdMajorant P+paidInverseOrderMajorant P+paidOrderMajorant P+1

theorem thresholdAgenda_base_le (M : ℕ) : M ≤ thresholdAgendaMajorant M := by
  dsimp only [thresholdAgendaMajorant,thresholdProfileScale,thresholdRadiusScale,
    thresholdGlobalScale,thresholdDensityScale]
  omega

theorem thresholdAgenda_bounds {M hOriginal : ℕ} {αOriginal C : ℝ}
    (b : ThresholdInputBounds M αOriginal C hOriginal) :
    let α := initialDensity αOriginal hOriginal
    let h := initialHingeOrder hOriginal
    let ε := rawPreparationTolerance α C h
    let L := rawPreparationRank α h+(rawPreparationRank α h+1)*Nat.log 2 (rawPreparationTorsion α h)
    let mI := nativeInteriorCount (α/2) h
    let aI := nativeDensity (α/2) h
    let mO := nativeInteriorCount (8*α) h
    let aO := nativeDensity (8*α) h
    let δO := nativeOuterAvoidBudget (8*α) h
    let εB := complementBudget (2*C) (α/16) h
    let γB := resourceStockBudget (α/16) (2*C)
    let ηB := CatalogNative.Explicit.bankProtectionBudget (α/16) (α/32) h
    let ρ := futureDensity (α/8) C h
    let q := globalInnerRate α aI aO εB γB ηB ρ h mI mO
    let ζ := assemblyStateCap α C εB γB ηB aI aO h mI mO
    let β := assemblyRadius α C ε δO εB γB ηB aI aO h L mI mO
    let N := assemblyScheduleOrder α C ε δO εB γB ηB aI aO h L mI mO
    let B := thresholdAgendaMajorant M
    Magnitude B q ∧ (∀ r, Magnitude B (β r)) ∧ N ≤ B ∧
      (∀ r, Magnitude B (paidInverseCost (α/8) (β r) h)) ∧
      (∀ r, Magnitude B (referenceLoad (α/8) C ζ h (β r))) ∧
      (∀ r, Magnitude B (referenceAvoid (α/8) C ζ h (β r))) ∧
      (∀ r, referenceThreshold (α/8) C ζ h (β r) ≤ B) ∧
      paidInverseOrder (α/8) h ≤ B ∧ ExplicitPaid.paidOrder (α/8) h ≤ B := by
  let α := initialDensity αOriginal hOriginal
  let h := initialHingeOrder hOriginal
  let ε := rawPreparationTolerance α C h
  let L := rawPreparationRank α h+(rawPreparationRank α h+1)*Nat.log 2 (rawPreparationTorsion α h)
  let mI := nativeInteriorCount (α/2) h
  let aI := nativeDensity (α/2) h
  let mO := nativeInteriorCount (8*α) h
  let aO := nativeDensity (8*α) h
  let δO := nativeOuterAvoidBudget (8*α) h
  let εB := complementBudget (2*C) (α/16) h
  let γB := resourceStockBudget (α/16) (2*C)
  let ηB := CatalogNative.Explicit.bankProtectionBudget (α/16) (α/32) h
  let ρ := futureDensity (α/8) C h
  let q := globalInnerRate α aI aO εB γB ηB ρ h mI mO
  let ζ := assemblyStateCap α C εB γB ηB aI aO h mI mO
  let β := assemblyRadius α C ε δO εB γB ηB aI aO h L mI mO
  let N := assemblyScheduleOrder α C ε δO εB γB ηB aI aO h L mI mO
  let U := thresholdDensityScale M
  let V := thresholdGlobalScale M
  let W := thresholdRadiusScale M
  let P := thresholdProfileScale M
  let B := thresholdAgendaMajorant M
  have hMU : M ≤ U := by dsimp only [U,thresholdDensityScale]; omega
  have hUV : U ≤ V := by dsimp only [V,thresholdGlobalScale,U]; omega
  have hVW : V ≤ W := by dsimp only [W,thresholdRadiusScale,V]; omega
  have hWP : W ≤ P := by dsimp only [P,thresholdProfileScale,W]; omega
  have hPB : P ≤ B := by dsimp only [B,thresholdAgendaMajorant,P]; omega
  have hMW := hMU.trans (hUV.trans hVW)
  have hMP := hMW.trans hWP
  have hMB := hMP.trans hPB
  have u := b.mono hMU
  have v := b.mono (hMU.trans hUV)
  have w := b.mono hMW
  have p := b.mono hMP
  have h8 : Magnitude 8 (8:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hα8U : Magnitude U (α/8) := (b.density.div h8).mono (by dsimp only [U,thresholdDensityScale]; omega)
  have hρ : Magnitude V ρ := (futureDensity_magnitude hα8U u.seedConstant u.hingeOrder).mono
    (by dsimp only [V,thresholdGlobalScale,U]; omega)
  have hq : Magnitude W q :=
    (globalInnerRate_magnitude v.density v.innerDensity v.outerDensity v.complement v.stock
      v.protection hρ v.hingeOrder v.innerCount_pos v.innerCount v.outerCount_pos v.outerCount).mono
      (by dsimp only [W,thresholdRadiusScale,V]; omega)
  have hζ : Magnitude W ζ :=
    (assemblyStateCap_magnitude v.density v.complement v.stock v.protection v.innerDensity
      v.outerDensity hρ v.hingeOrder v.innerCount_pos v.innerCount v.outerCount_pos v.outerCount).mono
      (by dsimp only [W,thresholdRadiusScale,V]; omega)
  have hη : Magnitude W (2*globalDebtCap α C ε δO aI aO h mI mO) := by
    have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
    exact (h2.mul (globalDebt_magnitude v.density v.seedConstant v.tolerance v.outerAvoid
      v.innerDensity v.outerDensity v.hingeOrder v.innerCount_pos v.innerCount
      v.outerCount_pos v.outerCount)).mono (by dsimp only [W,thresholdRadiusScale,V]; omega)
  have hα8W := hα8U.mono (hUV.trans hVW)
  have hβ : ∀ r, Magnitude P (β r) := fun r =>
    (innerRadius_magnitude hα8W w.seedConstant w.tolerance hζ hη
      (by have := b.hingeOrder_six; omega) w.hingeOrder w.length r).mono
      (by dsimp only [P,thresholdProfileScale,W]; omega)
  have hN : N ≤ B :=
    (innerSchedule_le_majorant hα8W w.seedConstant w.tolerance hζ hη
      (by have := b.hingeOrder_six; omega) w.hingeOrder w.length).trans
      (by dsimp only [B,thresholdAgendaMajorant,P,thresholdProfileScale,W]; omega)
  have hα8P := hα8W.mono hWP
  have hζP := hζ.mono hWP
  have hh1 : 1 ≤ h := by have := b.hingeOrder_six; omega
  refine ⟨hq.mono (hWP.trans hPB),fun r => (hβ r).mono hPB,hN,?_,?_,?_,?_,?_,?_⟩
  · intro r
    exact (paidCost_magnitude hα8P (hβ r) hh1 p.hingeOrder).mono
      (by dsimp only [B,thresholdAgendaMajorant,P]; omega)
  · intro r
    exact (referenceLoad_magnitude hα8P p.seedConstant hζP (hβ r) hh1 p.hingeOrder).mono
      (by dsimp only [B,thresholdAgendaMajorant,P]; omega)
  · intro r
    exact (referenceAvoid_magnitude hα8P p.seedConstant hζP (hβ r) hh1 p.hingeOrder).mono
      (by dsimp only [B,thresholdAgendaMajorant,P]; omega)
  · intro r
    exact (referenceThreshold_le_majorant hα8P p.seedConstant hζP (hβ r) hh1 p.hingeOrder).trans
      (by dsimp only [B,thresholdAgendaMajorant,P]; omega)
  · exact (paidInverseOrder_le_majorant hα8P hh1 p.hingeOrder).trans
      (by dsimp only [B,thresholdAgendaMajorant,P]; omega)
  · exact (paidOrder_le_majorant hα8P p.hingeOrder).trans
      (by dsimp only [B,thresholdAgendaMajorant,P]; omega)

#print axioms thresholdAgenda_bounds
end TypedTriangle.TowerBounds
