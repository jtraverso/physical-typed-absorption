module
public import RequestProject.TypedTriangle.TowerThresholdAgenda
public import RequestProject.TypedTriangle.TowerTrianglePacking
public import RequestProject.TypedTriangle.TowerParameterScale
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.TowerBounds
open Vortex Vortex.Explicit Vortex.ExplicitRaw

/-- Input normalization precedes the host, seed and weight family. -/
def triangleParameterScale (α C η : ℝ) (h q : ℕ) : ℕ :=
  max (parameterScale α C h) (max q (max ⌈η⌉₊ ⌈1/η⌉₊))

theorem triangleParameterScale_base (α C η : ℝ) (h q : ℕ) :
    parameterScale α C h ≤ triangleParameterScale α C η h q := le_max_left _ _

theorem triangle_eta_magnitude {α C η : ℝ} (h q : ℕ) (hη : 0 < η) :
    Magnitude (triangleParameterScale α C η h q) η := by
  have hupper : ⌈η⌉₊ ≤ triangleParameterScale α C η h q := by unfold triangleParameterScale; omega
  have hinv : ⌈1/η⌉₊ ≤ triangleParameterScale α C η h q := by unfold triangleParameterScale; omega
  exact ⟨hη,(Nat.le_ceil η).trans (Nat.cast_le.mpr hupper),
    (Nat.le_ceil (1/η)).trans (Nat.cast_le.mpr hinv)⟩

def triangleThresholdInputBase (K h q : ℕ) : ℕ :=
  let M := thresholdInputMajorant K h
  M+32*M+4*K+q+1

def triangleThresholdInputMajorant (K h q : ℕ) : ℕ :=
  let U := triangleThresholdInputBase K h q
  U+triangleComplementMajorant U+1

private theorem input_sum_bounds (m k q : ℕ) :
    m ≤ m+32*m+4*k+q+1 ∧ m*16 ≤ m+32*m+4*k+q+1 ∧
    2*m ≤ m+32*m+4*k+q+1 ∧ k*4 ≤ m+32*m+4*k+q+1 ∧
    q ≤ m+32*m+4*k+q+1 := by omega

private theorem pair_sum_bounds (a b : ℕ) : a ≤ a+b+1 ∧ b ≤ a+b+1 := by omega

theorem triangleThresholdInput_bounds {K hOriginal qStat : ℕ} {αOriginal C η : ℝ}
    (hα : Magnitude K αOriginal) (hC : Magnitude K C) (hη : Magnitude K η)
    (hh6 : 6 ≤ hOriginal) (hh : hOriginal ≤ K) :
    let B := triangleThresholdInputMajorant K hOriginal qStat
    ThresholdInputBounds B αOriginal C hOriginal ∧ Magnitude B (η/4) ∧ qStat ≤ B ∧
      Magnitude B (monitorComplementBudget (2*C) (initialDensity αOriginal hOriginal/16)
        (initialHingeOrder hOriginal) (η/4)) := by
  let M := thresholdInputMajorant K hOriginal
  let U := triangleThresholdInputBase K hOriginal qStat
  let B := triangleThresholdInputMajorant K hOriginal qStat
  have hb := input_sum_bounds M K qStat
  have hs := pair_sum_bounds U (triangleComplementMajorant U)
  have hMU : M ≤ U := hb.1
  have hUB : U ≤ B := hs.1
  have base : ThresholdInputBounds M αOriginal C hOriginal := thresholdInput_bounds hα hC hh6 hh
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h16 : Magnitude 16 (16:ℝ) := Magnitude.natCast (by decide) le_rfl
  have ha : Magnitude U (initialDensity αOriginal hOriginal/16) := (base.density.div h16).mono hb.2.1
  have hc : Magnitude U (2*C) := (h2.mul base.seedConstant).mono hb.2.2.1
  have hz : Magnitude U (η/4) := (hη.div h4).mono hb.2.2.2.1
  exact ⟨base.mono (hMU.trans hUB),hz.mono hUB,hb.2.2.2.2.trans hUB,
    (monitorComplement_magnitude hc ha hz (base.hingeOrder.trans hMU)).mono hs.2⟩

theorem thresholdAgenda_with_complement_bounds {M hOriginal : ℕ} {αOriginal C : ℝ}
    (b : ThresholdInputBounds M αOriginal C hOriginal) (εB : ℝ) (hεB : Magnitude M εB) :
    let α := initialDensity αOriginal hOriginal
    let h := initialHingeOrder hOriginal
    let ε := rawPreparationTolerance α C h
    let L := rawPreparationRank α h+(rawPreparationRank α h+1)*Nat.log 2 (rawPreparationTorsion α h)
    let mI := nativeInteriorCount (α/2) h
    let aI := nativeDensity (α/2) h
    let mO := nativeInteriorCount (8*α) h
    let aO := nativeDensity (8*α) h
    let δO := nativeOuterAvoidBudget (8*α) h
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
    (globalInnerRate_magnitude v.density v.innerDensity v.outerDensity (hεB.mono (hMU.trans hUV)) v.stock
      v.protection hρ v.hingeOrder v.innerCount_pos v.innerCount v.outerCount_pos v.outerCount).mono
      (by dsimp only [W,thresholdRadiusScale,V]; omega)
  have hζ : Magnitude W ζ :=
    (assemblyStateCap_magnitude v.density (hεB.mono (hMU.trans hUV)) v.stock v.protection v.innerDensity
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

#print axioms triangle_eta_magnitude
#print axioms triangleThresholdInput_bounds
#print axioms thresholdAgenda_with_complement_bounds
end TypedTriangle.TowerBounds
