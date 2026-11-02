module
public import RequestProject.TypedTriangle.TowerGlobalScalars
public import RequestProject.TypedTriangle.TowerBankBudgets
public import RequestProject.TypedTriangle.TowerBankResources
public import RequestProject.TypedTriangle.TowerGeometryPaths
public import RequestProject.TypedTriangle.TowerGeometryPreparation
public import RequestProject.TypedTriangle.ExplicitPaperIIIThreshold
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.TowerBounds
open Vortex Vortex.Explicit Vortex.ExplicitRaw

def initialHingeOrder (h : ℕ) : ℕ := 2*h-3
noncomputable def initialDensity (α : ℝ) (h : ℕ) : ℝ :=
  min α (S07V49.hingeConstB α 1 h)/8

def normalizedDensityMajorant (K : ℕ) : ℕ := max K (hingeDensityMajorant K)*8
def normalizedInputScale (K : ℕ) : ℕ := K+2*K+normalizedDensityMajorant K+1
def thresholdWorkingScale (K : ℕ) : ℕ := normalizedInputScale K*32
def rawToleranceMajorant (M : ℕ) : ℕ :=
  max (preparationToleranceMajorant (M*4)) (max (hingeRatioMajorant M 4) (8*max 1 (2*M)))
def rawRankMajorant (M : ℕ) : ℕ := preparationRankMajorant (M*4)
def rawTorsionMajorant (M : ℕ) : ℕ := preparationTorsionMajorant (M*4)
def rawLengthMajorant (M : ℕ) : ℕ := rawRankMajorant M+(rawRankMajorant M+1)*rawTorsionMajorant M
def nativeOuterAvoidMajorant (M : ℕ) : ℕ := max (nativeAvoidMajorant M) (max (M*2) 2)
def initialComplementMajorant (M : ℕ) : ℕ :=
  max (referenceSeedBudgetBound M) (max (geometryBudgetMajorant M) (latticeBudgetMajorant M))
def cleanHingeOrderMajorant (M : ℕ) : ℕ := max (48*M) (8*(M+6)*compressionPowerMajorant M*M)
def thresholdInputMajorant (K hOriginal : ℕ) : ℕ :=
  let M := thresholdWorkingScale K
  M+rawToleranceMajorant M+rawRankMajorant M+rawTorsionMajorant M+rawLengthMajorant M+
    nativeInteriorMajorant M+nativeDensityMajorant M+nativeOuterAvoidMajorant M+
    initialComplementMajorant M+resourceStockMajorant M+
    bankProtectionBound M (initialHingeOrder hOriginal)+cleanHingeOrderMajorant K+1

theorem initialDensity_magnitude {K h : ℕ} {α : ℝ}
    (hα : Magnitude K α) (hh1 : 1 ≤ h) (hh : h ≤ K) :
    Magnitude (normalizedDensityMajorant K) (initialDensity α h) := by
  have hOne : Magnitude K (1:ℝ) := Magnitude.one.mono (by have := hα.bound_pos; omega)
  exact (hα.min (hingeDensity_magnitude hα hOne hh1 hh)).div
    (Magnitude.natCast (by decide : 1 ≤ (8:ℕ)) (le_refl 8))

theorem rawTolerance_magnitude {M h : ℕ} {α C : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hh : h ≤ M) :
    Magnitude (rawToleranceMajorant M) (rawPreparationTolerance α C h) := by
  have h4 := Magnitude.natCast (by decide : 1 ≤ (4:ℕ)) (le_refl 4)
  have h2 := Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) (le_refl 2)
  have h8 := Magnitude.natCast (by decide : 1 ≤ (8:ℕ)) (le_refl 8)
  exact (preparationTolerance_magnitude (hα.div h4) (by omega : h ≤ M*4)).min
    ((hingeRatio_magnitude hα hh 4 (by decide)).min ((h8.mul (Magnitude.one.max (h2.mul hC))).inv))

theorem rawRank_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : rawPreparationRank α h ≤ rawRankMajorant M :=
  preparationRank_le_majorant
    (hα.div (Magnitude.natCast (by decide : 1 ≤ (4:ℕ)) (le_refl 4))) (by omega)

theorem rawTorsion_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : rawPreparationTorsion α h ≤ rawTorsionMajorant M :=
  preparationTorsion_le_majorant
    (hα.div (Magnitude.natCast (by decide : 1 ≤ (4:ℕ)) (le_refl 4))) (by omega)

theorem rawLength_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    rawPreparationRank α h+(rawPreparationRank α h+1)*Nat.log 2 (rawPreparationTorsion α h) ≤
      rawLengthMajorant M := by
  have hd := rawRank_le_majorant hα hh
  have hT := rawTorsion_le_majorant hα hh
  exact Nat.add_le_add hd (Nat.mul_le_mul (Nat.add_le_add_right hd 1) ((Nat.log_le_self 2 _).trans hT))

theorem nativeOuterAvoid_magnitude {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (nativeOuterAvoidMajorant M) (nativeOuterAvoidBudget α h) := by
  have h2 := Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) (le_refl 2)
  exact (nativeAvoidBudget_magnitude hα hh).min ((hα.div h2).min h2.inv)

theorem initialComplement_magnitude {M h : ℕ} {C α : ℝ}
    (hC : Magnitude M C) (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (initialComplementMajorant M) (complementBudget C α h) :=
  (referenceSeedBudget_magnitude hC.inv hC hα hh).min
    ((geometryBudget_magnitude hα hh).min (latticeBudget_magnitude hα hh))

theorem cleanHingeOrder_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : cleanHingeOrder α h ≤ cleanHingeOrderMajorant M := by
  have h48 := (Magnitude.natCast (by decide : 1 ≤ (48:ℕ)) (le_refl 48)).div hα
  have hn := Magnitude.natCast (by omega : 1 ≤ h+6) (Nat.add_le_add_right hh 6)
  have h8 := Magnitude.natCast (by decide : 1 ≤ (8:ℕ)) (le_refl 8)
  have hprod := (h8.mul hn).mul (hingePower_magnitude hh)
  have hceil := (h48.max (hprod.div hα)).ceil_le
  change ⌈max (48/α) (8*((h:ℝ)+6)*2^h.choose 2/α)⌉₊ ≤ cleanHingeOrderMajorant M
  simpa only [cleanHingeOrderMajorant, Nat.cast_add, Nat.cast_ofNat] using hceil

structure ThresholdInputBounds (M : ℕ) (αOriginal C : ℝ) (hOriginal : ℕ) : Prop where
  density : Magnitude M (initialDensity αOriginal hOriginal)
  seedConstant : Magnitude M C
  hingeOrder : initialHingeOrder hOriginal ≤ M
  hingeOrder_six : 6 ≤ initialHingeOrder hOriginal
  tolerance : Magnitude M (rawPreparationTolerance (initialDensity αOriginal hOriginal) C (initialHingeOrder hOriginal))
  rank : rawPreparationRank (initialDensity αOriginal hOriginal) (initialHingeOrder hOriginal) ≤ M
  torsion : rawPreparationTorsion (initialDensity αOriginal hOriginal) (initialHingeOrder hOriginal) ≤ M
  length : rawPreparationRank (initialDensity αOriginal hOriginal) (initialHingeOrder hOriginal)+
    (rawPreparationRank (initialDensity αOriginal hOriginal) (initialHingeOrder hOriginal)+1)*
      Nat.log 2 (rawPreparationTorsion (initialDensity αOriginal hOriginal) (initialHingeOrder hOriginal)) ≤ M
  innerCount : nativeInteriorCount (initialDensity αOriginal hOriginal/2) (initialHingeOrder hOriginal) ≤ M
  innerCount_pos : 0 < nativeInteriorCount (initialDensity αOriginal hOriginal/2) (initialHingeOrder hOriginal)
  innerDensity : Magnitude M (nativeDensity (initialDensity αOriginal hOriginal/2) (initialHingeOrder hOriginal))
  outerCount : nativeInteriorCount (8*initialDensity αOriginal hOriginal) (initialHingeOrder hOriginal) ≤ M
  outerCount_pos : 0 < nativeInteriorCount (8*initialDensity αOriginal hOriginal) (initialHingeOrder hOriginal)
  outerDensity : Magnitude M (nativeDensity (8*initialDensity αOriginal hOriginal) (initialHingeOrder hOriginal))
  outerAvoid : Magnitude M (nativeOuterAvoidBudget (8*initialDensity αOriginal hOriginal) (initialHingeOrder hOriginal))
  complement : Magnitude M (complementBudget (2*C) (initialDensity αOriginal hOriginal/16) (initialHingeOrder hOriginal))
  stock : Magnitude M (resourceStockBudget (initialDensity αOriginal hOriginal/16) (2*C))
  protection : Magnitude M (CatalogNative.Explicit.bankProtectionBudget
    (initialDensity αOriginal hOriginal/16) (initialDensity αOriginal hOriginal/32) (initialHingeOrder hOriginal))
  cleanOrder : cleanHingeOrder αOriginal hOriginal ≤ M

theorem thresholdInput_bounds {K hOriginal : ℕ} {αOriginal C : ℝ}
    (hα : Magnitude K αOriginal) (hC : Magnitude K C) (hh6 : 6 ≤ hOriginal) (hh : hOriginal ≤ K) :
    ThresholdInputBounds (thresholdInputMajorant K hOriginal) αOriginal C hOriginal := by
  let N := normalizedInputScale K
  let M := thresholdWorkingScale K
  have hKN : K ≤ N := by dsimp only [N, normalizedInputScale]; omega
  have hAN : normalizedDensityMajorant K ≤ N := by dsimp only [N, normalizedInputScale]; omega
  have hNM : N ≤ M := by dsimp only [M, thresholdWorkingScale]; change N ≤ N*32; omega
  have hH : initialHingeOrder hOriginal ≤ M := by
    have h2 : 2*K ≤ N := by dsimp only [N, normalizedInputScale]; omega
    unfold initialHingeOrder
    omega
  have hA : Magnitude N (initialDensity αOriginal hOriginal) :=
    (initialDensity_magnitude hα (by omega) hh).mono hAN
  have hCP : Magnitude M C := (hC.mono hKN).mono hNM
  have hAP : Magnitude M (initialDensity αOriginal hOriginal) := hA.mono hNM
  have h2 := Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) (le_refl 2)
  have h8 := Magnitude.natCast (by decide : 1 ≤ (8:ℕ)) (le_refl 8)
  have h16 := Magnitude.natCast (by decide : 1 ≤ (16:ℕ)) (le_refl 16)
  have h32 := Magnitude.natCast (by decide : 1 ≤ (32:ℕ)) (le_refl 32)
  have hAi : Magnitude M (initialDensity αOriginal hOriginal/2) := (hA.div h2).mono (by change N*2 ≤ N*32; omega)
  have hAo : Magnitude M (8*initialDensity αOriginal hOriginal) := (h8.mul hA).mono (by change 8*N ≤ N*32; omega)
  have hAw : Magnitude M (initialDensity αOriginal hOriginal/16) := (hA.div h16).mono (by change N*16 ≤ N*32; omega)
  have hAb : Magnitude M (initialDensity αOriginal hOriginal/32) := hA.div h32
  have hC2 : Magnitude M (2*C) := (h2.mul (hC.mono hKN)).mono (by change 2*N ≤ N*32; omega)
  have hAll : M ≤ thresholdInputMajorant K hOriginal ∧
      rawToleranceMajorant M ≤ thresholdInputMajorant K hOriginal ∧
      rawRankMajorant M ≤ thresholdInputMajorant K hOriginal ∧
      rawTorsionMajorant M ≤ thresholdInputMajorant K hOriginal ∧
      rawLengthMajorant M ≤ thresholdInputMajorant K hOriginal ∧
      nativeInteriorMajorant M ≤ thresholdInputMajorant K hOriginal ∧
      nativeDensityMajorant M ≤ thresholdInputMajorant K hOriginal ∧
      nativeOuterAvoidMajorant M ≤ thresholdInputMajorant K hOriginal ∧
      initialComplementMajorant M ≤ thresholdInputMajorant K hOriginal ∧
      resourceStockMajorant M ≤ thresholdInputMajorant K hOriginal ∧
      bankProtectionBound M (initialHingeOrder hOriginal) ≤ thresholdInputMajorant K hOriginal ∧
      cleanHingeOrderMajorant K ≤ thresholdInputMajorant K hOriginal := by
    dsimp only [M, thresholdInputMajorant]
    omega
  obtain ⟨hM,hTol,hRank,hTor,hLength,hInt,hDen,hAvoid,hComp,hStock,hProt,hClean⟩ := hAll
  refine ⟨hAP.mono hM,hCP.mono hM,hH.trans hM,?_,
    (rawTolerance_magnitude hAP hCP hH).mono hTol,
    (rawRank_le_majorant hAP hH).trans hRank,
    (rawTorsion_le_majorant hAP hH).trans hTor,
    (rawLength_le_majorant hAP hH).trans hLength,
    (nativeInteriorCount_le_majorant hAi hH).trans hInt,?_,
    (nativeDensity_magnitude hAi hH).mono hDen,
    (nativeInteriorCount_le_majorant hAo hH).trans hInt,?_,
    (nativeDensity_magnitude hAo hH).mono hDen,
    (nativeOuterAvoid_magnitude hAo hH).mono hAvoid,
    (initialComplement_magnitude hC2 hAw hH).mono hComp,
    (resourceStock_magnitude hAw hC2).mono hStock,
    (bankProtection_magnitude hAw hAb _).mono hProt,
    (cleanHingeOrder_le_majorant hα hh).trans hClean⟩
  · unfold initialHingeOrder; omega
  · unfold nativeInteriorCount S07V24.Explicit.pathInteriorCount; omega
  · unfold nativeInteriorCount S07V24.Explicit.pathInteriorCount; omega

#print axioms initialDensity_magnitude
#print axioms rawTolerance_magnitude
#print axioms rawLength_le_majorant
#print axioms cleanHingeOrder_le_majorant
#print axioms thresholdInput_bounds
end TypedTriangle.TowerBounds
