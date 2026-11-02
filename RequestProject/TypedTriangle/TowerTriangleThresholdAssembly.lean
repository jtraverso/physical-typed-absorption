module
public import RequestProject.TypedTriangle.TowerTriangleThresholdAgenda
public import RequestProject.TypedTriangle.TowerTriangleLayerOrders
public import RequestProject.TypedTriangle.TowerThresholdAssembly
public import RequestProject.TypedTriangle.ExplicitPaperIIITriangleThreshold
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TypedTriangle.TowerBounds
open Vortex Vortex.Explicit Vortex.ExplicitRaw

def triangleThresholdFinalMajorant (U h : ℕ) : ℕ :=
  U+outerInnerRootOrderBound U+monitorOuterLayerOrderMajorant U h+U*outerLayerTerminalMajorant U+1

/-- A specified integer program; all arguments, intermediate values and
operations in this height are natural numbers. -/
def paperIIITriangleTowerHeight (K hOriginal qStat : ℕ) : ℕ :=
  let h := initialHingeOrder hOriginal
  let M := triangleThresholdInputMajorant K hOriginal qStat
  let A := thresholdAgendaMajorant M
  let R := thresholdLayerScale A h
  let T := thresholdTerminalScale R
  let U := thresholdReserveScale T h
  triangleThresholdFinalMajorant U h

private theorem layer_sum_bounds (a b c : ℕ) :
    a ≤ a+b+c+1 ∧ max b c ≤ a+b+c+1 := by omega

private theorem terminal_sum_bounds (a b : ℕ) :
    a ≤ a+b+8*a+1 ∧ b ≤ a+b+8*a+1 ∧ a*8 ≤ a+b+8*a+1 := by omega

private theorem reserve_sum_bounds (a b c d e : ℕ) :
    a ≤ a+b+4*a+c+d+e+1 ∧ b ≤ a+b+4*a+c+d+e+1 ∧
    a*4 ≤ a+b+4*a+c+d+e+1 ∧ c ≤ a+b+4*a+c+d+e+1 ∧
    d ≤ a+b+4*a+c+d+e+1 ∧ e ≤ a+b+4*a+c+d+e+1 := by omega

private theorem final_sum_bounds (a b c d : ℕ) :
    a ≤ a+b+c+d+1 ∧ b ≤ a+b+c+d+1 ∧ c ≤ a+b+c+d+1 ∧ d ≤ a+b+c+d+1 := by omega

theorem paperIIITriangleThreshold_le_naturalMajorant {K hOriginal qStat : ℕ} {αOriginal C η : ℝ}
    (hαOriginal : Magnitude K αOriginal) (hC : Magnitude K C) (hη : Magnitude K η)
    (hhOriginal : hOriginal ≤ K) (hhSix : 6 ≤ hOriginal) :
    paperIIITriangleThreshold αOriginal C η hOriginal qStat ≤ paperIIITriangleTowerHeight K hOriginal qStat := by
  let α := initialDensity αOriginal hOriginal
  let h := initialHingeOrder hOriginal
  let ε := rawPreparationTolerance α C h
  let d := rawPreparationRank α h
  let tor := rawPreparationTorsion α h
  let L := d+(d+1)*Nat.log 2 tor
  let mI := nativeInteriorCount (α/2) h
  let aI := nativeDensity (α/2) h
  let mO := nativeInteriorCount (8*α) h
  let aO := nativeDensity (8*α) h
  let δO := nativeOuterAvoidBudget (8*α) h
  let ζStat := η/4
  let εB := monitorComplementBudget (2*C) (α/16) h ζStat
  let γB := resourceStockBudget (α/16) (2*C)
  let ηB := CatalogNative.Explicit.bankProtectionBudget (α/16) (α/32) h
  let ρ := futureDensity (α/8) C h
  let qi := globalInnerRate α aI aO εB γB ηB ρ h mI mO
  let ζ := assemblyStateCap α C εB γB ηB aI aO h mI mO
  let β := assemblyRadius α C ε δO εB γB ηB aI aO h L mI mO
  let Ni := assemblyScheduleOrder α C ε δO εB γB ηB aI aO h L mI mO
  let costs := fun r => paidInverseCost (α/8) (β r) h
  let loads := fun r => referenceLoad (α/8) C ζ h (β r)
  let avoids := fun r => referenceAvoid (α/8) C ζ h (β r)
  let orders := fun r => referenceThreshold (α/8) C ζ h (β r)
  let paid := fun _ : ℕ => paidInverseOrder (α/8) h
  let geometry := ExplicitPaid.paidOrder (α/8) h
  let Mi := innerLayerOrder α C qi aI h mI L costs loads avoids orders paid geometry
  let Mr := max Mi (max 1 (scheduledProfileOrder C costs loads L))
  let t := rawTerminalOrder α C qi h Ni Mr
  let tN := ⌈t⌉₊
  let βF := fun r : Fin (L+1) => β r
  let qr := PreparedSupply.Explicit.uniformOuterRate (α/8) h tN L βF
  let qo := min qr (εB/4)
  let Nr := PreparedSupply.Explicit.absorberOrder (α/8) h
  let Na := PreparedSupply.Explicit.uniformReserveOrder (α/8) h tN L βF
  let No := max Nr Na
  let raw := outerInnerRootOrder α C qi qo h Ni Mr No
  let θ := outerLayerTerminalBudget α C qo aO h mO L avoids
  let outer := monitorOuterLayerOrder α C qo aO ζStat h mO L qStat avoids orders paid geometry
  let reserve := PreparedSupply.Explicit.reserveSize (α/8) h tN
  let M := triangleThresholdInputMajorant K hOriginal qStat
  let A := thresholdAgendaMajorant M
  let R := thresholdLayerScale A h
  let T := thresholdTerminalScale R
  let U := thresholdReserveScale T h
  let V := triangleThresholdFinalMajorant U h
  have hLayer := layer_sum_bounds A (innerLayerOrderMajorant A h) (max 1 (scheduledOrderMajorant A))
  have hTerminal := terminal_sum_bounds R (rawTerminalOrderBound R)
  have hReserve := reserve_sum_bounds T (terminalUniformRateMajorant T h)
    (terminalUniformOrderMajorant T h) (compressionOrderMajorant T) (terminalReserveSizeMajorant T h)
  have hFinal := final_sum_bounds U (outerInnerRootOrderBound U)
    (monitorOuterLayerOrderMajorant U h) (U*outerLayerTerminalMajorant U)
  have hMA : M ≤ A := thresholdAgenda_base_le M
  have hAR : A ≤ R := hLayer.1
  have hRT : R ≤ T := hTerminal.1
  have hTU : T ≤ U := hReserve.1
  have hAU := hAR.trans (hRT.trans hTU)
  obtain ⟨b0,hζM,hqM,hεBM⟩ := triangleThresholdInput_bounds (qStat:=qStat)
    hαOriginal hC hη hhSix hhOriginal
  have b := b0.mono hMA
  have bR := b.mono hAR
  have bT := bR.mono hRT
  have bU := bT.mono hTU
  obtain ⟨hqi,hβ,hNi,hcost,hload,havoid,horder,hpaid,hgeometry⟩ := thresholdAgenda_with_complement_bounds b0 εB hεBM
  have hh1 : 1 ≤ h := by have := b.hingeOrder_six; omega
  have hMi : Mi ≤ innerLayerOrderMajorant A h :=
    innerLayerOrder_le_majorant b.density b.seedConstant hqi b.innerDensity
      (fun r _ => hcost r) (fun r _ => hload r) (fun r _ => havoid r)
      (fun r _ => horder r) (fun _ _ => hpaid) hgeometry hh1 b.hingeOrder b.innerCount b.length
  have hMr : Mr ≤ R := by
    have hp := scheduledOrder_le_majorant (L:=L) b.seedConstant (fun r _ => hcost r) (fun r _ => hload r)
    have hm := max_le_max hMi (max_le_max_left 1 hp)
    exact hm.trans hLayer.2
  have ht : t ≤ (rawTerminalOrderBound R:ℝ) :=
    rawTerminalOrder_le bR.density bR.seedConstant (hqi.mono hAR) bR.hingeOrder (hNi.trans hAR) hMr
  have htN : tN ≤ T := (Nat.ceil_le.mpr ht).trans hTerminal.2.1
  have h8 : Magnitude 8 (8:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hα8 : Magnitude T (α/8) := (bR.density.div h8).mono hTerminal.2.2
  have hβT : ∀ r, Magnitude T (βF r) := fun r => (hβ r).mono (hAR.trans hRT)
  have hqr : Magnitude (terminalUniformRateMajorant T h) qr :=
    terminalUniformRate_magnitude (h:=h) hα8 bT.hingeOrder htN βF hβT
  have hqo : Magnitude U qo := (hqr.min ((hεBM.mono (hMA.trans (hAR.trans hRT))).div h4)).mono
    (max_le hReserve.2.1 hReserve.2.2.1)
  have hNr : Nr ≤ U := (compressionOrder_le_majorant hα8 bT.hingeOrder).trans
    hReserve.2.2.2.2.1
  have hNa : Na ≤ U := (terminalUniformOrder_le_majorant (h:=h) hα8 bT.hingeOrder htN βF hβT).trans
    hReserve.2.2.2.1
  have hNo : No ≤ U := max_le hNr hNa
  have hreserve : reserve ≤ U := (terminalReserveSize_le_majorant (h:=h) hα8 bT.hingeOrder htN).trans
    hReserve.2.2.2.2.2
  have hraw : raw ≤ outerInnerRootOrderBound U :=
    outerInnerRootOrder_le bU.density bU.seedConstant (hqi.mono hAU) hqo
      bU.hingeOrder (hNi.trans hAU) hNo (hMr.trans (hRT.trans hTU))
  have houter : outer ≤ monitorOuterLayerOrderMajorant U h :=
    monitorOuterLayerOrder_le_majorant bU.density bU.seedConstant hqo bU.outerDensity
      (hζM.mono (hMA.trans hAU))
      (fun r _ => (havoid r).mono hAU) (fun r _ => (horder r).trans hAU)
      (fun _ _ => hpaid.trans hAU) (hgeometry.trans hAU) hh1 bU.hingeOrder bU.outerCount bU.length (hqM.trans (hMA.trans hAU))
  have hθ : Magnitude (outerLayerTerminalMajorant U) θ :=
    outerLayerTerminal_magnitude bU.density bU.seedConstant hqo bU.outerDensity
      (fun r _ => (havoid r).mono hAU) bU.hingeOrder bU.outerCount
  have hratio : ⌈(reserve:ℝ)/θ⌉₊ ≤ U*outerLayerTerminalMajorant U := by
    apply Nat.ceil_le.mpr
    have hp := mul_le_mul (Nat.cast_le.mpr hreserve : (reserve:ℝ) ≤ U) hθ.inv_upper
      (div_nonneg (by norm_num) hθ.pos.le) (Nat.cast_nonneg U)
    simpa only [div_eq_mul_inv,one_div,Nat.cast_mul,one_mul] using hp
  change max (cleanHingeOrder αOriginal hOriginal) (max raw (max outer ⌈(reserve:ℝ)/θ⌉₊)) ≤ V
  exact max_le (bU.cleanOrder.trans hFinal.1)
    (max_le (hraw.trans hFinal.2.1)
      (max_le (houter.trans hFinal.2.2.1) (hratio.trans hFinal.2.2.2)))

#print axioms paperIIITriangleThreshold_le_naturalMajorant
end TypedTriangle.TowerBounds
