module
public import RequestProject.TypedTriangle.TowerBankLayerOrders
public import RequestProject.TypedTriangle.TowerTrianglePacking
public import RequestProject.TypedTriangle.ExplicitTriangleMonitorConcreteOuterLayer
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.TowerBounds
open Vortex Vortex.Explicit

private theorem ceil_nat_scale_div_le {M U U' : ℕ} {β : ℝ}
    (hβ : Magnitude M β) (hU : U ≤ U') (k : ℕ) :
    ⌈(k:ℝ)*U/β⌉₊ ≤ k*U'*M := by
  have hUr : (U:ℝ) ≤ U' := Nat.cast_le.mpr hU
  have hn := mul_le_mul_of_nonneg_left hUr (Nat.cast_nonneg k)
  have hr : (k:ℝ)*U/β ≤ (k*U'*M:ℕ) := by
    calc (k:ℝ)*U/β = ((k:ℝ)*U)*(1/β) := by ring
      _ ≤ ((k:ℝ)*U')*M := mul_le_mul hn hβ.inv_upper
        (one_div_nonneg.mpr hβ.pos.le) (mul_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg U'))
      _ = (k*U'*M:ℕ) := by push_cast; rfl
  exact Nat.ceil_le.mpr hr


private theorem square_scale_le (n k : ℕ) (hk : k ≤ 64) : k*n*n ≤ 64*n^2 := by
  calc k*n*n = k*n^2 := by ring
    _ ≤ 64*n^2 := Nat.mul_le_mul_right _ hk

private theorem same_min {M : ℕ} {x y : ℝ} (hx : Magnitude M x) (hy : Magnitude M y) :
    Magnitude M (min x y) := by simpa only [max_self] using hx.min hy

private theorem eta_majorant_mono (M : ℕ) {B C : ℕ} (hB : B ≤ C) : bankEtaBound M B ≤ bankEtaBound M C := by
  unfold bankEtaBound
  gcongr

private theorem cap_majorant_mono (M : ℕ) {B C : ℕ} (hB : B ≤ C) : monitorCapBound M B ≤ monitorCapBound M C := by
  unfold monitorCapBound
  gcongr

/-- One finite natural growth step also pays the statistical packing order. -/
def triangleBankStep (M h : ℕ) : ℕ :=
  bankStep M h + triangleNativePartitionOrderMajorant M + 1

private structure TriangleBankStepBounds (M h B : ℕ) : Prop where
  grows : M ≤ B
  positive : 1 ≤ B
  successor : M+1 ≤ B
  scalar : 128*M ≤ B
  square : 64*M^2 ≤ B
  cube : 4*M^3 ≤ B
  count : (M+2)*M ≤ B
  dimension : catalogDimensionMajorant M ≤ B
  coefficient : catalogCoefficientMajorant M ≤ B
  column : catalogColumnMajorant M ≤ B
  radius : bankRadiusMajorant M ≤ B
  catalogue : bankCatalogSizeMajorant M ≤ B
  cell : bankCellSizeMajorant M h ≤ B
  protection : bankProtectionBound M h ≤ B
  core : coreDeltaBound M h ≤ B
  geometry : deletionBudgetMajorant M ≤ B
  deletion : nativeDeleteMajorant M ≤ B
  monitors : natEnvelope 20 M ≤ B
  copies : 2*natEnvelope 4 M ≤ B
  tolerance : bankToleranceBound M h ≤ B
  rate : preparedBankRateMajorant M h M ≤ B
  weights : physicalWeightMajorant M ≤ B
  eta : bankEtaBound M M ≤ B
  cap : monitorCapBound M M ≤ B
  input : resourceInputMajorant M ≤ B
  output : resourceOutputMajorant M ≤ B
  completion : resourceCompletionMajorant M ≤ B
  stockOrder : stockBankOrderMajorant M h ≤ B
  nativeOrder : triangleNativePartitionOrderMajorant M ≤ B
  weightOrder : nativeWeightOrderMajorant M ≤ B
  bankOrder : bankOrderBound M ≤ B

private theorem triangleBankStep_bounds (M h : ℕ) : TriangleBankStepBounds M h (triangleBankStep M h) := by
  constructor <;> unfold triangleBankStep bankStep <;> omega

def triangleBankStage (h : ℕ) : ℕ → ℕ → ℕ
  | 0,M => M
  | k+1,M => triangleBankStep (triangleBankStage h k M) h

def monitorLayerThresholdMajorant (M h : ℕ) : ℕ := triangleBankStage h 16 M

theorem triangleBankStage_mono_count (h M : ℕ) : Monotone (fun k => triangleBankStage h k M) :=
  monotone_nat_of_le_succ (fun k => (triangleBankStep_bounds (triangleBankStage h k M) h).grows)

theorem monitorLayerThreshold_le_majorant {M h t nRef qStat : ℕ} {α C β γRef q αPool εRoute ζStat : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hβ : Magnitude M β)
    (hγRef : Magnitude M γRef) (hq : Magnitude M q) (hPool : Magnitude M αPool)
    (hRoute : Magnitude M εRoute) (hζ : Magnitude M ζStat) (hh1 : 1 ≤ h) (hh : h ≤ M) (ht : t ≤ M) (hnRef : nRef ≤ M) (hqStat : qStat ≤ M) :
    monitorLayerThreshold α C β γRef q αPool εRoute ζStat h t nRef qStat ≤ monitorLayerThresholdMajorant M h := by
  let S := fun k => triangleBankStage h k M
  have hb (k : ℕ) : TriangleBankStepBounds (S k) h (S (k+1)) := triangleBankStep_bounds (S k) h
  have hs {i j : ℕ} (hij : i ≤ j) : S i ≤ S j := triangleBankStage_mono_count h M hij
  have h0 {j : ℕ} : M ≤ S j := hs (Nat.zero_le j)
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h64 : Magnitude 64 (64:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h128 : Magnitude 128 (128:ℝ) := Magnitude.natCast (by decide) le_rfl
  have htimes (k n : ℕ) (hn : n ≤ 128) : S k*n ≤ S (k+1) := by
    calc S k*n ≤ S k*128 := Nat.mul_le_mul_left _ hn
      _ = 128*S k := Nat.mul_comm _ _
      _ ≤ _ := (hb k).scalar
  let d := CatalogNative.Explicit.catalogDimension β h
  let c := CatalogNative.Explicit.catalogCoefficient β h
  let E := CatalogNative.Explicit.catalogColumn β h
  let Rc := CatalogNative.Explicit.bankCatalogRadius α β h
  let L := CatalogNative.Explicit.bankCatalogSize α β h
  let Ecell := CatalogNative.Explicit.bankCellSize α β h
  have hd : d ≤ S 1 := (catalogDimension_le_majorant hβ hh).trans (hb 0).dimension
  have hc : c ≤ S 1 := (catalogCoefficient_le_majorant hβ hh).trans (hb 0).coefficient
  have hE : E ≤ S 1 := (catalogColumn_le_majorant hβ hh).trans (hb 0).column
  have hCat := bankCatalog_bounds hα hβ hh
  have hRc : Rc ≤ S 1 := hCat.1.trans (hb 0).radius
  have hL : L ≤ S 1 := hCat.2.1.trans (hb 0).catalogue
  have hCell : Ecell ≤ S 1 := (bankCellSize_le_majorant hα hβ hh).trans (hb 0).cell
  have hRm : S07V44.monR Rc E ≤ S 1 := max_le (hb 0).positive (max_le hRc hE)
  have hm := monitor_envelope_bounds (hd.trans (le_natEnvelope 0 (S 1))) (hRm.trans (le_natEnvelope 0 (S 1)))
  let AM := S07V34.Explicit.paymentCost d (S07V44.monR Rc E)
  let MM := S07V34.Explicit.monitorMagnitude d (S07V44.monR Rc E)
  let KM := S07V34.Explicit.monitorDimension d (S07V44.monR Rc E)
  have hAM : AM ≤ S 2 := (envelope_lift hm.2.2.2.2.2.2.2 (by decide : 16 ≤ 20)).trans (hb 1).monitors
  have hMM : MM ≤ S 2 := (envelope_lift hm.2.2.2.1 (by decide : 9 ≤ 20)).trans (hb 1).monitors
  have hKM : KM ≤ S 2 := (envelope_lift hm.2.2.1 (by decide : 7 ≤ 20)).trans (hb 1).monitors
  let P := 2*S07V46.gammaL AM MM L
  have hP : P ≤ S 3 := (Nat.mul_le_mul_left 2 (gammaL_le_envelope
    (hAM.trans (le_natEnvelope 0 (S 2))) (hMM.trans (le_natEnvelope 0 (S 2)))
    ((hL.trans (hs (by decide : 1 ≤ 2))).trans (le_natEnvelope 0 (S 2))))).trans (hb 2).copies
  have hγ : Magnitude (S 1) (min γRef 1) := (clipped_magnitude hγRef).mono (hb 0).successor
  have hγ4 : Magnitude (S 2) (min γRef 1/4) := (hγ.div h4).mono (htimes 1 4 (by decide))
  have hq2 : Magnitude (S 1) (q/2) := (hq.div h2).mono (by
    exact (by omega : M*2 ≤ 128*M).trans (hb 0).scalar)
  have hβ2 : Magnitude (S 1) (β/2) := (hβ.div h2).mono (by
    exact (by omega : M*2 ≤ 128*M).trans (hb 0).scalar)
  have hα2 : Magnitude (S 1) (α/2) := (hα.div h2).mono (by
    exact (by omega : M*2 ≤ 128*M).trans (hb 0).scalar)
  let δcap := min (ExplicitGeometry.deletionBudget β h) (min (S07V42.coreDelta β h) (S07V37.delOf (β/2) h))
  have hδGeom : Magnitude (S 1) (ExplicitGeometry.deletionBudget β h) :=
    (deletionBudget_magnitude hβ hh).mono (hb 0).geometry
  have hδCore : Magnitude (S 1) (S07V42.coreDelta β h) := (coreDelta_magnitude hβ h).mono (hb 0).core
  have hδDel : Magnitude (S 2) (S07V37.delOf (β/2) h) :=
    (nativeDelete_magnitude hβ2 (hh.trans h0)).mono (hb 1).deletion
  have hδ : Magnitude (S 2) δcap := same_min (hδGeom.mono (hs (by decide : 1 ≤ 2)))
    (same_min (hδCore.mono (hs (by decide : 1 ≤ 2))) hδDel)
  let κBank := preparedBankRoundRate α β (min γRef 1/4) δcap h P
  let εBank := CatalogNative.Explicit.bankTolerance α β (min γRef 1/4) h
  have hκ : Magnitude (S 4) κBank :=
    ((preparedBankRate_magnitude (hα.mono h0) (hβ.mono h0) (hγ4.mono (hs (by decide : 2 ≤ 3)))
      (hδ.mono (hs (by decide : 2 ≤ 3))) (hh.trans h0) P).mono
      (preparedBankRateMajorant_mono_P (S 3) h hP)).mono (hb 3).rate
  have hεBank : Magnitude (S 3) εBank :=
    (bankTolerance_magnitude (hα.mono h0) (hβ.mono h0) hγ4 h).mono (hb 2).tolerance
  let Λ := CatalogNative.Explicit.physicalWeightMagnitude (α/2) (β/2) h d c MM
  have hΛ : Magnitude (S 3) Λ := (physicalWeight_magnitude (hα2.mono (hs (by decide : 1 ≤ 2)))
    (hβ2.mono (hs (by decide : 1 ≤ 2))) (hh.trans h0) (hd.trans (hs (by decide : 1 ≤ 2)))
    (hc.trans (hs (by decide : 1 ≤ 2))) hMM).mono (hb 2).weights
  let Bstatic := 2*Ecell*(2*L*P)
  have hB : Bstatic ≤ S 4 := by
    have hprod : Bstatic ≤ 2*S 3*(2*S 3*S 3) := Nat.mul_le_mul
      (Nat.mul_le_mul_left 2 (hCell.trans (hs (by decide : 1 ≤ 3))))
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (hL.trans (hs (by decide : 1 ≤ 3)))) hP)
    exact (hprod.trans_eq (by ring)).trans (hb 3).cube
  let ηPay := StockEntry.Explicit.bankEta κBank (q/2) εBank Bstatic
  have hηPay : Magnitude (S 5) ηPay := ((bankEta_magnitude hκ (hq2.mono (hs (by decide : 1 ≤ 4)))
    (hεBank.mono (hs (by decide : 3 ≤ 4))) Bstatic).mono (eta_majorant_mono (S 4) hB)).mono (hb 4).eta
  let δ := StockEntry.Explicit.monitorCap Λ ηPay KM
  have hδMoment : Magnitude (S 6) δ := ((monitorCap_magnitude (hΛ.mono (hs (by decide : 3 ≤ 5))) hηPay KM).mono
    (cap_majorant_mono (S 5) (hKM.trans (hs (by decide : 2 ≤ 5))))).mono (hb 5).cap
  let εPack := min (δ/2) ζStat
  have hPack : Magnitude (S 7) εPack := same_min
    ((hδMoment.div h2).mono (htimes 6 2 (by decide))) (hζ.mono h0)
  have hq128 : Magnitude (S 1) (q/128) := (hq.div h128).mono (by
    change M*128 ≤ S 1
    simpa only [Nat.mul_comm] using (show 128*M ≤ S 1 from (hb 0).scalar))
  have hq64 : Magnitude (S 1) (q/64) := (hq.div h64).mono (by
    exact (by omega : M*64 ≤ 128*M).trans (hb 0).scalar)
  have hγq : Magnitude (S 2) (min γRef 1*q/64) := ((hγ.mul (hq.mono (h0 : M ≤ S 1))).div h64).mono (by
    simpa only [Nat.pow_two,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using (hb 1).square)
  let ρcap := min εPack (min (q/128) (min γRef 1*q/64))
  let τcap := min εPack (min (q/64) (min γRef 1*q/64))
  have hρcap : Magnitude (S 7) ρcap := same_min hPack (same_min (hq128.mono (hs (by decide : 1 ≤ 7))) (hγq.mono (hs (by decide : 2 ≤ 7))))
  have hτcap : Magnitude (S 7) τcap := same_min hPack (same_min (hq64.mono (hs (by decide : 1 ≤ 7))) (hγq.mono (hs (by decide : 2 ≤ 7))))
  have hBank : Magnitude (S 1) (CatalogNative.Explicit.bankProtectionBudget α β h) := (bankProtection_magnitude hα hβ h).mono (hb 0).protection
  have hηBank : Magnitude (S 2) (CatalogNative.Explicit.bankProtectionBudget α β h/2) := (hBank.div h2).mono (htimes 1 2 (by decide))
  let ρ := resourceInputBudget αPool (q/2) εRoute (CatalogNative.Explicit.bankProtectionBudget α β h/2) t ρcap τcap
  let κStock := BasalIncidence.Explicit.rawStockCompletion α ρ
  have hκStock : Magnitude (S 8) κStock := (resourceCompletion_magnitude (hα.mono h0) (hPool.mono h0)
    (hq2.mono (hs (by decide : 1 ≤ 7))) (hRoute.mono h0) (hηBank.mono (hs (by decide : 2 ≤ 7)))
    hρcap hτcap (ht.trans h0)).mono (hb 7).completion
  have hNative := monitorNativePartitionOrder_le_majorant (hC.mono (h0 : M ≤ S 8)) (hα.mono h0) hκStock
    (hPack.mono (hs (by decide : 7 ≤ 8))) (hPack.mono (hs (by decide : 7 ≤ 8)))
    (hΛ.mono (hs (by decide : 3 ≤ 8))) hh1 (hh.trans h0) (hqStat.trans h0)
  have hResource := stockBankOrder_le_majorant (hα.mono (h0 : M ≤ S 7)) (hC.mono h0) (hβ.mono h0)
    (hγ4.mono (hs (by decide : 2 ≤ 7))) (hδ.mono (hs (by decide : 2 ≤ 7)))
    (hPool.mono h0) (hq2.mono (hs (by decide : 1 ≤ 7))) (hRoute.mono h0) hρcap hτcap
    (hh.trans h0) (hP.trans (hs (by decide : 3 ≤ 7))) (ht.trans h0)
  have hWeights := nativeWeightOrder_le_majorant (hα.mono (h0 : M ≤ S 1)) (hβ.mono h0) hq2 (hh.trans h0)
  have hBankOrder := bankOrder_le hκ (hq2.mono (hs (by decide : 1 ≤ 4)))
  have hCount : (L+2)*KM ≤ S 3 := (Nat.mul_le_mul (Nat.add_le_add_right (hL.trans (hs (by decide : 1 ≤ 2))) 2) hKM).trans (hb 2).count
  have hceilRef : ⌈2*(nRef:ℝ)/q⌉₊ ≤ 2*M*M := by
    simpa only [Nat.cast_ofNat] using ceil_nat_scale_div_le hq hnRef 2
  have hr : ⌈2*(nRef:ℝ)/q⌉₊ ≤ S 1 := hceilRef.trans
    ((square_scale_le M 2 (by decide)).trans (hb 0).square)
  have hgq : ⌈4/(min γRef 1*q)⌉₊ ≤ S 2 := by
    have he := (h4.div (hγ.mul (hq.mono (h0 : M ≤ S 1)))).ceil_le
    have hsquare : 4*(S 1*S 1) ≤ 64*(S 1)^2 := by
      simpa only [Nat.mul_assoc] using square_scale_le (S 1) 4 (by decide)
    exact he.trans (hsquare.trans (hb 1).square)
  change max _ (max _ (max _ (max _ (max _ (max _ _))))) ≤ S 16
  exact max_le (hResource.trans ((hb 7).stockOrder.trans (hs (by decide : 8 ≤ 16))))
    (max_le (hNative.trans ((hb 8).nativeOrder.trans (hs (by decide : 9 ≤ 16))))
      (max_le (hWeights.trans ((hb 1).weightOrder.trans (hs (by decide : 2 ≤ 16))))
        (max_le (hBankOrder.trans ((hb 4).bankOrder.trans (hs (by decide : 5 ≤ 16))))
          (max_le (hCount.trans (hs (by decide : 3 ≤ 16)))
            (max_le (hr.trans (hs (by decide : 1 ≤ 16))) (hgq.trans (hs (by decide : 2 ≤ 16))))))))


def monitorCleanLayerThresholdMajorant (M h : ℕ) : ℕ :=
  max (monitorLayerThresholdMajorant (3*M+1) h) (2*max 1 M*M)
def monitorOuterLayerOrderMajorant (M h : ℕ) : ℕ :=
  max 1 (max (monitorCleanLayerThresholdMajorant (outerLayerParameterScale M) h) (2*M))

theorem monitorCleanLayerThreshold_le_majorant {M h t nRef nPaid nGeometry qStat : ℕ} {α C β γ q αPool εRoute ζStat : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hβ : Magnitude M β)
    (hγ : Magnitude M γ) (hq : Magnitude M q) (hPool : Magnitude M αPool)
    (hRoute : Magnitude M εRoute) (hζ : Magnitude M ζStat) (hh1 : 1 ≤ h) (hh : h ≤ M) (ht : t ≤ M)
    (hnRef : nRef ≤ M) (hnPaid : nPaid ≤ M) (hnGeometry : nGeometry ≤ M) (hqStat : qStat ≤ M) :
    monitorCleanLayerThreshold α C β γ q αPool εRoute ζStat h t nRef nPaid nGeometry qStat ≤ monitorCleanLayerThresholdMajorant M h := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  let U := 3*M+1
  have hu : M ≤ U := by dsimp [U]; omega
  have h2C : Magnitude U (2*C) := (h2.mul hC).mono (by dsimp [U]; omega)
  have hL := monitorLayerThreshold_le_majorant (hα.mono hu) h2C (hβ.mono hu) (hγ.mono hu)
    (hq.mono hu) (hPool.mono hu) (hRoute.mono hu) (hζ.mono hu) hh1 (hh.trans hu) (ht.trans hu) (hnRef.trans hu) (hqStat.trans hu)
  have hk : max 1 (max nPaid nGeometry) ≤ max 1 M := max_le_max_left 1 (max_le hnPaid hnGeometry)
  have hKNat : Magnitude (max 1 M) ((max 1 (max nPaid nGeometry):ℕ):ℝ) :=
    Magnitude.natCast (le_max_left _ _) hk
  exact max_le_max hL ((h2.mul hKNat).div hq).ceil_le

private theorem monitor_clean_window_run_bound {M h m nRef nPaid nGeometry qStat : ℕ} {α C γ q a ζStat : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hγ : Magnitude M γ) (hq : Magnitude M q)
    (ha : Magnitude (2*M) a) (hζ : Magnitude M ζStat) (hh1 : 1 ≤ h) (hh : h ≤ M) (hm : m ≤ M)
    (hnRef : nRef ≤ M) (hnPaid : nPaid ≤ M) (hnGeometry : nGeometry ≤ M) (hqStat : qStat ≤ M) :
    monitorCleanLayerThreshold (α/16) C (α/32) γ q (α/4) (windowRouteRate a q m/4) ζStat
      h (m+1) nRef nPaid nGeometry qStat ≤ monitorCleanLayerThresholdMajorant (outerLayerParameterScale M) h := by
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h16 : Magnitude 16 (16:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h32 : Magnitude 32 (32:ℝ) := Magnitude.natCast (by decide) le_rfl
  let U := outerLayerParameterScale M
  have hu : M ≤ U := by dsimp [U,outerLayerParameterScale]; omega
  have hRoute := (windowRoute_magnitude ha (hq.mono (by omega : M ≤ 2*M)) (by omega : m ≤ 2*M)).div h4
  exact monitorCleanLayerThreshold_le_majorant
    ((hα.div h16).mono (by dsimp [U,outerLayerParameterScale]; omega)) (hC.mono hu)
    ((hα.div h32).mono (by dsimp [U,outerLayerParameterScale]; omega)) (hγ.mono hu) (hq.mono hu)
    ((hα.div h4).mono (by dsimp [U,outerLayerParameterScale]; omega))
    (hRoute.mono (by dsimp [U,outerLayerParameterScale]; omega)) (hζ.mono hu) hh1 (hh.trans hu)
    (by dsimp [U,outerLayerParameterScale]; omega) (hnRef.trans hu) (hnPaid.trans hu) (hnGeometry.trans hu) (hqStat.trans hu)

theorem monitorOuterLayerOrder_le_majorant {M h m L nGeometry qStat : ℕ} {α C q a ζStat : ℝ}
    {γRef : ℕ → ℝ} {nRef nPaid : ℕ → ℕ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hq : Magnitude M q) (ha : Magnitude M a) (hζ : Magnitude M ζStat)
    (hγ : ∀ j ≤ L, Magnitude M (γRef j)) (hnRef : ∀ j ≤ L, nRef j ≤ M)
    (hnPaid : ∀ j ≤ L, nPaid j ≤ M) (hnGeometry : nGeometry ≤ M)
    (hh1 : 1 ≤ h) (hh : h ≤ M) (hm : m ≤ M) (_hL : L ≤ M) (hqStat : qStat ≤ M) :
    monitorOuterLayerOrder α C q a ζStat h m L qStat γRef nRef nPaid nGeometry ≤ monitorOuterLayerOrderMajorant M h := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have ha2 : Magnitude (2*M) (a/2) := by simpa only [Nat.mul_comm] using ha.div h2
  apply max_le_max le_rfl
  apply max_le_max
  · apply Finset.sup_le
    intro j _
    exact monitor_clean_window_run_bound hα hC (hγ j (Nat.le_of_lt_succ j.isLt)) hq ha2 hζ hh1 hh hm
      (hnRef j (Nat.le_of_lt_succ j.isLt)) (hnPaid j (Nat.le_of_lt_succ j.isLt)) hnGeometry hqStat
  · exact (h2.div hq).ceil_le


#print axioms triangleBankStage_mono_count
#print axioms monitorLayerThreshold_le_majorant
#print axioms monitorCleanLayerThreshold_le_majorant
#print axioms monitorOuterLayerOrder_le_majorant
end TypedTriangle.TowerBounds
