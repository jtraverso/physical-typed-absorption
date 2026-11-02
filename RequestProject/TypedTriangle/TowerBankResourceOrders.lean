module
public import RequestProject.TypedTriangle.TowerBankResources
public import RequestProject.TypedTriangle.TowerReferenceOrders
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.TowerBounds
open CorePaid.Explicit Vortex.Explicit BasalIncidence.Explicit

def samplingPrecisionMajorant (M : ℕ) : ℕ := max (M^2*4) (M*M^4*128)
def basalSamplingMajorant (M : ℕ) : ℕ := 96*samplingPrecisionMajorant M^4+1
def stockRateMajorant (M : ℕ) : ℕ := max (M*12) 2
def rawStockSamplingScale (M : ℕ) : ℕ := M+stockRateMajorant M+M*2+1
def rawStockOrderMajorant (M : ℕ) : ℕ :=
  max (referenceOrderBound (8*M)) (basalSamplingMajorant (rawStockSamplingScale M))
def resourceStockOrderScale (M : ℕ) : ℕ := M+resourceInputMajorant M+1
def resourceOrderMajorant (M : ℕ) : ℕ :=
  max (rawStockOrderMajorant (resourceStockOrderScale M))
    (max (withdrawalOrderMajorant (resourceInputScale M))
      (4*withdrawalInputMajorant (resourceInputScale M)))

theorem basalSampling_le_majorant {M : ℕ} {q β : ℝ}
    (hq : Magnitude M q) (hβ : Magnitude M β) :
    BasalSampling.Explicit.samplingCut q β ≤ basalSamplingMajorant M := by
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h128 : Magnitude 128 (128:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h96 : Magnitude 96 (96:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hδ := ((hq.pow 2).div h4).min ((hβ.mul (hq.pow 4)).div h128)
  exact Nat.add_le_add_right (h96.div (hδ.pow 4)).ceil_le 1

theorem stockRate_magnitude {M : ℕ} {ρ : ℝ} (hρ : Magnitude M ρ) :
    Magnitude (stockRateMajorant M) (stockRate ρ) := by
  have h12 : Magnitude 12 (12:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact (hρ.div h12).min (Magnitude.one.div h2)

theorem rawStockOrder_le_majorant {M : ℕ} {a b α ρ : ℝ}
    (ha : Magnitude M a) (hb : Magnitude M b) (hα : Magnitude M α) (hρ : Magnitude M ρ) :
    rawStockOrder a b α ρ ≤ rawStockOrderMajorant M := by
  have h8 : Magnitude 8 (8:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hα8 : Magnitude (8*M) (α/8) := by simpa only [Nat.mul_comm] using hα.div h8
  have hRef := referenceOrder_le_bound (ha.mono (by omega : M ≤ 8*M)) (hb.mono (by omega : M ≤ 8*M)) hα8
  let U := rawStockSamplingScale M
  have hr : Magnitude U (stockRate ρ) := (stockRate_magnitude hρ).mono
    (by dsimp [U,rawStockSamplingScale]; omega)
  have hα2 : Magnitude U (α/2) := (hα.div h2).mono (by dsimp [U,rawStockSamplingScale]; omega)
  exact max_le_max hRef (basalSampling_le_majorant hr hα2)

theorem resourceOrder_le_majorant {M h t : ℕ} {α C αW qW εW η ρcap τcap : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hαW : Magnitude M αW)
    (hq : Magnitude M qW) (hε : Magnitude M εW) (hη : Magnitude M η)
    (hρ : Magnitude M ρcap) (hτ : Magnitude M τcap) (ht : t ≤ M) :
    resourceOrder α C h αW qW εW η t ρcap τcap ≤ resourceOrderMajorant M := by
  let U := resourceInputScale M
  let W := resourceStockOrderScale M
  have hu : M ≤ U := by dsimp [U,resourceInputScale]; omega
  have hw : M ≤ W := by dsimp [W,resourceStockOrderScale]; omega
  have hτ' : Magnitude U (resourceOutputBudget qW η τcap) :=
    (resourceOutput_magnitude hq hη hτ).mono (by dsimp [U,resourceInputScale]; omega)
  have hδ := withdrawalInput_magnitude (hαW.mono hu) (hq.mono hu) (hε.mono hu) hτ' (ht.trans hu)
  have hInput : Magnitude W (resourceInputBudget αW qW εW η t ρcap τcap) :=
    (resourceInput_magnitude hαW hq hε hη hρ hτ ht).mono (by dsimp [W,resourceStockOrderScale]; omega)
  have hRaw := rawStockOrder_le_majorant (hC.inv.mono hw) (hC.mono hw) (hα.mono hw) hInput
  have hW := withdrawalOrder_le_majorant (hαW.mono hu) (hq.mono hu) (hε.mono hu) hτ' (ht.trans hu)
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact max_le_max hRaw (max_le_max hW (h4.div hδ).ceil_le)

#print axioms rawStockOrder_le_majorant
#print axioms resourceOrder_le_majorant
end TypedTriangle.TowerBounds
