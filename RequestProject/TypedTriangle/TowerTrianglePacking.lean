module
public import RequestProject.TypedTriangle.TowerPackingOrders
public import RequestProject.TypedTriangle.TowerBankLayerOrders
public import RequestProject.TypedTriangle.ExplicitTriangleMonitorPartition
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.TowerBounds
open Vortex.Explicit

def jointTrianglePackingOrderMajorant (M : ℕ) : ℕ := localizedSignedOrderBound (M+1)
def triangleStockInputMajorant (M : ℕ) : ℕ := M+packingCoverBudgetBound M*4+4+1
def triangleStockOrderMajorant (M : ℕ) : ℕ :=
  max (jointTrianglePackingOrderMajorant (triangleStockInputMajorant M))
    (max (packingCoverRateBound M) (2*packingCoverBudgetBound M))
def triangleFixedPackingOrderMajorant (M : ℕ) : ℕ := triangleStockOrderMajorant M
def monitorFixedPartitionOrderMajorant (M : ℕ) : ℕ :=
  max (triangleFixedPackingOrderMajorant (M+2)) 2
def triangleNativePartitionOrderMajorant (M : ℕ) : ℕ :=
  max (layerComplementOrderMajorant M)
    (max (monitorFixedPartitionOrderMajorant (nativePartitionInputMajorant M)) (max (16*M+1) 1))
def seedPointwisePlusTwoMajorant (M : ℕ) : ℕ :=
  (16*M+4)*referenceProviderBound (2*M)+2
def triangleComplementMajorant (M : ℕ) : ℕ :=
  max (layerComplementBudgetMajorant M) (max (referenceSeedBudgetBound M)
    (max M (M*seedPointwisePlusTwoMajorant M)))

theorem jointTrianglePackingOrder_le_majorant {M q : ℕ} {C α η τ L : ℝ}
    (hC : Magnitude M C) (hα : Magnitude M α) (hη : Magnitude M η)
    (hτ : Magnitude M τ) (hL : Magnitude M L) (hq : q ≤ M) :
    WeightedStar.Explicit.jointTrianglePackingOrder C α η τ L q ≤ jointTrianglePackingOrderMajorant M := by
  have hM : M ≤ M+1 := Nat.le_succ M
  exact localizedSignedOrder_le (hC.mono hM) (hα.mono hM) (hη.mono hM)
    (hτ.mono hM) (hL.add Magnitude.one) (hq.trans hM)

theorem triangleStockOrder_le_majorant {M h q : ℕ} {C α κ η τ L : ℝ}
    (hC : Magnitude M C) (hα : Magnitude M α) (hκ : Magnitude M κ)
    (hη : Magnitude M η) (hτ : Magnitude M τ) (hL : Magnitude M L) (hq : q ≤ M) :
    StockEntry.Explicit.triangleStockOrder C α κ η τ L h q ≤ triangleStockOrderMajorant M := by
  let S := triangleStockInputMajorant M
  have hM : M ≤ S := by dsimp only [S,triangleStockInputMajorant]; omega
  have h4 := Magnitude.natCast (by decide : 1 ≤ (4:ℕ)) (le_refl 4)
  have h2 := Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) (le_refl 2)
  have hbudget := packingCoverBudget_magnitude hκ hη
  have hprecision : Magnitude S
      (min (StockEntry.Explicit.coverDownBudget κ η/4) (min (1/4) η)) := by
    have hp := (hbudget.div h4).min ((Magnitude.one.div h4).min hη)
    exact hp.mono (by dsimp only [S,triangleStockInputMajorant]; omega)
  exact max_le_max
    (jointTrianglePackingOrder_le_majorant (hC.mono hM) (hα.mono hM) hprecision
      (hτ.mono hM) (hL.mono hM) (hq.trans hM))
    (max_le_max (packingCoverOrder_le hκ hη) (h2.div hbudget).ceil_le)

theorem triangleFixedPackingOrder_le_majorant {M h q : ℕ} {C α κ η τ Λ : ℝ}
    (hC : Magnitude M C) (hα : Magnitude M α) (hκ : Magnitude M κ)
    (hη : Magnitude M η) (hτ : Magnitude M τ) (hΛ : Magnitude M Λ) (hq : q ≤ M) :
    triangleFixedPackingOrder C α κ η τ Λ h q ≤ triangleFixedPackingOrderMajorant M :=
  triangleStockOrder_le_majorant hC hα hκ hη hτ hΛ hq

theorem monitorFixedPartitionOrder_le_majorant {M h q : ℕ} {C α κ η τ Λ : ℝ}
    (hC : Magnitude M C) (hα : Magnitude M α) (hκ : Magnitude M κ)
    (hη : Magnitude M η) (hτ : Magnitude M τ) (hΛ : Magnitude M Λ) (hq : q ≤ M) :
    monitorFixedPartitionOrder C α κ η τ Λ h q ≤ monitorFixedPartitionOrderMajorant M := by
  have hM : M ≤ M+2 := by omega
  exact max_le_max (triangleFixedPackingOrder_le_majorant (hC.mono hM) (hα.mono hM)
    (hκ.mono hM) (hη.mono hM) (hτ.mono hM) (hΛ.mono hM) (by omega : q+2 ≤ M+2)) le_rfl

theorem monitorNativePartitionOrder_le_majorant {M h q : ℕ} {C α κ η τ Λ : ℝ}
    (hC : Magnitude M C) (hα : Magnitude M α) (hκ : Magnitude M κ)
    (hη : Magnitude M η) (hτ : Magnitude M τ) (hΛ : Magnitude M Λ)
    (hh1 : 1 ≤ h) (hh : h ≤ M) (hq : q ≤ M) :
    monitorNativePartitionOrder C α h q κ η τ Λ ≤ triangleNativePartitionOrderMajorant M := by
  let S := nativePartitionInputMajorant M
  have hM : M ≤ S := by dsimp only [S,nativePartitionInputMajorant]; omega
  have h2 := Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) (le_refl 2)
  have hC2 : Magnitude S (2*C) := (h2.mul hC).mono
    (by dsimp only [S,nativePartitionInputMajorant]; omega)
  have hpaid : Magnitude S (paidGeometryDensity α h) :=
    (paidDensity_magnitude hα hh1 hh).mono
      (by dsimp only [S,nativePartitionInputMajorant]; omega)
  exact max_le_max (layerComplementOrder_le_majorant hC hα hh)
    (max_le_max (monitorFixedPartitionOrder_le_majorant (h := 2*h-3) hC2 hpaid
      (hκ.mono hM) (hη.mono hM) (hτ.mono hM) (hΛ.mono hM) (hq.trans hM))
      (max_le_max (packingSeedOrder_le hC) le_rfl))

theorem seedPointwisePlusTwo_magnitude {M h : ℕ} {α C : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hh : h ≤ M) :
    Magnitude (seedPointwisePlusTwoMajorant M) (ExplicitSeed.seedPointwiseCost α C h+2) := by
  have h16 := Magnitude.natCast (by decide : 1 ≤ (16:ℕ)) (le_refl 16)
  have h4 := Magnitude.natCast (by decide : 1 ≤ (4:ℕ)) (le_refl 4)
  have h2 := Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) (le_refl 2)
  have hM : M ≤ 2*M := by omega
  exact (((h16.mul hC).add h4).mul
    (referenceProvider_magnitude (hα.mono hM) (h2.mul hC) (hh.trans hM))).add h2

theorem monitorComplement_magnitude {M h : ℕ} {C α ζ : ℝ}
    (hC : Magnitude M C) (hα : Magnitude M α) (hζ : Magnitude M ζ) (hh : h ≤ M) :
    Magnitude (triangleComplementMajorant M) (monitorComplementBudget C α h ζ) :=
  (layerComplementBudget_magnitude hC hα hh).min
    ((referenceSeedBudget_magnitude hC.inv hC hα hh).min
      (hζ.min (hζ.div (seedPointwisePlusTwo_magnitude hα hC hh))))

#print axioms jointTrianglePackingOrder_le_majorant
#print axioms triangleStockOrder_le_majorant
#print axioms triangleFixedPackingOrder_le_majorant
#print axioms monitorFixedPartitionOrder_le_majorant
#print axioms monitorNativePartitionOrder_le_majorant
#print axioms seedPointwisePlusTwo_magnitude
#print axioms monitorComplement_magnitude
end TypedTriangle.TowerBounds
