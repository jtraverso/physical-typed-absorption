module
public import RequestProject.TypedTriangle.TowerReferenceBudgets
public import RequestProject.TypedTriangle.TowerAnalyticClone
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TypedTriangle.TowerBounds
open RawReference.Explicit

def referenceOrderInput (M : ℕ) : ℕ := 1+referenceWeightBound M+referencePrecisionBound M
def referenceOrderBound (M : ℕ) : ℕ :=
  max (max (16*M+1) (approxPackingBound (referenceOrderInput M))) 1
def prescribedOrderBound (M : ℕ) : ℕ :=
  max (envelopeOrderBound M) (max (referenceOrderBound M)
    (2*envelopeDegreeBound M*referenceStockBudgetBound M))

theorem seedOrder_le_bound {M : ℕ} {b : ℝ} (hb : Magnitude M b) :
    seedOrder b ≤ 16*M+1 := by
  have h16 : Magnitude 16 (16:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact Nat.add_le_add_right (h16.mul hb).ceil_le 1

theorem referenceOrder_le_bound {M : ℕ} {a b η : ℝ}
    (ha : Magnitude M a) (hb : Magnitude M b) (hη : Magnitude M η) :
    referenceOrder a b η ≤ referenceOrderBound M := by
  let U := referenceOrderInput M
  have hU1 : 1 ≤ U := by dsimp [U,referenceOrderInput]; omega
  have hw := (referenceWeightUpper_magnitude ha hb).upper
  have hp := referencePackingPrecision_magnitude hη
  have hwU : referenceWeightUpper a b ≤ (U:ℝ) :=
    hw.trans (by exact_mod_cast (by dsimp [U,referenceOrderInput]; omega : referenceWeightBound M ≤ U))
  have hiU : (referencePackingPrecision η)⁻¹ ≤ (U:ℝ) := by
    have hu : (referencePrecisionBound M:ℝ) ≤ U := by
      exact_mod_cast (by dsimp [U,referenceOrderInput]; omega : referencePrecisionBound M ≤ U)
    simpa only [one_div] using hp.inv_upper.trans hu
  exact max_le_max (max_le_max (seedOrder_le_bound hb)
    (approxPackingCut_le hU1 hwU hp.pos hiU)) le_rfl

theorem prescribedOrder_le_bound {M h : ℕ} {a b α η : ℝ}
    (ha : Magnitude M a) (hb : Magnitude M b) (hα : Magnitude M α)
    (hη : Magnitude M η) (hh : h ≤ M) :
    prescribedOrder a b α h η ≤ prescribedOrderBound M := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hd : Magnitude (envelopeDegreeBound M) (Envelope.Explicit.envelopeDegree α:ℝ) :=
    Magnitude.natCast (Envelope.Explicit.envelopeDegree_pos α) (envelopeDegree_le_bound hα)
  have hs := referenceStockBudget_magnitude ha hb hα hh
  exact max_le_max (envelopeOrder_le_bound hα)
    (max_le_max (referenceOrder_le_bound ha hb hη) ((h2.mul hd).div hs).ceil_le)

#print axioms referenceOrder_le_bound
#print axioms prescribedOrder_le_bound
end TypedTriangle.TowerBounds
