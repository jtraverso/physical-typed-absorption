module
public import RequestProject.TypedTriangle.TowerAnalyticClone
public import RequestProject.TypedTriangle.TowerReferenceBudgets
public import RequestProject.TypedTriangle.ExplicitMonitoredPackingCore
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.TowerBounds

def monitoredPackingOrderBound (M : ℕ) : ℕ := max 2 (cloneBound (3*M+2))
def packingSignedScale (M : ℕ) : ℕ := max M (max (M*3) (max (M*(5*M)) (M+1)))
def signedEnvelopeOrderBound (M : ℕ) : ℕ := max 2 (monitoredPackingOrderBound (packingSignedScale M))
def packingLocalizedScale (M : ℕ) : ℕ := max M (max (M*6) (max (6*M) (9*M)))
def localizedSignedOrderBound (M : ℕ) : ℕ := signedEnvelopeOrderBound (packingLocalizedScale M)
def packingPhysicalScale (M : ℕ) : ℕ := max M (max (2*M) (M*2))
def physicalMomentOrderBound (M : ℕ) : ℕ :=
  max (16*M+1) (localizedSignedOrderBound (packingPhysicalScale M))
def physicalMomentBudgetBound (M : ℕ) : ℕ := max (referenceSeedBudgetBound M) (M*4)
def packingCoverRateBound (M : ℕ) : ℕ := max (M*64) (max (M*64) 64)
def packingCoverBudgetBound (M : ℕ) : ℕ := (packingCoverRateBound M)^2
def packingStockScale (M : ℕ) : ℕ := max M (max (packingCoverBudgetBound M*4) 4)
def stockMomentOrderBound (M : ℕ) : ℕ :=
  max (physicalMomentOrderBound (packingStockScale M))
    (max (packingCoverRateBound M) (2*packingCoverBudgetBound M))
def fixedPackingOrderBound (M : ℕ) : ℕ := stockMomentOrderBound M

theorem monitoredPackingOrder_le {M q : ℕ} {C α c η : ℝ}
    (hC : Magnitude M C) (hα : Magnitude M α)
    (hc : Magnitude M c) (hη : Magnitude M η) (hq : q ≤ M) :
    WeightedStar.Explicit.monitoredPackingOrder C α c η q ≤ monitoredPackingOrderBound M := by
  have h2 : Magnitude 2 (2 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hM : M ≤ 3*M+2 := by omega
  have hmass : Magnitude (3*M+2) (min c (α/2)) :=
    (hc.min (hα.div h2)).mono (by omega)
  have hC' := hC.mono hM
  have hη' := hη.mono hM
  have hcut := nativePackingCut_le (M := 3*M+2) (by omega) hC'.pos.le hmass.pos hη'.pos
    hC'.upper (by simpa only [one_div] using hmass.inv_upper)
    (by simpa only [one_div] using hη'.inv_upper) (by omega : q+2 ≤ 3*M+2)
  exact max_le_max_left 2 hcut

theorem signedEnvelopeOrder_le {M q : ℕ} {C α c η τ B : ℝ}
    (hC : Magnitude M C) (hα : Magnitude M α) (hc : Magnitude M c)
    (hη : Magnitude M η) (hτ : Magnitude M τ) (hB : Magnitude M B) (hq : q ≤ M) :
    WeightedStar.Explicit.signedEnvelopeOrder C α c η τ B q ≤ signedEnvelopeOrderBound M := by
  let S := packingSignedScale M
  have h0 : M ≤ S := by dsimp only [S, packingSignedScale]; omega
  have h1 : M*3 ≤ S := by dsimp only [S, packingSignedScale]; omega
  have h2 : max M (M*(5*M)) ≤ S := by dsimp only [S, packingSignedScale]; omega
  have hq' : q+1 ≤ S := by dsimp only [S, packingSignedScale]; omega
  have hThree : Magnitude 3 (3 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hFive : Magnitude 5 (5 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hmass := (hc.div hThree).mono h1
  have hprecision := (hη.min (hτ.div (hFive.mul hB))).mono h2
  have horder := monitoredPackingOrder_le (hC.mono h0) (hα.mono h0) hmass hprecision hq'
  exact max_le_max_left 2 horder

theorem localizedSignedOrder_le {M q : ℕ} {C α η τ L : ℝ}
    (hC : Magnitude M C) (hα : Magnitude M α) (hη : Magnitude M η)
    (hτ : Magnitude M τ) (hL : Magnitude M L) (hq : q ≤ M) :
    WeightedStar.Explicit.localizedSignedOrder C α η τ L q ≤ localizedSignedOrderBound M := by
  let S := packingLocalizedScale M
  have h0 : M ≤ S := by dsimp only [S, packingLocalizedScale]; omega
  have h1 : M*6 ≤ S := by dsimp only [S, packingLocalizedScale]; omega
  have h2 : 6*M ≤ S := by dsimp only [S, packingLocalizedScale]; omega
  have h3 : 9*M ≤ S := by dsimp only [S, packingLocalizedScale]; omega
  have hSix : Magnitude 6 (6 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hNine : Magnitude 9 (9 : ℝ) := Magnitude.natCast (by decide) le_rfl
  exact signedEnvelopeOrder_le (hC.mono h0) (hα.mono h0) ((hα.div hSix).mono h1)
    (hη.mono h0) ((hSix.mul hτ).mono h2) ((hNine.mul hL).mono h3) (hq.trans h0)

theorem packingSeedOrder_le {M : ℕ} {C : ℝ} (hC : Magnitude M C) :
    RawReference.Explicit.seedOrder C ≤ 16*M+1 := by
  have h16 : Magnitude 16 (16 : ℝ) := Magnitude.natCast (by decide) le_rfl
  exact Nat.add_le_add_right (h16.mul hC).ceil_le 1

theorem physicalMomentOrder_le {M h q : ℕ} {C α η τ L : ℝ}
    (hC : Magnitude M C) (hα : Magnitude M α) (hη : Magnitude M η)
    (hτ : Magnitude M τ) (hL : Magnitude M L) (hq : q ≤ M) :
    ProtectedNibble.Explicit.physicalMomentOrder C α η τ L h q ≤ physicalMomentOrderBound M := by
  let S := packingPhysicalScale M
  have h0 : M ≤ S := by dsimp only [S, packingPhysicalScale]; omega
  have h1 : 2*M ≤ S := by dsimp only [S, packingPhysicalScale]; omega
  have h2' : M*2 ≤ S := by dsimp only [S, packingPhysicalScale]; omega
  have hTwo : Magnitude 2 (2 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have horder := localizedSignedOrder_le ((hTwo.mul hC).mono h1) ((hα.div hTwo).mono h2')
    (hη.mono h0) (hτ.mono h0) (hL.mono h0) (hq.trans h0)
  exact max_le_max (packingSeedOrder_le hC) horder

theorem physicalMomentBudget_magnitude {M h : ℕ} {C α : ℝ}
    (hC : Magnitude M C) (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (physicalMomentBudgetBound M) (ProtectedNibble.Explicit.physicalMomentBudget C α h) := by
  have h4 : Magnitude 4 (4 : ℝ) := Magnitude.natCast (by decide) le_rfl
  exact (referenceSeedBudget_magnitude hC.inv hC hα hh).min (hα.div h4)

theorem packingCoverRate_magnitude {M : ℕ} {κ η : ℝ}
    (hκ : Magnitude M κ) (hη : Magnitude M η) :
    Magnitude (packingCoverRateBound M) (StockEntry.Explicit.coverDownRate κ η) := by
  have h64 : Magnitude 64 (64 : ℝ) := Magnitude.natCast (by decide) le_rfl
  simpa only [packingCoverRateBound, StockEntry.Explicit.coverDownRate, Nat.one_mul] using
    (hκ.div h64).min ((hη.div h64).min (Magnitude.one.div h64))

theorem packingCoverBudget_magnitude {M : ℕ} {κ η : ℝ}
    (hκ : Magnitude M κ) (hη : Magnitude M η) :
    Magnitude (packingCoverBudgetBound M) (StockEntry.Explicit.coverDownBudget κ η) :=
  (packingCoverRate_magnitude hκ hη).pow 2

theorem packingCoverOrder_le {M : ℕ} {κ η : ℝ}
    (hκ : Magnitude M κ) (hη : Magnitude M η) :
    StockEntry.Explicit.coverDownOrder κ η ≤ packingCoverRateBound M :=
  (packingCoverRate_magnitude hκ hη).inv.ceil_le

theorem stockMomentOrder_le {M h q : ℕ} {C α κ η τ L : ℝ}
    (hC : Magnitude M C) (hα : Magnitude M α) (hκ : Magnitude M κ)
    (hη : Magnitude M η) (hτ : Magnitude M τ) (hL : Magnitude M L) (hq : q ≤ M) :
    StockEntry.Explicit.stockMomentOrder C α κ η τ L h q ≤ stockMomentOrderBound M := by
  let S := packingStockScale M
  have h0 : M ≤ S := by dsimp only [S, packingStockScale]; omega
  have h1 : max (packingCoverBudgetBound M*4) 4 ≤ S := by
    dsimp only [S, packingStockScale]; omega
  have hFour : Magnitude 4 (4 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hTwo : Magnitude 2 (2 : ℝ) := Magnitude.natCast (by decide) le_rfl
  have hbudget := packingCoverBudget_magnitude hκ hη
  have hprecision : Magnitude S (min (StockEntry.Explicit.coverDownBudget κ η/4) (1/4)) := by
    have hh := (hbudget.div hFour).min (Magnitude.one.div hFour)
    simpa only [Nat.one_mul] using hh.mono h1
  have horder := physicalMomentOrder_le (h := h) (hC.mono h0) (hα.mono h0) hprecision
    (hτ.mono h0) (hL.mono h0) (hq.trans h0)
  exact max_le_max horder (max_le_max (packingCoverOrder_le hκ hη) (hTwo.div hbudget).ceil_le)

theorem fixedPackingOrder_le {M h : ℕ} {C α κ η τ Λ : ℝ}
    (hC : Magnitude M C) (hα : Magnitude M α) (hκ : Magnitude M κ)
    (hη : Magnitude M η) (hτ : Magnitude M τ) (hΛ : Magnitude M Λ) :
    Vortex.Explicit.fixedPackingOrder C α κ η τ Λ h ≤ fixedPackingOrderBound M := by
  have hM : 0 < M := hC.bound_pos
  exact stockMomentOrder_le (h := h) hC hα hκ hη hτ hΛ (by omega : 1 ≤ M)

#print axioms monitoredPackingOrder_le
#print axioms signedEnvelopeOrder_le
#print axioms localizedSignedOrder_le
#print axioms packingSeedOrder_le
#print axioms physicalMomentOrder_le
#print axioms physicalMomentBudget_magnitude
#print axioms packingCoverRate_magnitude
#print axioms packingCoverBudget_magnitude
#print axioms packingCoverOrder_le
#print axioms stockMomentOrder_le
#print axioms fixedPackingOrder_le
end TypedTriangle.TowerBounds
