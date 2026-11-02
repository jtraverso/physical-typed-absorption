module
public import RequestProject.TypedTriangle.TowerNatTerminal
public import RequestProject.TypedTriangle.ExplicitResourceCore
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.TowerBounds

def bankGammaBound (M : ℕ) : ℕ := M*M*8
def bankEtaBound (M B : ℕ) : ℕ := max (M*(M^2)*8) (bankGammaBound M*(B+1))
def monitorCapBound (M K : ℕ) : ℕ := (M*(K+1))*(2+15*M)
def bankOrderBound (M : ℕ) : ℕ := 8*(M*(M^2))+1
def cellDegreeBudgetBound (M h : ℕ) : ℕ := max (M*8) (supplyBudgetBound (M*2) h*2)
def bankProtectionBound (M h : ℕ) : ℕ := cellDegreeBudgetBound M h*2
def bankToleranceBound (M h : ℕ) : ℕ := max (bankProtectionBound M h) M
def coreDeltaBound (M h : ℕ) : ℕ := max 2 (M*(2*2^(h.choose 2)))
def geometricDeletionBound (M h : ℕ) : ℕ := max 2 (M*(4*2^((h+1).choose 2)))
def cellDeletionBound (M h : ℕ) : ℕ := max (geometricDeletionBound M h) (coreDeltaBound M h)
def bankDeletionBound (M h : ℕ) : ℕ :=
  max (geometricDeletionBound M h) (max (max (cellDeletionBound M h) (coreDeltaBound M h)) M)

theorem bankGamma_magnitude {M : ℕ} {q ε : ℝ} (hq : Magnitude M q) (hε : Magnitude M ε) :
    Magnitude (bankGammaBound M) (StockEntry.Explicit.bankGamma q ε) :=
  (hε.mul hq).div (Magnitude.natCast (by decide : 1 ≤ (8:ℕ)) le_rfl)

theorem bankEta_magnitude {M : ℕ} {κ q ε : ℝ}
    (hκ : Magnitude M κ) (hq : Magnitude M q) (hε : Magnitude M ε) (B : ℕ) :
    Magnitude (bankEtaBound M B) (StockEntry.Explicit.bankEta κ q ε B) := by
  have h8 := Magnitude.natCast (by decide : 1 ≤ (8:ℕ)) (le_refl 8)
  have hden := Magnitude.natCast (by omega : 1 ≤ B+1) (le_refl (B+1))
  have h := ((hκ.mul (hq.pow 2)).div h8).min ((bankGamma_magnitude hq hε).div hden)
  simpa only [bankEtaBound, StockEntry.Explicit.bankEta, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat] using h

theorem monitorCap_magnitude {M : ℕ} {Λ η : ℝ}
    (hΛ : Magnitude M Λ) (hη : Magnitude M η) (K : ℕ) :
    Magnitude (monitorCapBound M K) (StockEntry.Explicit.monitorCap Λ η K) := by
  have h2 := Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) (le_refl 2)
  have h15 := Magnitude.natCast (by decide : 1 ≤ (15:ℕ)) (le_refl 15)
  have hden := Magnitude.natCast (by omega : 1 ≤ K+1) (le_refl (K+1))
  have h := (hη.div hden).div (h2.add (h15.mul hΛ))
  simpa only [monitorCapBound, StockEntry.Explicit.monitorCap, StockEntry.Explicit.smallMomentCap,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using h

theorem bankOrder_le {M : ℕ} {κ q : ℝ} (hκ : Magnitude M κ) (hq : Magnitude M q) :
    StockEntry.Explicit.bankOrder κ q ≤ bankOrderBound M := by
  have h8 := Magnitude.natCast (by decide : 1 ≤ (8:ℕ)) (le_refl 8)
  exact Nat.add_le_add_right (h8.div (hκ.mul (hq.pow 2))).ceil_le 1

theorem boundedPieceBudget_magnitude {M : ℕ} {α : ℝ} (hα : Magnitude M α) (h : ℕ) :
    Magnitude (supplyBudgetBound M h) (CatalogNative.Explicit.boundedPieceBudget α h) := by
  have hM : 1 ≤ M := by have := hα.bound_pos; omega
  exact supplyBudget_magnitude hα (Magnitude.one.mono hM) h

theorem cellDegreeBudget_magnitude {M : ℕ} {α β : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (h : ℕ) :
    Magnitude (cellDegreeBudgetBound M h) (CatalogNative.Explicit.catalogCellDegreeBudget α β h) := by
  have h2 := Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) (le_refl 2)
  have h8 := Magnitude.natCast (by decide : 1 ≤ (8:ℕ)) (le_refl 8)
  exact (hβ.div h8).min ((boundedPieceBudget_magnitude (hα.div h2) h).div h2)

/-- The old-forbidden protection magnitude precedes every requested new density. -/
theorem bankProtection_magnitude {M : ℕ} {α β : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (h : ℕ) :
    Magnitude (bankProtectionBound M h) (CatalogNative.Explicit.bankProtectionBudget α β h) :=
  (cellDegreeBudget_magnitude hα hβ h).div (Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) le_rfl)

theorem bankTolerance_magnitude {M : ℕ} {α β ε : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hε : Magnitude M ε) (h : ℕ) :
    Magnitude (bankToleranceBound M h) (CatalogNative.Explicit.bankTolerance α β ε h) :=
  (bankProtection_magnitude hα hβ h).min hε

theorem coreDelta_magnitude {M : ℕ} {β : ℝ} (hβ : Magnitude M β) (h : ℕ) :
    Magnitude (coreDeltaBound M h) (S07V42.coreDelta β h) := by
  have h2 := Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) (le_refl 2)
  exact (Magnitude.one.div h2).min (hβ.div (h2.mul (h2.pow (h.choose 2))))

theorem geometricDeletion_magnitude {M : ℕ} {α : ℝ} (hα : Magnitude M α) (h : ℕ) :
    Magnitude (geometricDeletionBound M h) (ExplicitGeometry.deletionBudget α h) := by
  have h2 := Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) (le_refl 2)
  have h4 := Magnitude.natCast (by decide : 1 ≤ (4:ℕ)) (le_refl 4)
  exact (Magnitude.one.div h2).min (hα.div (h4.mul (h2.pow ((h+1).choose 2))))

theorem cellDeletion_magnitude {M : ℕ} {α β : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (h : ℕ) :
    Magnitude (cellDeletionBound M h) (CatalogNative.Explicit.catalogCellDeletionBudget α β h) :=
  (geometricDeletion_magnitude hα h).min (coreDelta_magnitude hβ h)

theorem bankDeletion_magnitude {M : ℕ} {α β δ : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hδ : Magnitude M δ) (h : ℕ) :
    Magnitude (bankDeletionBound M h) (CatalogNative.Explicit.bankDeletionBudget α β δ h) :=
  (geometricDeletion_magnitude hα h).min (((cellDeletion_magnitude hα hβ h).min
    (coreDelta_magnitude hβ h)).min hδ)

#print axioms bankGamma_magnitude
#print axioms bankEta_magnitude
#print axioms monitorCap_magnitude
#print axioms bankOrder_le
#print axioms boundedPieceBudget_magnitude
#print axioms bankProtection_magnitude
#print axioms bankTolerance_magnitude
#print axioms bankDeletion_magnitude
end TypedTriangle.TowerBounds
