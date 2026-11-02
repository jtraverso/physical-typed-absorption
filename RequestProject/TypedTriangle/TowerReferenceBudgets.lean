module
public import RequestProject.TypedTriangle.TowerGeometryBudgets
public import RequestProject.TypedTriangle.ExplicitPrescribedReference
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TypedTriangle.TowerBounds
open RawReference.Explicit

def referenceProviderBound (M : ℕ) : ℕ :=
  let Z := compressionPowerMajorant M * (M*2)
  let A := 1+3*(2*M)
  Z*(A+A^2)*(1+2*(1+3*(2*M)+3*Z))

def referenceSeedBudgetBound (M : ℕ) : ℕ :=
  max (M*(10*compressionPowerMajorant M))
    (max (32*M) (M*(2*(16*M+4)*(referenceProviderBound (2*M)+1))))

def referenceStockBudgetBound (M : ℕ) : ℕ := max (referenceSeedBudgetBound M) (8*M)
def referencePrecisionBound (M : ℕ) : ℕ := max (M*2) 2
def referenceToleranceBound (M : ℕ) : ℕ := referencePrecisionBound M*8
def referenceLoadBound (M : ℕ) : ℕ := max (referenceToleranceBound M*4) 4
def referenceWeightBound (M : ℕ) : ℕ := M+M*2
def referenceAvoidBound (M : ℕ) : ℕ := max (M*2) (referenceToleranceBound M*(8*referenceWeightBound M))
def envelopeLoadBound (M : ℕ) : ℕ := 4*M+1
def envelopeDegreeBound (M : ℕ) : ℕ := 2+2*envelopeLoadBound M
def envelopeBudgetBound (M : ℕ) : ℕ := M*(64*(envelopeLoadBound M+4))
def envelopeOrderBound (M : ℕ) : ℕ := 32*envelopeLoadBound M*M+1
def prescribedBudgetBound (M : ℕ) : ℕ :=
  max (envelopeBudgetBound M) (referenceStockBudgetBound M*(2*(envelopeDegreeBound M+1)))
def prescribedLoadBound (M : ℕ) : ℕ := max (referenceLoadBound M) 2
def prescribedAvoidBound (M : ℕ) : ℕ := max (referenceAvoidBound M) (envelopeBudgetBound M)

theorem referenceProvider_magnitude {M h : ℕ} {α κ : ℝ}
    (hα : Magnitude M α) (hκ : Magnitude M κ) (hh : h ≤ M) :
    Magnitude (referenceProviderBound M) (provL α κ h) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h3 : Magnitude 3 (3:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hZ := (hingePower_magnitude hh).div (hα.div h2)
  have hA := Magnitude.one.add (h3.mul (h2.mul hκ))
  exact (hZ.mul (hA.add (hA.pow 2))).mul
    (Magnitude.one.add (h2.mul ((Magnitude.one.add (h3.mul (h2.mul hκ))).add (h3.mul hZ))))

theorem referenceSeedBudget_magnitude {M h : ℕ} {a b α : ℝ}
    (ha : Magnitude M a) (hb : Magnitude M b) (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (referenceSeedBudgetBound M) (seedBudget a b α h) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h10 : Magnitude 10 (10:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h16 : Magnitude 16 (16:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h32 : Magnitude 32 (32:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hMM : M ≤ 2*M := by omega
  have hp := referenceProvider_magnitude (hα.mono hMM) (h2.mul hb) (hh.trans hMM)
  have hFirst := hα.div (h10.mul (hingePower_magnitude hh))
  have hSecond := Magnitude.one.div (h32.mul hb)
  have hThird := ha.div ((h2.mul ((h16.mul hb).add h4)).mul (hp.add Magnitude.one))
  simpa only [referenceSeedBudgetBound,seedBudget,Nat.one_mul] using hFirst.min (hSecond.min hThird)

theorem referenceStockBudget_magnitude {M h : ℕ} {a b α : ℝ}
    (ha : Magnitude M a) (hb : Magnitude M b) (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (referenceStockBudgetBound M) (stockBudget a b α h) := by
  have h8 : Magnitude 8 (8:ℝ) := Magnitude.natCast (by decide) le_rfl
  simpa only [referenceStockBudgetBound,stockBudget,Nat.one_mul] using
    (referenceSeedBudget_magnitude ha hb hα hh).min (Magnitude.one.div (h8.mul hb))

theorem referencePackingPrecision_magnitude {M : ℕ} {η : ℝ} (hη : Magnitude M η) :
    Magnitude (referencePrecisionBound M) (referencePackingPrecision η) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  simpa only [referencePrecisionBound,referencePackingPrecision,Nat.one_mul] using
    (hη.div h2).min (Magnitude.one.div h2)

theorem referencePackingTolerance_magnitude {M : ℕ} {η : ℝ} (hη : Magnitude M η) :
    Magnitude (referenceToleranceBound M) (referencePackingTolerance η) := by
  have h8 : Magnitude 8 (8:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact (referencePackingPrecision_magnitude hη).div h8

theorem referenceLoadTolerance_magnitude {M : ℕ} {η : ℝ} (hη : Magnitude M η) :
    Magnitude (referenceLoadBound M) (referenceLoadTolerance η) := by
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  simpa only [referenceLoadBound,referenceLoadTolerance,Nat.one_mul] using
    ((referencePackingTolerance_magnitude hη).div h4).min (Magnitude.one.div h4)

theorem referenceWeightUpper_magnitude {M : ℕ} {a b : ℝ}
    (ha : Magnitude M a) (hb : Magnitude M b) :
    Magnitude (referenceWeightBound M) (referenceWeightUpper a b) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact hb.add (ha.div h2)

theorem referenceAvoidBudget_magnitude {M : ℕ} {a b η : ℝ}
    (ha : Magnitude M a) (hb : Magnitude M b) (hη : Magnitude M η) :
    Magnitude (referenceAvoidBound M) (referenceAvoidBudget a b η) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h8 : Magnitude 8 (8:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact (hη.div h2).min ((referencePackingTolerance_magnitude hη).div
    (h8.mul (referenceWeightUpper_magnitude ha hb)))

theorem envelopeLoad_le_bound {M : ℕ} {α : ℝ} (hα : Magnitude M α) :
    Envelope.Explicit.envelopeLoad α ≤ envelopeLoadBound M := by
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact Nat.add_le_add_right (h4.div hα).ceil_le 1

theorem envelopeDegree_le_bound {M : ℕ} {α : ℝ} (hα : Magnitude M α) :
    Envelope.Explicit.envelopeDegree α ≤ envelopeDegreeBound M := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 (envelopeLoad_le_bound hα)) 2

theorem envelopeLoad_magnitude {M : ℕ} {α : ℝ} (hα : Magnitude M α) :
    Magnitude (envelopeLoadBound M) (Envelope.Explicit.envelopeLoad α : ℝ) := by
  exact Magnitude.natCast (by unfold Envelope.Explicit.envelopeLoad; omega) (envelopeLoad_le_bound hα)

theorem envelopeBudget_magnitude {M : ℕ} {α : ℝ} (hα : Magnitude M α) :
    Magnitude (envelopeBudgetBound M) (Envelope.Explicit.envelopeBudget α) := by
  have h64 : Magnitude 64 (64:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hL : Magnitude (envelopeLoadBound M+4) ((Envelope.Explicit.envelopeLoad α:ℝ)+4) := by
    have hn := envelopeLoad_le_bound hα
    have h := Magnitude.natCast (by omega : 1 ≤ Envelope.Explicit.envelopeLoad α+4)
      (Nat.add_le_add_right hn 4)
    simpa only [Nat.cast_add,Nat.cast_ofNat] using h
  exact hα.div (h64.mul hL)

theorem envelopeOrder_le_bound {M : ℕ} {α : ℝ} (hα : Magnitude M α) :
    Envelope.Explicit.envelopeOrder α ≤ envelopeOrderBound M := by
  have h32 : Magnitude 32 (32:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact Nat.add_le_add_right ((h32.mul (envelopeLoad_magnitude hα)).div hα).ceil_le 1

theorem prescribedBudget_magnitude {M h : ℕ} {a b α : ℝ}
    (ha : Magnitude M a) (hb : Magnitude M b) (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (prescribedBudgetBound M) (prescribedBudget a b α h) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hD : Magnitude (envelopeDegreeBound M+1) ((Envelope.Explicit.envelopeDegree α:ℝ)+1) := by
    have h := Magnitude.natCast (Nat.succ_pos _) (Nat.add_le_add_right (envelopeDegree_le_bound hα) 1)
    simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_succ] using h
  exact (envelopeBudget_magnitude hα).min ((referenceStockBudget_magnitude ha hb hα hh).div (h2.mul hD))

theorem prescribedLoadTolerance_magnitude {M : ℕ} {η : ℝ} (hη : Magnitude M η) :
    Magnitude (prescribedLoadBound M) (prescribedLoadTolerance η) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  simpa only [prescribedLoadBound,prescribedLoadTolerance,Nat.one_mul] using
    (referenceLoadTolerance_magnitude hη).min (Magnitude.one.div h2)

theorem prescribedAvoidBudget_magnitude {M : ℕ} {a b α η : ℝ}
    (ha : Magnitude M a) (hb : Magnitude M b) (hα : Magnitude M α) (hη : Magnitude M η) :
    Magnitude (prescribedAvoidBound M) (prescribedAvoidBudget a b α η) :=
  (referenceAvoidBudget_magnitude ha hb hη).min (envelopeBudget_magnitude hα)

#print axioms referenceProvider_magnitude
#print axioms referenceSeedBudget_magnitude
#print axioms prescribedBudget_magnitude
#print axioms prescribedAvoidBudget_magnitude
end TypedTriangle.TowerBounds
