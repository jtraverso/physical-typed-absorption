module
public import RequestProject.TypedTriangle.TowerSmoothBounds
public import RequestProject.TypedTriangle.TowerReferenceOrders
public import RequestProject.TypedTriangle.TowerRadiusBounds
public import RequestProject.TypedTriangle.ExplicitConcreteInnerSchedule
public import RequestProject.TypedTriangle.ExplicitScheduledRawProfileBudget
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.TowerBounds
open Vortex.Explicit RawReference.Explicit

def futureDensityMajorant (M : ℕ) : ℕ := prescribedBudgetBound (12*M)
def referencePrecisionMajorant (M : ℕ) : ℕ :=
  max M (max (M*(10*compressionPowerMajorant M))
    (max (paidBudgetMajorant M*4) (512*M*M*paidCostMajorant M)))
def referenceAgendaInput (M : ℕ) : ℕ := 12*M+referencePrecisionMajorant M
def referenceLoadMajorant (M : ℕ) : ℕ := prescribedLoadBound (referencePrecisionMajorant M)
def referenceAvoidMajorant (M : ℕ) : ℕ := prescribedAvoidBound (referenceAgendaInput M)
def referenceThresholdMajorant (M : ℕ) : ℕ := prescribedOrderBound (referenceAgendaInput M)
def profileToleranceMajorant (M : ℕ) : ℕ :=
  max (2*M*paidCostMajorant M) (referenceLoadMajorant M)
def innerRadiusInput (M : ℕ) : ℕ := M+2*M+max M (M*(2*(M+1)))+1
def innerRadiusMajorant (M : ℕ) : ℕ :=
  radiusMajorant profileToleranceMajorant (innerRadiusInput M) M
def innerNodeOrderMajorant (M : ℕ) : ℕ :=
  max (max (max (paidOrderMajorant M) (paidPreparedOrderMajorant M))
    (paidInverseOrderMajorant M)) (referenceThresholdMajorant M)
def innerScheduleMajorant (M : ℕ) : ℕ :=
  max (paidOrderMajorant M) (innerNodeOrderMajorant (M+innerRadiusMajorant M))
def scheduledPrecisionMajorant (M : ℕ) : ℕ := max (M*8) (128*M*M)
def scheduledOrderMajorant (M : ℕ) : ℕ := max 1 ((scheduledPrecisionMajorant M)^4)

private theorem reference_ab_magnitudes {M : ℕ} {C : ℝ} (hC : Magnitude M C) :
    Magnitude (12*M) (3/(4*C)) ∧ Magnitude (12*M) (2*C) := by
  have h3 : Magnitude 3 (3:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact ⟨(h3.div (h4.mul hC)).mono (by omega), (h2.mul hC).mono (by omega)⟩

theorem futureDensity_magnitude {M h : ℕ} {α C : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hh : h ≤ M) :
    Magnitude (futureDensityMajorant M) (futureDensity α C h) := by
  have hab := reference_ab_magnitudes hC
  exact prescribedBudget_magnitude hab.1 hab.2 (hα.mono (by omega)) (by omega)

theorem referencePrecision_magnitude {M h : ℕ} {α C ζ x : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hζ : Magnitude M ζ)
    (hx : Magnitude M x) (hh1 : 1 ≤ h) (hh : h ≤ M) :
    Magnitude (referencePrecisionMajorant M) (referencePrecision α C ζ h x) := by
  have h10 : Magnitude 10 (10:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h512 : Magnitude 512 (512:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hp := hα.div (h10.mul (hingePower_magnitude hh))
  have hb := (paidBudget_magnitude hα hh).div h4
  have hk := (((h512.mul hC).mul hC).mul (paidCost_magnitude hα hx hh1 hh)).inv
  exact hζ.min (hp.min (hb.min hk))

theorem referenceLoad_magnitude {M h : ℕ} {α C ζ x : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hζ : Magnitude M ζ)
    (hx : Magnitude M x) (hh1 : 1 ≤ h) (hh : h ≤ M) :
    Magnitude (referenceLoadMajorant M) (referenceLoad α C ζ h x) :=
  prescribedLoadTolerance_magnitude (referencePrecision_magnitude hα hC hζ hx hh1 hh)

theorem referenceAvoid_magnitude {M h : ℕ} {α C ζ x : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hζ : Magnitude M ζ)
    (hx : Magnitude M x) (hh1 : 1 ≤ h) (hh : h ≤ M) :
    Magnitude (referenceAvoidMajorant M) (referenceAvoid α C ζ h x) := by
  have hab := reference_ab_magnitudes hC
  have hp := referencePrecision_magnitude hα hC hζ hx hh1 hh
  have hM : M ≤ referenceAgendaInput M := by unfold referenceAgendaInput; omega
  exact prescribedAvoidBudget_magnitude (hab.1.mono (Nat.le_add_right _ _))
    (hab.2.mono (Nat.le_add_right _ _)) (hα.mono hM) (hp.mono (Nat.le_add_left _ _))

theorem referenceThreshold_le_majorant {M h : ℕ} {α C ζ x : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hζ : Magnitude M ζ)
    (hx : Magnitude M x) (hh1 : 1 ≤ h) (hh : h ≤ M) :
    referenceThreshold α C ζ h x ≤ referenceThresholdMajorant M := by
  have hab := reference_ab_magnitudes hC
  have hp := referencePrecision_magnitude hα hC hζ hx hh1 hh
  have hM : M ≤ referenceAgendaInput M := by unfold referenceAgendaInput; omega
  exact prescribedOrder_le_bound (hab.1.mono (Nat.le_add_right _ _))
    (hab.2.mono (Nat.le_add_right _ _)) (hα.mono hM) (hp.mono (Nat.le_add_left _ _)) (hh.trans hM)

theorem profileTolerance_magnitude {M h : ℕ} {α C ζ x : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hζ : Magnitude M ζ)
    (hx : Magnitude M x) (hh1 : 1 ≤ h) (hh : h ≤ M) :
    Magnitude (profileToleranceMajorant M)
      (paidProfileTolerance C (fun x => paidInverseCost α x h) (referenceLoad α C ζ h) x) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact (((h2.mul hC).mul (paidCost_magnitude hα hx hh1 hh)).inv).min
    (referenceLoad_magnitude hα hC hζ hx hh1 hh)

theorem innerRadius_magnitude {M h L : ℕ} {α C cap ζ η : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hcap : Magnitude M cap)
    (hζ : Magnitude M ζ) (hη : Magnitude M η) (hh1 : 1 ≤ h)
    (hh : h ≤ M) (hL : L ≤ M) (j : ℕ) :
    Magnitude (innerRadiusMajorant M) (innerRadius α C cap ζ η h L j) := by
  let U := innerRadiusInput M
  have hMU : M ≤ U := by dsimp [U,innerRadiusInput]; omega
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hb : Magnitude U (2*C) := (h2.mul hC).mono (by dsimp [U,innerRadiusInput]; omega)
  have hL1 : Magnitude (M+1) (L+1:ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      Magnitude.natCast (by omega : 1 ≤ L+1) (by omega : L+1 ≤ M+1)
  have ht : Magnitude U (radiusTop cap η L) :=
    (hcap.min (hη.div (h2.mul hL1))).mono (by dsimp [U,innerRadiusInput]; omega)
  exact radiusSequence_magnitude hb ht (hL.trans hMU) hL
    (fun K hUK x hx => profileTolerance_magnitude
      (hα.mono (hMU.trans hUK)) (hC.mono (hMU.trans hUK))
      (hζ.mono (hMU.trans hUK)) hx hh1 (hh.trans (hMU.trans hUK))) j

theorem innerNodeOrder_le_majorant {M h : ℕ} {α C ζ x : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hζ : Magnitude M ζ)
    (hx : Magnitude M x) (hh1 : 1 ≤ h) (hh : h ≤ M) :
    innerNodeOrder α C ζ h x ≤ innerNodeOrderMajorant M :=
  max_le_max (max_le_max (max_le_max (paidOrder_le_majorant hα hh)
    (paidPreparedOrder_le_majorant hα hh1 hh)) (paidInverseOrder_le_majorant hα hh1 hh))
    (referenceThreshold_le_majorant hα hC hζ hx hh1 hh)

theorem innerSchedule_le_majorant {M h L : ℕ} {α C cap ζ η : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hcap : Magnitude M cap)
    (hζ : Magnitude M ζ) (hη : Magnitude M η) (hh1 : 1 ≤ h)
    (hh : h ≤ M) (hL : L ≤ M) :
    innerScheduleOrder α C cap ζ η h L ≤ innerScheduleMajorant M := by
  apply max_le_max (paidOrder_le_majorant hα hh)
  apply Finset.sup_le
  intro j _
  have hx := innerRadius_magnitude hα hC hcap hζ hη hh1 hh hL j
  exact innerNodeOrder_le_majorant (hα.mono (Nat.le_add_right _ _))
    (hC.mono (Nat.le_add_right _ _)) (hζ.mono (Nat.le_add_right _ _))
    (hx.mono (Nat.le_add_left _ _)) hh1 (hh.trans (Nat.le_add_right _ _))

theorem finiteImageMin_magnitude {ι : Type} [Fintype ι] [Nonempty ι] {M : ℕ}
    {f : ι → ℝ} (hf : ∀ i, Magnitude M (f i)) :
    Magnitude M (((Finset.univ : Finset ι).image f).min' (by simp)) := by
  classical
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.min'_mem
    ((Finset.univ : Finset ι).image f) (by simp))
  rw [← hi]
  exact hf i

theorem scheduledPrecision_magnitude {M L : ℕ} {C : ℝ} {K ε : ℕ → ℝ}
    (hC : Magnitude M C) (hK : ∀ j ≤ L, Magnitude M (K j))
    (hε : ∀ j ≤ L, Magnitude M (ε j)) :
    Magnitude (scheduledPrecisionMajorant M) (scheduledProfilePrecision C K ε L) := by
  have h8 : Magnitude 8 (8:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h128 : Magnitude 128 (128:ℝ) := Magnitude.natCast (by decide) le_rfl
  apply finiteImageMin_magnitude
  intro j
  have hj : (j:ℕ) ≤ L := by omega
  exact ((hε j hj).div h8).min (((h128.mul hC).mul (hK j hj)).inv)

theorem scheduledOrder_le_majorant {M L : ℕ} {C : ℝ} {K ε : ℕ → ℝ}
    (hC : Magnitude M C) (hK : ∀ j ≤ L, Magnitude M (K j))
    (hε : ∀ j ≤ L, Magnitude M (ε j)) :
    scheduledProfileOrder C K ε L ≤ scheduledOrderMajorant M := by
  have hp := scheduledPrecision_magnitude hC hK hε
  simpa only [one_div,scheduledProfileOrder,scheduledOrderMajorant] using
    max_le_max_left 1 (hp.inv.pow 4).ceil_le

#print axioms referencePrecision_magnitude
#print axioms innerRadius_magnitude
#print axioms innerSchedule_le_majorant
#print axioms scheduledOrder_le_majorant
end TypedTriangle.TowerBounds
