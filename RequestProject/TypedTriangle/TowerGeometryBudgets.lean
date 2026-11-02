module
public import RequestProject.TypedTriangle.TowerGeometrySample
public import RequestProject.TypedTriangle.ExplicitIntrinsicPreparation
public import RequestProject.TypedTriangle.ExplicitPaidPreparedCore
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TypedTriangle.TowerBounds
open ExplicitGeometry Vortex.Explicit Vortex.ExplicitPaid

def deletionBudgetMajorant (M : ℕ) : ℕ := max 2 (M*(4*compressionPowerMajorant (M+1)))
def nestedBudgetMajorant (M : ℕ) : ℕ :=
  max (deletionBudgetMajorant M) (M*(128*compressionPowerMajorant (M+1)))
def latticeBudgetMajorant (M : ℕ) : ℕ := M*(8*compressionPowerMajorant M)
def hingeBudgetMajorant (M : ℕ) : ℕ := M*(64*compressionPowerMajorant M)
def geometryBudgetMajorant (M : ℕ) : ℕ := max (M*4) (hingeBudgetMajorant M)
def paidBudgetMajorant (M : ℕ) : ℕ := max (geometryBudgetMajorant M*2) (latticeBudgetMajorant M*2)

def geometryOrderMajorant (M : ℕ) : ℕ := 128*(M+2)*compressionPowerMajorant M*M+1
def latticeOrderMajorant (M : ℕ) : ℕ := 4*M+1
def paidOrderMajorant (M : ℕ) : ℕ := max (geometryOrderMajorant M) (latticeOrderMajorant M)
def nestedOrderMajorant (M : ℕ) : ℕ := (16+16*M*compressionPowerMajorant M)*M+1

def coreToleranceMajorant (M : ℕ) : ℕ := max (max (deletionBudgetMajorant M) (nestedBudgetMajorant M)) 2
def preparationToleranceMajorant (M : ℕ) : ℕ :=
  max (max (nestedBudgetMajorant M) (coreToleranceMajorant M)) (max 2 (M*(2*compressionPowerMajorant M)))

theorem deletionBudget_magnitude {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (deletionBudgetMajorant M) (deletionBudget α h) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hP := hingePower_magnitude (Nat.add_le_add_right hh 1)
  exact Magnitude.one.div h2 |>.min (hα.div (h4.mul hP))

theorem nestedBudget_magnitude {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (nestedBudgetMajorant M) (nestedBudget α h) := by
  have h128 : Magnitude 128 (128:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hP := hingePower_magnitude (Nat.add_le_add_right hh 1)
  exact (deletionBudget_magnitude hα hh).min (hα.div (h128.mul hP))

theorem latticeBudget_magnitude {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (latticeBudgetMajorant M) (latticeBudget α h) := by
  have h8 : Magnitude 8 (8:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact hα.div (h8.mul (hingePower_magnitude hh))

theorem hingeBudget_magnitude {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (hingeBudgetMajorant M) (hingeBudget α h) := by
  have h64 : Magnitude 64 (64:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact hα.div (h64.mul (hingePower_magnitude hh))

theorem geometryBudget_magnitude {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (geometryBudgetMajorant M) (geometryBudget α h) := by
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact (hα.div h4).min (hingeBudget_magnitude hα hh)

theorem paidBudget_magnitude {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (paidBudgetMajorant M) (paidBudget α h) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact ((geometryBudget_magnitude hα hh).div h2).min ((latticeBudget_magnitude hα hh).div h2)

theorem geometryOrder_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    geometryOrder α h ≤ geometryOrderMajorant M := by
  have h128 : Magnitude 128 (128:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hH : Magnitude (M+2) ((h+2:ℕ):ℝ) := Magnitude.natCast (by omega) (by omega)
  have hp := hingePower_magnitude hh
  have hd := ((h128.mul hH).mul hp).div hα
  have hc : ⌈128*(h+2)*(2:ℝ)^h.choose 2/α⌉₊ ≤
      128*(M+2)*compressionPowerMajorant M*M := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hd.ceil_le
  exact Nat.add_le_add_right hc 1

theorem latticeOrder_le_majorant {M : ℕ} {α : ℝ}
    (hα : Magnitude M α) : latticeOrder α ≤ latticeOrderMajorant M := by
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact Nat.add_le_add_right (h4.div hα).ceil_le 1

theorem paidOrder_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : paidOrder α h ≤ paidOrderMajorant M :=
  max_le_max (geometryOrder_le_majorant hα hh) (latticeOrder_le_majorant hα)

theorem nestedOrder_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : nestedOrder α h ≤ nestedOrderMajorant M := by
  have hP := hingePower_magnitude hh
  have hhR : (h:ℝ) ≤ M := Nat.cast_le.mpr hh
  have ha0 := hα.pos
  have hp0 := hP.pos
  have hr : (16+16*h*(2:ℝ)^h.choose 2)/α ≤
      (((16+16*M*compressionPowerMajorant M)*M:ℕ):ℝ) := by
    push_cast
    calc (16+16*h*(2:ℝ)^h.choose 2)/α = (16+16*h*(2:ℝ)^h.choose 2)*(1/α) := by ring
      _ ≤ (16+16*M*compressionPowerMajorant M)*M := by
        gcongr <;> first | exact hhR | exact hP.upper | exact hα.inv_upper
  exact Nat.add_le_add_right (Nat.ceil_le.mpr hr) 1

theorem coreTolerance_magnitude {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (coreToleranceMajorant M) (coreTolerance α h) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact ((deletionBudget_magnitude hα hh).min (nestedBudget_magnitude hα hh)).min (Magnitude.one.div h2)

theorem preparationTolerance_magnitude {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (preparationToleranceMajorant M) (preparationTolerance α h) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact ((nestedBudget_magnitude hα hh).min (coreTolerance_magnitude hα hh)).min
    ((Magnitude.one.div h2).min (hα.div (h2.mul (hingePower_magnitude hh))))

#print axioms preparationTolerance_magnitude
#print axioms paidBudget_magnitude
#print axioms paidOrder_le_majorant
end TypedTriangle.TowerBounds
