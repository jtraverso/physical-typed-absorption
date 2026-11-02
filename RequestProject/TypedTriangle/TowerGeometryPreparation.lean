module
public import RequestProject.TypedTriangle.TowerGeometryBudgets
public import RequestProject.TypedTriangle.TowerNatMonitors
public import RequestProject.TypedTriangle.ExplicitPaidSmooth
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.TowerBounds
open ExplicitSample Vortex.Explicit Incidence

def compL2Majorant (M : ℕ) : ℕ := 2*(3*(2*M))+1
def compNMajorant (M : ℕ) : ℕ := 4+24*compL2Majorant M
def compDMajorant (M s : ℕ) : ℕ := 16*compNMajorant M+96*(2*s+1)*compNMajorant M

def physicalRankMajorant (M : ℕ) : ℕ := (compressionSampleMajorant M+1)^2
def physicalColumnMajorant (M : ℕ) : ℕ :=
  3*compDMajorant (compressionClipMajorant M) (compressionSampleMajorant M)
def physicalTorsionMajorant (M : ℕ) : ℕ :=
  max 1 (QuotientBox.explicitTorsionBound (physicalRankMajorant M) (physicalColumnMajorant M))

def preparationRankMajorant (M : ℕ) : ℕ := physicalRankMajorant (M*2)
def preparationTorsionMajorant (M : ℕ) : ℕ := physicalTorsionMajorant (M*2)
def entryOrderMajorant (M : ℕ) : ℕ := max (nestedOrderMajorant M) (2*compressionOrderMajorant (M*2))
def coreOrderMajorant (M : ℕ) : ℕ := max (nestedOrderMajorant M) (2*M)
def preparationOrderMajorant (M : ℕ) : ℕ :=
  max (entryOrderMajorant M) (2*max (entryOrderMajorant M) (coreOrderMajorant M))

theorem compL2_le_majorant {M : ℕ} {α : ℝ} (hα : Magnitude M α) :
    compL2 α ≤ compL2Majorant M := by
  have hr : 2/α ≤ ((2*M:ℕ):ℝ) := by
    push_cast
    calc 2/α = 2*(1/α) := by ring
      _ ≤ 2*M := mul_le_mul_of_nonneg_left hα.inv_upper (by norm_num)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 3 (Nat.floor_le_of_le hr))) 1

theorem compN_le_majorant {M : ℕ} {α : ℝ} (hα : Magnitude M α) : compN α ≤ compNMajorant M :=
  Nat.add_le_add_left (Nat.mul_le_mul_left 24 (compL2_le_majorant hα)) 4

theorem compD_le_majorant {M s S : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hs : s ≤ S) : compD0 α s ≤ compDMajorant M S := by
  have hN := compN_le_majorant hα
  have hL : compL5 s ≤ 2*S+1 := Nat.add_le_add_right (Nat.mul_le_mul_left 2 hs) 1
  exact Nat.add_le_add (Nat.mul_le_mul_left 16 hN)
    (Nat.mul_le_mul (Nat.mul_le_mul_left 96 hL) hN)

theorem physicalRank_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : physicalRankBound α h ≤ physicalRankMajorant M :=
  Nat.pow_le_pow_left (Nat.add_le_add_right (compressionSampleSize_le_majorant hα hh) 1) 2

theorem physicalTorsion_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : physicalTorsionBound α h ≤ physicalTorsionMajorant M := by
  have hS := compressionSampleSize_le_majorant hα hh
  have hD := Nat.mul_le_mul_left 3 (compD_le_majorant (clipped_magnitude hα) hS)
  exact max_le_max le_rfl (torsionBound_mono (physicalRank_le_majorant hα hh) hD)

theorem preparationRank_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : preparationRank α h ≤ preparationRankMajorant M := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact physicalRank_le_majorant (hα.div h2) (hh.trans (by omega))

theorem preparationTorsion_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : preparationTorsion α h ≤ preparationTorsionMajorant M := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact physicalTorsion_le_majorant (hα.div h2) (hh.trans (by omega))

theorem entryOrder_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : entryOrder α h ≤ entryOrderMajorant M := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact max_le_max (nestedOrder_le_majorant hα hh)
    (Nat.mul_le_mul_left 2 (compressionOrder_le_majorant (hα.div h2) (hh.trans (by omega))))

theorem coreOrder_le_majorant {M h N : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) (hN : N ≤ M) : coreOrder α h N ≤ coreOrderMajorant M :=
  max_le_max (nestedOrder_le_majorant hα hh) (Nat.mul_le_mul_left 2 hN)

theorem preparationOrder_le_majorant {M h N : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) (hN : N ≤ M) : preparationOrder α h N ≤ preparationOrderMajorant M :=
  max_le_max (entryOrder_le_majorant hα hh)
    (Nat.mul_le_mul_left 2 (max_le_max (entryOrder_le_majorant hα hh) (coreOrder_le_majorant hα hh hN)))

/-- The normalized hinge density is controlled on both sides, including
its reciprocal; the height bound remains a purely natural expression. -/
def hingeDensityMajorant (M : ℕ) : ℕ :=
  (M^3*M^(2*M+1))*((2048*M^2)*compressionPowerMajorant (2*M))
def paidDensityMajorant (M : ℕ) : ℕ := max (M*2) (hingeDensityMajorant M)
def paidPreparedInputMajorant (M : ℕ) : ℕ := paidDensityMajorant M*4+2*M+1
def paidPreparedOrderMajorant (M : ℕ) : ℕ := compressionOrderMajorant (paidPreparedInputMajorant M)

theorem hingeDensity_magnitude {M h : ℕ} {α q : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hh1 : 1 ≤ h) (hh : h ≤ M) :
    Magnitude (hingeDensityMajorant M) (S07V49.hingeConstB α q h) := by
  have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hα.bound_pos)
  have hpow : M^(2*h+1) ≤ M^(2*M+1) := Nat.pow_le_pow_right hM (by omega)
  have hqpow : Magnitude (M^(2*M+1)) (q^(2*h+1)) := (hq.pow (2*h+1)).mono hpow
  have h2048 : Magnitude 2048 (2048:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hH : Magnitude M (h:ℝ) := Magnitude.natCast hh1 hh
  have hP := hingePower_magnitude (Nat.mul_le_mul_left 2 hh)
  exact ((hα.pow 3).mul hqpow).div ((h2048.mul (hH.pow 2)).mul hP)

theorem paidDensity_magnitude {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh1 : 1 ≤ h) (hh : h ≤ M) :
    Magnitude (paidDensityMajorant M) (paidDensity α h) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hOne : Magnitude M (1:ℝ) := Magnitude.one.mono (by have := hα.bound_pos; omega)
  exact (hα.div h2).min (hingeDensity_magnitude hα hOne hh1 hh)

theorem paidPreparedOrder_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh1 : 1 ≤ h) (hh : h ≤ M) :
    paidPreparedOrder α h ≤ paidPreparedOrderMajorant M := by
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hp : Magnitude (paidPreparedInputMajorant M) (paidDensity α h/4) :=
    ((paidDensity_magnitude hα hh1 hh).div h4).mono (by unfold paidPreparedInputMajorant; omega)
  exact compressionOrder_le_majorant hp (by unfold paidHingeOrder paidPreparedInputMajorant; omega)

/-- Elementary routing and smooth-coefficient envelopes. -/
def routingCompMajorant (M : ℕ) : ℕ := M+1
def routeDMajorant (M : ℕ) : ℕ := 12*routingCompMajorant M^2
def routeBudgetMajorant (M : ℕ) : ℕ := max (M*(8*compressionPowerMajorant M)) (routingCompMajorant M)
def routeOrderMajorant (M : ℕ) : ℕ := (8+4*M*compressionPowerMajorant M)*M+1
def kernelCapMajorant (M : ℕ) : ℕ := max 1 ((compressionPowerMajorant M*2)*M)
def nZeroMajorant (M : ℕ) : ℕ := 2*(12*M+3)*compressionPowerMajorant M*M
def smoothCoefficientMajorant (M : ℕ) : ℕ :=
  let D := 12*kernelCapMajorant M
  6*M+((3*M)*2)*(14*(3*D^2+D^3*3)+36*M^2)

theorem routingComp_le_majorant {M : ℕ} {α : ℝ} (hα : Magnitude M α) :
    RoutingConstants.compConst α ≤ routingCompMajorant M :=
  max_le (by unfold routingCompMajorant; omega)
    (hα.inv.ceil_le.trans (by unfold routingCompMajorant; omega))

theorem routeD_le_majorant {M : ℕ} {α : ℝ} (hα : Magnitude M α) :
    RoutingConstants.routeD α ≤ routeDMajorant M :=
  Nat.mul_le_mul_left 12 (Nat.pow_le_pow_left (routingComp_le_majorant hα) 2)

theorem routeBudget_magnitude {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (routeBudgetMajorant M) (RoutingConstants.routeδ α h) := by
  have h8 : Magnitude 8 (8:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hc : Magnitude (routingCompMajorant M) ((RoutingConstants.compConst α:ℕ):ℝ) :=
    Magnitude.natCast (RoutingConstants.one_le_compConst α) (routingComp_le_majorant hα)
  simpa only [RoutingConstants.routeδ,RoutingConstants.powP,routeBudgetMajorant,
    Nat.cast_pow,Nat.cast_ofNat,Nat.one_mul] using
    (hα.div (h8.mul (hingePower_magnitude hh))).min (Magnitude.one.div hc)

theorem routeOrder_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    RoutingConstants.routeN0 α h ≤ routeOrderMajorant M := by
  have hp := hingePower_magnitude hh
  have hhR : (h:ℝ) ≤ M := Nat.cast_le.mpr hh
  have hα0 := hα.pos
  have hr : (8+4*h*(2:ℝ)^h.choose 2)/α ≤
      (((8+4*M*compressionPowerMajorant M)*M:ℕ):ℝ) := by
    push_cast
    calc (8+4*h*(2:ℝ)^h.choose 2)/α = (8+4*h*(2:ℝ)^h.choose 2)*(1/α) := by ring
      _ ≤ (8+4*M*compressionPowerMajorant M)*M := by
        gcongr <;> first | exact hhR | exact hp.upper | exact hα.inv_upper
  simpa only [RoutingConstants.routeN0,RoutingConstants.powP,routeOrderMajorant,
    Nat.cast_pow,Nat.cast_ofNat] using Nat.add_le_add_right (Nat.ceil_le.mpr hr) 1

theorem kernelCap_magnitude {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (kernelCapMajorant M) (S10V23.Kc α h) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hp := hingePower_magnitude hh
  simpa only [S10V23.Kc,pow_succ,kernelCapMajorant] using Magnitude.one.max ((hp.mul h2).div hα)

theorem nZero_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    S10V23.Proc.nZero α h ≤ (nZeroMajorant M:ℝ) := by
  have hp := hingePower_magnitude hh
  have hhR : (h:ℝ) ≤ M := Nat.cast_le.mpr hh
  have hα0 := hα.pos
  change 2*(12*(h:ℝ)+3)*(2:ℝ)^h.choose 2/α ≤ ((2*(12*M+3)*compressionPowerMajorant M*M:ℕ):ℝ)
  push_cast
  calc 2*(12*(h:ℝ)+3)*(2:ℝ)^h.choose 2/α =
      2*(12*(h:ℝ)+3)*(2:ℝ)^h.choose 2*(1/α) := by ring
    _ ≤ 2*(12*M+3)*compressionPowerMajorant M*M := by
      gcongr <;> first | exact hhR | exact hp.upper | exact hα.inv_upper

theorem smoothCoefficient_magnitude {M h : ℕ} {α K : ℝ}
    (hα : Magnitude M α) (hK : Magnitude M K) (hh : h ≤ M) :
    Magnitude (smoothCoefficientMajorant M) (NativeSmooth.coeff α h K) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h3 : Magnitude 3 (3:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h6 : Magnitude 6 (6:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h12 : Magnitude 12 (12:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h14 : Magnitude 14 (14:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h36 : Magnitude 36 (36:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hD := h12.mul (kernelCap_magnitude hα hh)
  exact (h6.mul hα.inv).add
    (((h3.mul hK).div h2).mul
      ((h14.mul ((h3.mul (hD.pow 2)).add ((hD.pow 3).div h3))).add (h36.mul (hα.inv.pow 2))))

#print axioms physicalTorsion_le_majorant
#print axioms preparationOrder_le_majorant
#print axioms paidDensity_magnitude
#print axioms paidPreparedOrder_le_majorant
end TypedTriangle.TowerBounds
