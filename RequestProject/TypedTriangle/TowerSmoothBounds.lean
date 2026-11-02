module
public import RequestProject.TypedTriangle.TowerUniformCertificate
public import RequestProject.TypedTriangle.TowerNatMonitors
public import RequestProject.TypedTriangle.ExplicitPaidSmooth
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.TowerBounds
open ExplicitSample ExplicitCertificate NativeSmooth.Explicit Vortex.Explicit

def smoothSampleMajorant (M : ℕ) : ℕ := compressionSampleMajorant (2*M)
def smoothDMajorant (M : ℕ) : ℕ := compDMajorant (2*M) (smoothSampleMajorant M)
def smoothDemandMajorant (M : ℕ) : ℕ :=
  let S := smoothSampleMajorant M
  let D := smoothDMajorant M
  let R := routeDMajorant (2*M)
  3*R*natKernel ((S+1)^2) (max (D*(3*R)) (3*D))
def smoothCertMajorant (M : ℕ) : ℕ := uniformCertMajorant (4*M)*smoothDemandMajorant M

def congestionMajorant (M : ℕ) : ℕ :=
  let K := smoothCertMajorant M
  let D := routeDMajorant (2*M)
  let δ := routeBudgetMajorant (2*M)
  K*(4*D+3+32*D*δ+12*K*M+2*D+2)+1

def inverseCostMajorant (M : ℕ) : ℕ := smoothCoefficientMajorant (M+congestionMajorant M)
def inverseOrderMajorant (M : ℕ) : ℕ :=
  max (max (compressionOrderMajorant (4*M))
    (max (compressionOrderMajorant (2*M)) (routeOrderMajorant (2*M)))) (nZeroMajorant M)
def paidSmoothInputMajorant (M : ℕ) : ℕ :=
  M+paidDensityMajorant M+max M 2+2*M+1
def paidCostMajorant (M : ℕ) : ℕ :=
  max (inverseCostMajorant (paidSmoothInputMajorant M)) (paidBudgetMajorant M)
def paidInverseOrderMajorant (M : ℕ) : ℕ := inverseOrderMajorant (paidSmoothInputMajorant M)

theorem smoothSample_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : sampleSize α h ≤ smoothSampleMajorant M := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have ha : Magnitude (2*M) (α/2) := (hα.div h2).mono (by omega)
  exact compressionSampleSize_le_majorant ha (by omega)

theorem smoothD_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : sampleD α h ≤ smoothDMajorant M := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have ha : Magnitude (2*M) (α/2) := (hα.div h2).mono (by omega)
  exact compD_le_majorant (clamp_one_magnitude ha) (smoothSample_le_majorant hα hh)

theorem smoothDemand_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : certificateDemand α h ≤ smoothDemandMajorant M := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have ha : Magnitude (2*M) (α/2) := (hα.div h2).mono (by omega)
  have hR := routeD_le_majorant ha
  have hS := smoothSample_le_majorant hα hh
  have hD := smoothD_le_majorant hα hh
  change 3*RoutingConstants.routeD (α/2)*GroupingExplicit.kernelBound ((sampleSize α h+1)^2)
    (max (sampleD α h*(3*RoutingConstants.routeD (α/2))) (3*sampleD α h)) ≤ _
  rw [← natKernel_eq]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 3 hR)
    (natKernel_mono (Nat.pow_le_pow_left (Nat.add_le_add_right hS 1) 2)
      (max_le_max (Nat.mul_le_mul hD (Nat.mul_le_mul_left 3 hR)) (Nat.mul_le_mul_left 3 hD)))

theorem smoothCert_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : certificateCost α h ≤ smoothCertMajorant M := by
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have ha : Magnitude (4*M) (α/4) := (hα.div h4).mono (by omega)
  exact Nat.mul_le_mul (uniformCertCost_le_majorant ha (by omega)) (smoothDemand_le_majorant hα hh)

private theorem congestion_polynomial_magnitude {M K D E : ℕ} {k d δ β : ℝ}
    (hk0 : 0 ≤ k) (hd0 : 0 ≤ d) (hk : k ≤ (K:ℝ)) (hd : d ≤ (D:ℝ))
    (hδ : Magnitude E δ) (hβ : Magnitude M β) :
    Magnitude (K*(4*D+3+32*D*E+12*K*M+2*D+2)+1)
      (k*(4*d+3+32*d/δ+12*k/β+2*d+2)+1) := by
  have hδ0 := hδ.pos
  have hβ0 := hβ.pos
  have hS : 0 ≤ 4*d+3+32*d/δ+12*k/β+2*d+2 := by positivity
  have hOne : 1 ≤ k*(4*d+3+32*d/δ+12*k/β+2*d+2)+1 := by
    linarith only [mul_nonneg hk0 hS]
  have hδi : δ⁻¹ ≤ (E:ℝ) := by simpa only [one_div] using hδ.inv_upper
  have hβi : β⁻¹ ≤ (M:ℝ) := by simpa only [one_div] using hβ.inv_upper
  have hUpper : k*(4*d+3+32*d/δ+12*k/β+2*d+2)+1 ≤
      (K*(4*D+3+32*D*E+12*K*M+2*D+2)+1:ℕ) := by
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,div_eq_mul_inv]
    gcongr <;> norm_num
  refine ⟨lt_of_lt_of_le (by norm_num) hOne,hUpper,?_⟩
  have hi : 1/(k*(4*d+3+32*d/δ+12*k/β+2*d+2)+1) ≤ 1 := by
    simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hOne
  exact hi.trans (hOne.trans hUpper)

theorem congestion_magnitude {M h : ℕ} {α β : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hh : h ≤ M) :
    Magnitude (congestionMajorant M) (congestionCost α β h) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have ha : Magnitude (2*M) (α/2) := (hα.div h2).mono (by omega)
  have hδ := routeBudget_magnitude ha (by omega : h ≤ 2*M)
  have hK : (certificateCost α h:ℝ) ≤ smoothCertMajorant M := by
    exact_mod_cast smoothCert_le_majorant hα hh
  have hD : (RoutingConstants.routeD (α/2):ℝ) ≤ routeDMajorant (2*M) := by
    exact_mod_cast routeD_le_majorant ha
  have hp := congestion_polynomial_magnitude
    (Nat.cast_nonneg (certificateCost α h)) (Nat.cast_nonneg (RoutingConstants.routeD (α/2)))
    hK hD hδ hβ
  simpa only [congestionCost,congestionMajorant,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hp

theorem inverseCost_magnitude {M h : ℕ} {α β : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hh : h ≤ M) :
    Magnitude (inverseCostMajorant M) (inverseCost α β h) := by
  have hc := congestion_magnitude hα hβ hh
  exact smoothCoefficient_magnitude (hα.mono (Nat.le_add_right _ _))
    (hc.mono (Nat.le_add_left _ _)) (hh.trans (Nat.le_add_right _ _))

theorem inverseOrder_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : inverseOrder α h ≤ inverseOrderMajorant M := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have ha2 : Magnitude (2*M) (α/2) := (hα.div h2).mono (by omega)
  have ha4 : Magnitude (4*M) (α/4) := (hα.div h4).mono (by omega)
  exact max_le_max (max_le_max (compressionOrder_le_majorant ha4 (by omega))
    (max_le_max (compressionOrder_le_majorant ha2 (by omega)) (routeOrder_le_majorant ha2 (by omega))))
    (Nat.ceil_le.mpr (nZero_le_majorant hα hh))

theorem paidCost_magnitude {M h : ℕ} {α β : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hh1 : 1 ≤ h) (hh : h ≤ M) :
    Magnitude (paidCostMajorant M) (paidInverseCost α β h) := by
  let U := paidSmoothInputMajorant M
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hd : Magnitude U (paidDensity α h) := (paidDensity_magnitude hα hh1 hh).mono (by dsimp [U,paidSmoothInputMajorant]; omega)
  have hb : Magnitude U (min β (1/2)) := (hβ.min (Magnitude.one.div h2)).mono (by dsimp [U,paidSmoothInputMajorant]; omega)
  have hH : paidHingeOrder h ≤ U := by dsimp [paidHingeOrder,U,paidSmoothInputMajorant]; omega
  simpa only [paidInverseCost,paidCostMajorant,Nat.one_mul] using
    (inverseCost_magnitude hd hb hH).max (paidBudget_magnitude hα hh).inv

theorem paidInverseOrder_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh1 : 1 ≤ h) (hh : h ≤ M) :
    paidInverseOrder α h ≤ paidInverseOrderMajorant M := by
  have hd : Magnitude (paidSmoothInputMajorant M) (paidDensity α h) :=
    (paidDensity_magnitude hα hh1 hh).mono (by unfold paidSmoothInputMajorant; omega)
  exact inverseOrder_le_majorant hd (by unfold paidHingeOrder paidSmoothInputMajorant; omega)

#print axioms uniformCertCost_le_majorant
#print axioms congestion_magnitude
#print axioms paidCost_magnitude
#print axioms paidInverseOrder_le_majorant
end TypedTriangle.TowerBounds
