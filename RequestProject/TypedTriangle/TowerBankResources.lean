module
public import RequestProject.TypedTriangle.TowerReferenceBudgets
public import RequestProject.TypedTriangle.ExplicitResourceCore
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.TowerBounds
open CorePaid.Explicit Vortex.Explicit BasalIncidence.Explicit

def paymentForbiddenMajorant (M : ℕ) : ℕ := M*M*16
def paymentGammaMajorant (M : ℕ) : ℕ := max (M*M*32) (M*8)
def paymentTMajorant (M : ℕ) : ℕ := M+61*M+61
def paymentCostMajorant (M : ℕ) : ℕ := 2*(paymentGammaMajorant M+8)*paymentTMajorant M+4
def paymentInputMajorant (M : ℕ) : ℕ :=
  max (M*M*(8*paymentCostMajorant M)) (M*(12*paymentTMajorant M))
def paymentOrderMajorant (M : ℕ) : ℕ := max (max (paymentInputMajorant M) (paymentGammaMajorant M)) 1

theorem paymentForbidden_magnitude {M : ℕ} {κ μ : ℝ}
    (hκ : Magnitude M κ) (hμ : Magnitude M μ) :
    Magnitude (paymentForbiddenMajorant M) (paymentForbiddenBudget κ μ) := by
  have hc : Magnitude 16 (16:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact (hκ.mul hμ).div hc

theorem paymentGamma_magnitude {M : ℕ} {κ μ τ : ℝ}
    (hκ : Magnitude M κ) (hμ : Magnitude M μ) (hτ : Magnitude M τ) :
    Magnitude (paymentGammaMajorant M) (paymentGamma κ μ τ) := by
  have h32 : Magnitude 32 (32:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h8 : Magnitude 8 (8:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact ((hκ.mul hμ).div h32).min (hτ.div h8)

theorem paymentJ_le_majorant {M : ℕ} {κ μ τ : ℝ}
    (hκ : Magnitude M κ) (hμ : Magnitude M μ) (hτ : Magnitude M τ) :
    paymentJ κ μ τ ≤ paymentGammaMajorant M := (paymentGamma_magnitude hκ hμ hτ).inv.ceil_le

theorem paymentCost_magnitude {M A D : ℕ} {κ μ τ : ℝ}
    (hκ : Magnitude M κ) (hμ : Magnitude M μ) (hτ : Magnitude M τ)
    (hA : A ≤ M) (hD : D ≤ M) :
    Magnitude (paymentCostMajorant M) (paymentCost κ μ τ A D) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h8 : Magnitude 8 (8:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hΓ := paymentGamma_magnitude hκ hμ hτ
  have hJ : Magnitude (paymentGammaMajorant M) ((paymentJ κ μ τ:ℕ):ℝ) :=
    Magnitude.natCast hΓ.inv.ceil_pos (paymentJ_le_majorant hκ hμ hτ)
  have hT : Magnitude (paymentTMajorant M) ((paymentT A D:ℕ):ℝ) :=
    Magnitude.natCast (by unfold paymentT; omega) (by unfold paymentT paymentTMajorant; omega)
  simpa only [paymentCost,paymentCostMajorant,Nat.cast_add,Nat.cast_ofNat] using
    (h2.mul (hJ.add h8) |>.mul hT |>.add h4)

theorem paymentInput_magnitude {M A D : ℕ} {κ μ τ : ℝ}
    (hκ : Magnitude M κ) (hμ : Magnitude M μ) (hτ : Magnitude M τ)
    (hA : A ≤ M) (hD : D ≤ M) :
    Magnitude (paymentInputMajorant M) (paymentInputBudget κ μ τ A D) := by
  have h8 : Magnitude 8 (8:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h12 : Magnitude 12 (12:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hT : Magnitude (paymentTMajorant M) ((paymentT A D:ℕ):ℝ) :=
    Magnitude.natCast (by unfold paymentT; omega) (by unfold paymentT paymentTMajorant; omega)
  exact ((hκ.mul hμ).div (h8.mul (paymentCost_magnitude hκ hμ hτ hA hD))).min
    (hτ.div (h12.mul hT))

theorem paymentOrder_le_majorant {M A D : ℕ} {κ μ τ : ℝ}
    (hκ : Magnitude M κ) (hμ : Magnitude M μ) (hτ : Magnitude M τ)
    (hA : A ≤ M) (hD : D ≤ M) : paymentOrder κ μ τ A D ≤ paymentOrderMajorant M :=
  max_le_max (max_le_max (paymentInput_magnitude hκ hμ hτ hA hD).inv.ceil_le
    (paymentGamma_magnitude hκ hμ hτ).inv.ceil_le) le_rfl

def selectorAMajorant (M : ℕ) : ℕ := 200*M+8
def selectorEpsilonMajorant (M B : ℕ) : ℕ := (M+1)^2*(10000*B)
def selectorQMajorant (M B : ℕ) : ℕ := 4*B*(M+1)+2
def selectorScale (M : ℕ) : ℕ :=
  M+M*M*2+M*2+selectorAMajorant M+selectorQMajorant M (selectorAMajorant M)+1
def selectorStockMajorant (M : ℕ) : ℕ :=
  max (selectorEpsilonMajorant M (selectorAMajorant M)) (paymentForbiddenMajorant (selectorScale M))
def selectorInputMajorant (M : ℕ) : ℕ :=
  max (selectorEpsilonMajorant M (selectorAMajorant M)) (paymentInputMajorant (selectorScale M))
def selectorOrderMajorant (M : ℕ) : ℕ :=
  max (paymentOrderMajorant (selectorScale M)) (200*(M+1))

theorem selectorA_le_majorant {M t : ℕ} (ht : t ≤ M) : S07V27.selA t ≤ selectorAMajorant M :=
  Nat.add_le_add_right (Nat.mul_le_mul_left 200 ht) 8

theorem selectorEpsilon_magnitude {M A B : ℕ} {ε : ℝ}
    (hε : Magnitude M ε) (hA1 : 1 ≤ A) (hA : A ≤ B) :
    Magnitude (selectorEpsilonMajorant M B) (S07V27.selEps ε A) := by
  have hc : Magnitude 10000 (10000:ℝ) := Magnitude.natCast (by decide) le_rfl
  have ha : Magnitude B (A:ℝ) := Magnitude.natCast hA1 hA
  norm_num only [S07V27.selEps]
  exact ((clipped_magnitude hε).pow 2).div (hc.mul ha)

theorem selectorQ_le_majorant {M A B : ℕ} {ε : ℝ}
    (hε : Magnitude M ε) (hA1 : 1 ≤ A) (hA : A ≤ B) :
    selQLimit ε A ≤ selectorQMajorant M B := by
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have ha : Magnitude B (A:ℝ) := Magnitude.natCast hA1 hA
  exact Nat.add_le_add_right ((h4.mul ha).div (clipped_magnitude hε)).ceil_le 2

private theorem selector_inputs {M t : ℕ} {α q ε τ : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hε : Magnitude M ε)
    (hτ : Magnitude M τ) (ht : t ≤ M) :
    Magnitude (selectorScale M) (q*α/2) ∧ Magnitude (selectorScale M) (q/2) ∧
    Magnitude (selectorScale M) τ ∧ S07V27.selA t ≤ selectorScale M ∧
      selQLimit ε (S07V27.selA t) ≤ selectorScale M := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  refine ⟨((hq.mul hα).div h2).mono (by unfold selectorScale; omega),
    (hq.div h2).mono (by unfold selectorScale; omega),
    hτ.mono (by unfold selectorScale; omega),?_,?_⟩
  · exact (selectorA_le_majorant ht).trans (by unfold selectorScale; omega)
  · exact (selectorQ_le_majorant hε (by unfold S07V27.selA; omega) (selectorA_le_majorant ht)).trans
      (by unfold selectorScale; omega)

theorem selectorStock_magnitude {M t : ℕ} {α q ε : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hε : Magnitude M ε) (ht : t ≤ M) :
    Magnitude (selectorStockMajorant M) (selectorStockBudget α q ε t) := by
  obtain ⟨hk,hμ,_,_,_⟩ := selector_inputs hα hq hε hε ht
  exact (selectorEpsilon_magnitude hε (by unfold S07V27.selA; omega) (selectorA_le_majorant ht)).min
    (paymentForbidden_magnitude hk hμ)

theorem selectorInput_magnitude {M t : ℕ} {α q ε τ : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hε : Magnitude M ε)
    (hτ : Magnitude M τ) (ht : t ≤ M) :
    Magnitude (selectorInputMajorant M) (selectorInputBudget α q ε t τ) := by
  obtain ⟨hk,hμ,hτ',hA,hD⟩ := selector_inputs hα hq hε hτ ht
  exact (selectorEpsilon_magnitude hε (by unfold S07V27.selA; omega) (selectorA_le_majorant ht)).min
    (paymentInput_magnitude hk hμ hτ' hA hD)

theorem selectorOrder_le_majorant {M t : ℕ} {α q ε τ : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hε : Magnitude M ε)
    (hτ : Magnitude M τ) (ht : t ≤ M) : selectorOrder α q ε t τ ≤ selectorOrderMajorant M := by
  obtain ⟨hk,hμ,hτ',hA,hD⟩ := selector_inputs hα hq hε hτ ht
  have hc : Magnitude 200 (200:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact max_le_max (paymentOrder_le_majorant hk hμ hτ' hA hD)
    (hc.div (clipped_magnitude hε)).ceil_le

def forkEpsilonMajorant (M : ℕ) : ℕ := M^2*(1024*(M+1))
def forkQMajorant (M : ℕ) : ℕ := 128*M+1
def withdrawalKappaMajorant (M : ℕ) : ℕ := M*M*2
def withdrawalKMajorant (M : ℕ) : ℕ := forkQMajorant (withdrawalKappaMajorant M)+6
def withdrawalStockMajorant (M : ℕ) : ℕ :=
  max (forkEpsilonMajorant (withdrawalKappaMajorant M)) (selectorStockMajorant M*4)
def withdrawalInputMajorant (M : ℕ) : ℕ :=
  max (forkEpsilonMajorant (withdrawalKappaMajorant M))
    (max (max (selectorInputMajorant (2*M)) (M*2)*(4*withdrawalKMajorant M))
      (selectorStockMajorant M*(8*withdrawalKMajorant M)))
def withdrawalOrderMajorant (M : ℕ) : ℕ :=
  max (max (selectorOrderMajorant (2*M)) (32*withdrawalKappaMajorant M)) (withdrawalInputMajorant M)

theorem forkEpsilon_magnitude {M : ℕ} {κ : ℝ} (hκ : Magnitude M κ) :
    Magnitude (forkEpsilonMajorant M) (S07V26.forkEps κ) := by
  have hc : Magnitude 1024 (1024:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact (hκ.pow 2).div (hc.mul (hκ.add Magnitude.one))

theorem forkQ_le_majorant {M : ℕ} {κ : ℝ} (hκ : Magnitude M κ) : forkQLimit κ ≤ forkQMajorant M := by
  have hc : Magnitude 128 (128:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact Nat.add_le_add_right (hc.div hκ).ceil_le 1

theorem withdrawalStock_magnitude {M t : ℕ} {α q ε : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hε : Magnitude M ε) (ht : t ≤ M) :
    Magnitude (withdrawalStockMajorant M) (withdrawalStockBudget α q ε t) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact (forkEpsilon_magnitude ((hq.mul hα).div h2)).min ((selectorStock_magnitude hα hq hε ht).div h4)

theorem withdrawalInput_magnitude {M t : ℕ} {α q ε τ : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hε : Magnitude M ε)
    (hτ : Magnitude M τ) (ht : t ≤ M) :
    Magnitude (withdrawalInputMajorant M) (withdrawalInputBudget α q ε t τ) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h8 : Magnitude 8 (8:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hk := (hq.mul hα).div h2
  have hτ2 : Magnitude (2*M) (τ/2) := by simpa only [Nat.mul_comm] using hτ.div h2
  have hs := selectorInput_magnitude (hα.mono (by omega : M ≤ 2*M)) (hq.mono (by omega : M ≤ 2*M))
    (hε.mono (by omega : M ≤ 2*M)) hτ2 (by omega : t ≤ 2*M)
  have hK : Magnitude (withdrawalKMajorant M) ((forkQLimit (q*α/2)+6:ℕ):ℝ) :=
    Magnitude.natCast (by omega) (Nat.add_le_add_right (forkQ_le_majorant hk) 6)
  simpa only [withdrawalInputBudget,withdrawalInputMajorant,withdrawalKappaMajorant,Nat.cast_add,Nat.cast_ofNat] using
    (forkEpsilon_magnitude hk).min
      (((hs.min (hτ.div h2)).div (h4.mul hK)).min ((selectorStock_magnitude hα hq hε ht).div (h8.mul hK)))

theorem withdrawalOrder_le_majorant {M t : ℕ} {α q ε τ : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hε : Magnitude M ε)
    (hτ : Magnitude M τ) (ht : t ≤ M) : withdrawalOrder α q ε t τ ≤ withdrawalOrderMajorant M := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h32 : Magnitude 32 (32:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hτ2 : Magnitude (2*M) (τ/2) := by simpa only [Nat.mul_comm] using hτ.div h2
  exact max_le_max (max_le_max
    (selectorOrder_le_majorant (hα.mono (by omega : M ≤ 2*M)) (hq.mono (by omega : M ≤ 2*M))
      (hε.mono (by omega : M ≤ 2*M)) hτ2 (by omega : t ≤ 2*M))
    (h32.div ((hq.mul hα).div h2)).ceil_le) (withdrawalInput_magnitude hα hq hε hτ ht).inv.ceil_le

def resourceStockMajorant (M : ℕ) : ℕ := referenceAvoidBound (8*M)
def rawStockBudgetMajorant (M : ℕ) : ℕ := max (referenceStockBudgetBound M) (M*8)
def resourceTerminalMajorant (M : ℕ) : ℕ :=
  max (rawStockBudgetMajorant M) (max (withdrawalStockMajorant M) (M*M*16))
def resourceOutputMajorant (M : ℕ) : ℕ := max (M*M*16) M
def resourceInputScale (M : ℕ) : ℕ := M+resourceOutputMajorant M+1
def resourceInputMajorant (M : ℕ) : ℕ :=
  max (withdrawalInputMajorant (resourceInputScale M)*4) (max (resourceOutputMajorant M) M)
def resourceCompletionMajorant (M : ℕ) : ℕ :=
  M*2*(max (resourceInputMajorant M*12) 2)^2*2

theorem resourceStock_magnitude {M : ℕ} {α C : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) :
    Magnitude (resourceStockMajorant M) (resourceStockBudget α C) := by
  have h8 : Magnitude 8 (8:ℝ) := Magnitude.natCast (by decide) le_rfl
  have ha : Magnitude (8*M) (α/8) := by simpa only [Nat.mul_comm] using hα.div h8
  exact referenceAvoidBudget_magnitude (hC.inv.mono (by omega : M ≤ 8*M))
    (hC.mono (by omega : M ≤ 8*M)) ha

theorem rawStockBudget_magnitude {M h : ℕ} {a b α : ℝ}
    (ha : Magnitude M a) (hb : Magnitude M b) (hα : Magnitude M α) (hh : h ≤ M) :
    Magnitude (rawStockBudgetMajorant M) (rawStockBudget a b α h) := by
  have h8 : Magnitude 8 (8:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact (referenceStockBudget_magnitude ha hb hα hh).min (hα.div h8)

theorem resourceTerminal_magnitude {M h t : ℕ} {α C αW qW εW η : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hαW : Magnitude M αW)
    (hqW : Magnitude M qW) (hεW : Magnitude M εW) (hη : Magnitude M η)
    (hh : h ≤ M) (ht : t ≤ M) :
    Magnitude (resourceTerminalMajorant M) (resourceTerminalBudget α C h αW qW εW η t) := by
  have h16 : Magnitude 16 (16:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact (rawStockBudget_magnitude hC.inv hC hα hh).min
    ((withdrawalStock_magnitude hαW hqW hεW ht).min ((hη.mul hqW).div h16))

theorem resourceOutput_magnitude {M : ℕ} {qW η τcap : ℝ}
    (hq : Magnitude M qW) (hη : Magnitude M η) (hτ : Magnitude M τcap) :
    Magnitude (resourceOutputMajorant M) (resourceOutputBudget qW η τcap) := by
  have h16 : Magnitude 16 (16:ℝ) := Magnitude.natCast (by decide) le_rfl
  exact ((hη.mul hq).div h16).min hτ

theorem resourceInput_magnitude {M t : ℕ} {α q ε η ρ τ : ℝ}
    (hα : Magnitude M α) (hq : Magnitude M q) (hε : Magnitude M ε)
    (hη : Magnitude M η) (hρ : Magnitude M ρ) (hτ : Magnitude M τ) (ht : t ≤ M) :
    Magnitude (resourceInputMajorant M) (resourceInputBudget α q ε η t ρ τ) := by
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  let U := resourceInputScale M
  have hτ' := resourceOutput_magnitude hq hη hτ
  have hu : M ≤ U := by dsimp [U,resourceInputScale]; omega
  have hτU : Magnitude U (resourceOutputBudget q η τ) := hτ'.mono (by dsimp [U,resourceInputScale]; omega)
  exact ((withdrawalInput_magnitude (hα.mono hu) (hq.mono hu) (hε.mono hu) hτU (ht.trans hu)).div h4).min
    (hτ'.min hρ)

theorem resourceCompletion_magnitude {M t : ℕ} {α αW q ε η ρ τ : ℝ}
    (hα : Magnitude M α) (hαW : Magnitude M αW) (hq : Magnitude M q) (hε : Magnitude M ε)
    (hη : Magnitude M η) (hρ : Magnitude M ρ) (hτ : Magnitude M τ) (ht : t ≤ M) :
    Magnitude (resourceCompletionMajorant M) (resourceCompletion α αW q ε η t ρ τ) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h12 : Magnitude 12 (12:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hr := resourceInput_magnitude hαW hq hε hη hρ hτ ht
  have hRate := (hr.div h12).min (Magnitude.one.div h2)
  exact ((hα.div h2).mul (hRate.pow 2)).div h2

#print axioms paymentInput_magnitude
#print axioms withdrawalInput_magnitude
#print axioms resourceTerminal_magnitude
#print axioms resourceInput_magnitude
end TypedTriangle.TowerBounds
