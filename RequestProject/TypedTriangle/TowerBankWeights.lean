module
public import RequestProject.TypedTriangle.TowerGeometryPreparation
public import RequestProject.TypedTriangle.ExplicitPhysicalMonitorWeights
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.TowerBounds
open CoreMonitor.Explicit CatalogNative.Explicit

def deletedExtensionMajorant (M : ℕ) : ℕ :=
  let D := compDMajorant (M+1) (compressionSampleMajorant M)
  natExtensionCost (physicalRankMajorant M) D (3*D) (3*routeDMajorant M)
def physicalGlueMajorant (M : ℕ) : ℕ := deletedExtensionMajorant M+1
def physicalGlueOrderMajorant (M : ℕ) : ℕ :=
  max (max (compressionOrderMajorant M) (max (routeOrderMajorant M) (3*M+1))) (3*M+1)
def physicalWeightMajorant (M : ℕ) : ℕ :=
  max ((1+4*(6*M^2+1))*physicalGlueMajorant M*(M*(M*M))) (M*(M*M))+1
def nativeWeightOrderMajorant (M : ℕ) : ℕ := 4*physicalGlueOrderMajorant (2*M)*M+1

theorem deletedExtensionCost_le_majorant {M h : ℕ} {α β : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hh : h ≤ M) :
    deletedExtensionCost α β h ≤ (deletedExtensionMajorant M:ℝ) := by
  have hS := compressionSampleSize_le_majorant hα hh
  have hD := compD_le_majorant (clipped_magnitude hα) hS
  have hR := Nat.mul_le_mul_left 3 (routeD_le_majorant hβ)
  have hd := physicalRank_le_majorant hα hh
  unfold deletedExtensionCost
  rw [extensionCost_eq_nat]
  exact_mod_cast natExtensionCost_mono hd hD (Nat.mul_le_mul_left 3 hD) hR

theorem physicalGlueCost_magnitude {M h : ℕ} {α β : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hh : h ≤ M) :
    Magnitude (physicalGlueMajorant M) (physicalGlueCost α β h) := by
  have hb := deletedExtensionCost_le_majorant hα hβ hh
  have hz := deletedExtensionCost_nonneg α β h
  have hOne : 1 ≤ physicalGlueCost α β h := by unfold physicalGlueCost; linarith only [hz]
  refine ⟨lt_of_lt_of_le zero_lt_one hOne,?_,?_⟩
  · change deletedExtensionCost α β h+1 ≤ ((deletedExtensionMajorant M+1:ℕ):ℝ)
    push_cast
    linarith only [hb]
  · have hi : 1/physicalGlueCost α β h ≤ (1:ℝ) := by
      simpa only [div_one] using one_div_le_one_div_of_le one_pos hOne
    exact hi.trans (by exact_mod_cast (by unfold physicalGlueMajorant; omega : 1 ≤ physicalGlueMajorant M))

theorem physicalGlueOrder_le_majorant {M h : ℕ} {α β : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hh : h ≤ M) :
    physicalGlueOrder α β h ≤ physicalGlueOrderMajorant M := by
  have h3 : Magnitude 3 (3:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hn : S07V25.n1Of β ≤ 3*M+1 := Nat.add_le_add_right (h3.div hβ).ceil_le 1
  exact max_le_max (max_le_max (compressionOrder_le_majorant hα hh)
    (max_le_max (routeOrder_le_majorant hβ hh) hn)) hn

theorem physicalWeight_magnitude {M h d c K : ℕ} {α β : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hh : h ≤ M)
    (hd : d ≤ M) (hc : c ≤ M) (hK : K ≤ M) :
    Magnitude (physicalWeightMajorant M) (physicalWeightMagnitude α β h d c K) := by
  let A : ℝ := (K*(d*c):ℕ)
  have hA : A ≤ ((M*(M*M):ℕ):ℝ) := by
    dsimp only [A]
    exact_mod_cast Nat.mul_le_mul hK (Nat.mul_le_mul hd hc)
  have hA0 : 0 ≤ A := Nat.cast_nonneg _
  have h1 := Magnitude.one
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h6 : Magnitude 6 (6:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hf := h1.add (h4.mul ((h6.div (hβ.pow 2)).add h1))
  have hfUpper : 1+4*(6/β^2+1) ≤ 1+4*(6*(M:ℝ)^2+1) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat] using hf.upper
  have hB := physicalGlueCost_magnitude hα hβ hh
  have hProduct0 : 0 ≤ physicalGlueCost α β h*A := mul_nonneg hB.pos.le hA0
  have hAR : A ≤ (M:ℝ)*(M*M) := by simpa only [Nat.cast_mul] using hA
  have hg : S07V39.glueConst β (physicalGlueCost α β h*A) ≤
      (((1+4*(6*M^2+1))*physicalGlueMajorant M*(M*(M*M)):ℕ):ℝ) := by
    push_cast
    change (1+4*(6/β^2+1))*(physicalGlueCost α β h*A) ≤ _
    calc _ ≤ (1+4*(6*(M:ℝ)^2+1))*(physicalGlueMajorant M*((M*(M*M):ℕ):ℝ)) := by
           gcongr <;> first | exact hfUpper | exact hB.upper | exact hAR | exact hProduct0
         _ = _ := by push_cast; ring
  have hOne : 1 ≤ physicalWeightMagnitude α β h d c K := by
    change 1 ≤ max (S07V39.glueConst β (physicalGlueCost α β h*A)) A+1
    have hz : 0 ≤ max (S07V39.glueConst β (physicalGlueCost α β h*A)) A := hA0.trans (le_max_right _ _)
    linarith only [hz]
  refine ⟨lt_of_lt_of_le zero_lt_one hOne,?_,?_⟩
  · have hTop : max (S07V39.glueConst β (physicalGlueCost α β h*A)) A ≤
        (physicalWeightMajorant M:ℝ)-1 := by
      simpa only [physicalWeightMajorant,Nat.cast_add,Nat.cast_max,Nat.cast_one,add_sub_cancel_right] using max_le_max hg hA
    change max (S07V39.glueConst β (physicalGlueCost α β h*A)) A+1 ≤ _
    linarith only [hTop]
  · have hi : 1/physicalWeightMagnitude α β h d c K ≤ (1:ℝ) := by
      simpa only [div_one] using one_div_le_one_div_of_le one_pos hOne
    exact hi.trans (by exact_mod_cast (by unfold physicalWeightMajorant; omega : 1 ≤ physicalWeightMajorant M))

theorem nativeWeightOrder_le_majorant {M h : ℕ} {α β q : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hq : Magnitude M q) (hh : h ≤ M) :
    nativeWeightOrder α β q h ≤ nativeWeightOrderMajorant M := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have ha : Magnitude (2*M) (α/2) := by simpa only [Nat.mul_comm] using hα.div h2
  have hb : Magnitude (2*M) (β/2) := by simpa only [Nat.mul_comm] using hβ.div h2
  have hn : (physicalGlueOrder (α/2) (β/2) h:ℝ) ≤ physicalGlueOrderMajorant (2*M) := by
    exact_mod_cast physicalGlueOrder_le_majorant ha hb (by omega : h ≤ 2*M)
  have hq0 := hq.pos
  have hr : 4*(physicalGlueOrder (α/2) (β/2) h:ℝ)/q ≤
      ((4*physicalGlueOrderMajorant (2*M)*M:ℕ):ℝ) := by
    push_cast
    calc _ = 4*(physicalGlueOrder (α/2) (β/2) h:ℝ)*(1/q) := by ring
      _ ≤ 4*physicalGlueOrderMajorant (2*M)*M := by gcongr; exact hq.inv_upper
  exact Nat.add_le_add_right (Nat.ceil_le.mpr hr) 1

#print axioms physicalWeight_magnitude
#print axioms nativeWeightOrder_le_majorant
end TypedTriangle.TowerBounds
