module
public import RequestProject.TypedTriangle.ApplicationsRainbowDefs
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Applications

theorem exists_balanced_signs (A : Type) [Fintype A] (hEven : Even (Fintype.card A)) :
    ∃ σ : A → ℝ, (∀ x,σ x=1 ∨ σ x= -1) ∧ (∑ x,σ x)=0 := by
  obtain ⟨m,hm⟩ := hEven
  obtain ⟨S,_,hS⟩ : ∃ S ⊆ (univ : Finset A),S.card=m :=
    exists_subset_card_eq (by rw [card_univ]; omega)
  let σ : A → ℝ := fun x => if x∈S then 1 else -1
  have hSign : ∀ x,σ x=1 ∨ σ x= -1 := by
    intro x
    by_cases hx : x∈S <;> simp [σ,hx]
  have hIndicator : (∑ x : A,if x∈S then (1:ℝ) else 0)=(S.card:ℝ) := by
    calc
      _ = ∑ x∈S,(1:ℝ) := by
        rw [←sum_filter]
        congr 1
        ext x
        simp
      _ = _ := by simp
  have hPoint (x : A) : σ x=2*(if x∈S then (1:ℝ) else 0)-1 := by
    by_cases hx : x∈S <;> norm_num [σ,hx]
  refine ⟨σ,hSign,?_⟩
  simp_rw [hPoint]
  rw [sum_sub_distrib,←mul_sum,hIndicator]
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,hS]
  have hmR : (Fintype.card A:ℝ)=(m:ℝ)+m := by exact_mod_cast hm
  linarith only [hmR]

#print axioms exists_balanced_signs
end TypedTriangle.Applications
