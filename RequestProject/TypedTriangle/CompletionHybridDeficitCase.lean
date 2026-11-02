module
public import RequestProject.TypedTriangle.CompletionHybridUniversalReduction
@[expose] public section
open Finset
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Completion.HybridDeficit

/-- Weighted variance at the original weighted receipt B. Here W=u*N;
the theorem is an algebraic identity, not a new graph hypothesis. -/
theorem moment_identity {I : Type} (s : Finset I) (u W N : I → ℝ) (B : ℝ)
    (hW : ∀ b ∈ s,W b=u b*N b) (hB : ∑ b ∈ s,W b=B) :
    B^2*(∑ b ∈ s,N b)-2*B^2+(∑ b ∈ s,u b*W b)=
      ∑ b ∈ s,N b*(B-u b)^2 := by
  have hp : ∀ b ∈ s,N b*(B-u b)^2=B^2*N b-2*B*W b+u b*W b := by
    intro b hb
    rw [hW b hb]
    ring
  rw [sum_congr rfl hp]
  simp only [sum_add_distrib,sum_sub_distrib,←mul_sum,hB]
  ring

/-- Sufficient condition for the pending case. The reserve bound is NOT
claimed to follow from all admissible graphs; it remains an explicit condition. -/
theorem normalization_closes_from_weighted_reserve {I : Type}
    (s : Finset I) (u W N : I → ℝ) (B : ℝ)
    (hBpos : 0 < B) (hN : ∀ b ∈ s,0 ≤ N b)
    (hW : ∀ b ∈ s,W b=u b*N b) (hB : ∑ b ∈ s,W b=B)
    (hReserve : B*(1-B) ≤ ∑ b ∈ s,(1-u b)*W b) :
    1 ≤ ∑ b ∈ s,N b := by
  have hid := moment_identity s u W N B hW hB
  have hnon : 0 ≤ ∑ b ∈ s,N b*(B-u b)^2 :=
    sum_nonneg fun b hb => mul_nonneg (hN b hb) (sq_nonneg _)
  have hs : (∑ b ∈ s,(1-u b)*W b)=B-(∑ b ∈ s,u b*W b) := by
    simp only [sub_mul,one_mul,sum_sub_distrib,hB]
  rw [hs] at hReserve
  have hsq : 0 < B^2 := sq_pos_of_pos hBpos
  by_contra h
  have hh : (∑ b ∈ s,N b) < 1 := lt_of_not_ge h
  have hneg := mul_neg_of_pos_of_neg hsq (sub_neg.mpr hh)
  nlinarith only [hid,hnon,hReserve,hneg]

/-- Exact remaining obstruction, including normalization variance and
switching gain. No lower bound for its right-hand side is assumed. -/
theorem full_deficit_identity {I : Type} (s : Finset I) (u W N : I → ℝ)
    (B D K : ℝ) (hW : ∀ b ∈ s,W b=u b*N b)
    (hB : ∑ b ∈ s,W b=B) (hD : D=(∑ b ∈ s,N b)+K) :
    B^2*(D-1)=(∑ b ∈ s,(1-u b)*W b)+
      (∑ b ∈ s,N b*(B-u b)^2)+B^2*K-B*(1-B) := by
  have hid := moment_identity s u W N B hW hB
  have hs : (∑ b ∈ s,(1-u b)*W b)=B-(∑ b ∈ s,u b*W b) := by
    simp only [sub_mul,one_mul,sum_sub_distrib,hB]
  rw [hs,hD]
  nlinarith only [hid]

/-- Aggregate sender budgets, normalization and the near-unit floor alone
do not imply the target. This is NOT a counterexample to an admissible graph. -/
theorem aggregate_data_do_not_force_target :
    ∃ L p₁ p₂ q₁ q₂ capacity : ℝ,
      L=(28992529/29000000 : ℝ) ∧
      0 < L ∧ L < 1 ∧
      0 ≤ p₁ ∧ 0 ≤ p₂ ∧ 0 ≤ q₁ ∧ 0 ≤ q₂ ∧
      p₁+p₂=capacity ∧ q₁+q₂=capacity ∧
      capacity=2 ∧ L ≤ p₁ ∧ L ≤ p₂ ∧
      q₁=p₁ ∧ q₂=p₂ ∧ max p₁ q₁ < 1 := by
  refine ⟨28992529/29000000,28992529/29000000,
    2-28992529/29000000,28992529/29000000,2-28992529/29000000,2,?_⟩
  norm_num

end TypedTriangle.Completion.HybridDeficit
