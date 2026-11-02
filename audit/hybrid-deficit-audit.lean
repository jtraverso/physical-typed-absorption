module
public import RequestProject.TypedTriangle.CompletionHybridDeficitCase

open Finset TypedTriangle.Completion
noncomputable section

example {I : Type} (s : Finset I) (u W N : I → ℝ) (B : ℝ)
    (hW : ∀ b ∈ s,W b=u b*N b) (hB : ∑ b ∈ s,W b=B) :
    B^2*(∑ b ∈ s,N b)-2*B^2+(∑ b ∈ s,u b*W b)=
      ∑ b ∈ s,N b*(B-u b)^2 :=
  HybridDeficit.moment_identity s u W N B hW hB

example {I : Type} (s : Finset I) (u W N : I → ℝ) (B : ℝ)
    (hBpos : 0 < B) (hN : ∀ b ∈ s,0 ≤ N b)
    (hW : ∀ b ∈ s,W b=u b*N b) (hB : ∑ b ∈ s,W b=B)
    (hReserve : B*(1-B) ≤ ∑ b ∈ s,(1-u b)*W b) :
    1 ≤ ∑ b ∈ s,N b :=
  HybridDeficit.normalization_closes_from_weighted_reserve s u W N B hBpos hN hW hB hReserve

example {I : Type} (s : Finset I) (u W N : I → ℝ)
    (B D K : ℝ) (hW : ∀ b ∈ s,W b=u b*N b)
    (hB : ∑ b ∈ s,W b=B) (hD : D=(∑ b ∈ s,N b)+K) :
    B^2*(D-1)=(∑ b ∈ s,(1-u b)*W b)+
      (∑ b ∈ s,N b*(B-u b)^2)+B^2*K-B*(1-B) :=
  HybridDeficit.full_deficit_identity s u W N B D K hW hB hD

end

#print axioms TypedTriangle.Completion.HybridDeficit.aggregate_data_do_not_force_target
#print axioms TypedTriangle.Completion.HybridDeficit.full_deficit_identity
#print axioms TypedTriangle.Completion.HybridDeficit.moment_identity
#print axioms TypedTriangle.Completion.HybridDeficit.normalization_closes_from_weighted_reserve
