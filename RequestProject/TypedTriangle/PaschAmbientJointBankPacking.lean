module
public import RequestProject.TypedTriangle.PaschJointBankLinearPacking
public import RequestProject.TypedTriangle.PaschAmbientRootedMonitor
public import RequestProject.TypedTriangle.PaschFloorMixedControl
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open WeightedStar LocalizedCover

/-- The actual normalized ambient monitor is carried by the same packing
as all moments, triangle statistics, pure Pasch and fixed-bank mixed tests.
Its linear quota is derived from H1/H3, including the empty-host branch. -/
theorem joint_packing_with_triangle_monitors_pasch_bank_and_ambient_test
    (C α η τ Λ σ ε : ℝ) (q L : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hη : 0 < η) (hτ : 0 < τ)
    (hΛ : 0 < Λ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (μ : Finset V → ℝ), N ≤ Fintype.card V → IsDiffuseSeed H F C μ →
      CommonNbrCond H F α →
      ∀ (X : Type) [Fintype X] (e : V ↪ X) (Rprev : Finset (Finset X)) (Lprev : ℕ),
      PairCodegreeBound Rprev Lprev → ∀ (κ ι ν : Type) [Fintype κ] [Fintype ι] [Fintype ν]
      (bad : κ → Finset V) (loc : κ → Sym2 V → ℝ) (full : ι → Sym2 V → ℝ)
      (w : ν → Finset V → ℝ),
      ((Fintype.card κ+Fintype.card ι+Fintype.card ν:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^q →
      (∀ k T, IsAllowed H F T → |triSum (loc k) T| ≤ 3*Λ*(T∩bad k).card) →
      (∀ k T, IsAllowed H F T → |triSum (full k) T| ≤ 3*Λ*T.card) →
      (∀ k T, IsAllowed H F T → |w k T| ≤ 1) →
      ∀ B : Finset (Finset V), PairCodegreeBound B L → (∀ T ∈ B, T.card = 3) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
        (∀ k, |edgeSum (loc k) (edges H\P.biUnion triEdges)| ≤ τ*Fintype.card V*(bad k).card) ∧
        (∀ k, |edgeSum (full k) (edges H\P.biUnion triEdges)| ≤ τ*(Fintype.card V:ℝ)^2) ∧
        (∀ k, |(∑ T ∈ P, w k T)-(∑ T ∈ allowed H F, μ T*w k T)| ≤
          τ*(Fintype.card V:ℝ)^2) ∧
        |(count P:ℝ)-target μ (allowed H F)| ≤ σ*(Fintype.card V:ℝ)^2 ∧
        (|(∑ T ∈ P, childPaddedWeight e Rprev Lprev T)-
           (∑ T ∈ allowed H F, μ T*childPaddedWeight e Rprev Lprev T)| ≤
          ε*(∑ T ∈ allowed H F, μ T*childPaddedWeight e Rprev Lprev T)) ∧
        ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 →
          let A := allowed H F
          let n := (Fintype.card V:ℝ)
          let θ := floorWeights A μ n
          |PatternStatistics.statistic (completionWeight B) ℓ P-mixedMass A B θ ℓ| ≤
            (n^2)^(-egj13Epsilon)*(2*(Nat.choose 4 ℓ:ℝ)*target θ A+mixedMass A B θ ℓ) := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let c := α^3/(54*C)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨N,hPack⟩ := joint_packing_with_triangle_monitors_pasch_bank_and_relative_tests
    C α η τ Λ σ c ε q L hC hα hη hτ hΛ hσ hc hε
  refine ⟨max N 1,?_⟩
  intro V I _ H F μ hn hH1 hH3 X _ e Rprev Lprev hPrev
    κ ι ν _ _ _ bad loc full w hcard hloc hfull hw B hL hB
  have hn1 : 1 ≤ Fintype.card V := by omega
  have hn0 : 0 < (Fintype.card V:ℝ) := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hW : ∀ (_k : Unit) T, 0 ≤ childPaddedWeight e Rprev Lprev T ∧
      childPaddedWeight e Rprev Lprev T ≤ 1 :=
    fun _ T => childPaddedWeight_bounds e Rprev Lprev hPrev hn1 T
  have hQuota : (∑ T ∈ allowed H F, μ T*childPaddedWeight e Rprev Lprev T) = 0 ∨
      c*Fintype.card V ≤ ∑ T ∈ allowed H F, μ T*childPaddedWeight e Rprev Lprev T := by
    rcases child_padded_target_lower_or_empty e Rprev Lprev hPrev hα
      hC0 hn0 hH1 hH3 with hEmpty | hPositive
    · exact Or.inl hEmpty.2
    · exact Or.inr hPositive
  have hUnit : Fintype.card Unit ≤ (Fintype.card V)^q := by
    change 1 ≤ (Fintype.card V)^q
    exact one_le_pow₀ hn1
  obtain ⟨P,hPsub,hP,hSparse,hLocal,hFull,hTriangles,hPasch,hRelative,hMixed⟩ :=
    hPack H F μ ((le_max_left _ _).trans hn) hH1 hH3 κ ι ν bad loc full w
      hcard hloc hfull hw B hL hB Unit (fun _ => childPaddedWeight e Rprev Lprev)
      hUnit hW (fun _ => hQuota)
  exact ⟨P,hPsub,hP,hSparse,hLocal,hFull,hTriangles,hPasch,hRelative (),hMixed⟩

#print axioms joint_packing_with_triangle_monitors_pasch_bank_and_ambient_test
end TypedTriangle.Pasch
