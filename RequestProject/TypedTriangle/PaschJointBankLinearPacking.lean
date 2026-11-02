module
public import RequestProject.TypedTriangle.PaschRelativeTupleControl
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

/-- One packing controls the fixed bank and positive linear monitors.
The linear quota is a condition on the monitor, to be discharged for the
ambient padded monitor by its host theorem. No second nibble is used. -/
theorem joint_packing_with_triangle_monitors_pasch_bank_and_relative_tests
    (C α η τ Λ σ c ε : ℝ) (q L : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hη : 0 < η) (hτ : 0 < τ)
    (hΛ : 0 < Λ) (hσ : 0 < σ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (μ : Finset V → ℝ), N ≤ Fintype.card V → IsDiffuseSeed H F C μ →
      CommonNbrCond H F α → ∀ (κ ι ν : Type) [Fintype κ] [Fintype ι] [Fintype ν]
      (bad : κ → Finset V) (loc : κ → Sym2 V → ℝ) (full : ι → Sym2 V → ℝ)
      (w : ν → Finset V → ℝ),
      ((Fintype.card κ+Fintype.card ι+Fintype.card ν:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^q →
      (∀ k T, IsAllowed H F T → |triSum (loc k) T| ≤ 3*Λ*(T∩bad k).card) →
      (∀ k T, IsAllowed H F T → |triSum (full k) T| ≤ 3*Λ*T.card) →
      (∀ k T, IsAllowed H F T → |w k T| ≤ 1) →
      ∀ B : Finset (Finset V), PairCodegreeBound B L → (∀ T ∈ B, T.card = 3) →
      ∀ (ξ : Type) [Fintype ξ] (W : ξ → Finset V → ℝ),
      Fintype.card ξ ≤ (Fintype.card V)^q →
      (∀ k T, 0 ≤ W k T ∧ W k T ≤ 1) →
      (∀ k, (∑ T ∈ allowed H F, μ T*W k T) = 0 ∨
        c*Fintype.card V ≤ ∑ T ∈ allowed H F, μ T*W k T) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
        (∀ k, |edgeSum (loc k) (edges H\P.biUnion triEdges)| ≤ τ*Fintype.card V*(bad k).card) ∧
        (∀ k, |edgeSum (full k) (edges H\P.biUnion triEdges)| ≤ τ*(Fintype.card V:ℝ)^2) ∧
        (∀ k, |(∑ T ∈ P, w k T)-(∑ T ∈ allowed H F, μ T*w k T)| ≤
          τ*(Fintype.card V:ℝ)^2) ∧
        |(count P:ℝ)-target μ (allowed H F)| ≤ σ*(Fintype.card V:ℝ)^2 ∧
        (∀ k, |(∑ T ∈ P, W k T)-(∑ T ∈ allowed H F, μ T*W k T)| ≤
          ε*(∑ T ∈ allowed H F, μ T*W k T)) ∧
        ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 →
          let A := allowed H F
          let n := (Fintype.card V:ℝ)
          let θ := floorWeights A μ n
          |PatternStatistics.statistic (completionWeight B) ℓ P-mixedMass A B θ ℓ| ≤
            (n^2)^(-egj13Epsilon)*(2*(Nat.choose 4 ℓ:ℝ)*target θ A+mixedMass A B θ ℓ) := by
  obtain ⟨nJoint,hJoint⟩ := joint_packing_with_triangle_monitors_pasch_and_tuple_tests
    C α η τ Λ σ (q+2) hC hα hη hτ hΛ hσ
  obtain ⟨nNum,hnNum,hNum⟩ := exists_egj13_square_order C c (ε/2) 0 0 hc (by positivity)
  refine ⟨max nJoint (max 2 (max (mixedEligibilityOrder α C L)
    (max nNum ⌈4/c^2⌉₊))),?_⟩
  intro V I _ H F μ hn hH1 hH3 κ ι ν _ _ _ bad loc full w hcard hloc hfull hw B hL hB
    ξ _ W hξ hW hMass
  have hn2 : 2 ≤ Fintype.card V := by omega
  have hn1 : 1 ≤ Fintype.card V := by omega
  have hn0 : 0 < (Fintype.card V:ℝ) := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hnNum' : nNum ≤ Fintype.card V := by omega
  obtain ⟨_,_,_,_,_,hρ,hRound,_,hRatio⟩ := hNum (Fintype.card V) hnNum'
  have hSqrt : Real.sqrt (Fintype.card V:ℝ) ≤ c*Fintype.card V/2 := by
    apply sqrt_le_linear_of_order hc hn0
    exact (Nat.le_ceil (4/c^2)).trans (by exact_mod_cast (show ⌈4/c^2⌉₊ ≤ Fintype.card V by omega))
  have hCard' : ((Fintype.card κ+Fintype.card ι+Fintype.card ν:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^(q+2) :=
    hcard.trans (pow_le_pow_right₀ (by exact_mod_cast hn1) (by omega))
  have hExtra : Fintype.card (Bool ⊕ ξ) ≤ (Fintype.card V)^(q+2) := by
    let n := Fintype.card V
    have hN : n ≤ n^(q+1) := le_self_pow₀ hn1 (by omega)
    have hPower : n^q ≤ n^(q+1) := pow_le_pow_right₀ hn1 (Nat.le_succ q)
    have hξPower : Fintype.card ξ ≤ n^(q+1) := (show Fintype.card ξ ≤ n^q from hξ).trans hPower
    have hTwo : 2 ≤ n^(q+1) := hn2.trans hN
    calc
      Fintype.card (Bool ⊕ ξ) = 2+Fintype.card ξ := by simp
      _ ≤ n^(q+1)+n^(q+1) := Nat.add_le_add hTwo hξPower
      _ = 2*n^(q+1) := by omega
      _ ≤ n*n^(q+1) := Nat.mul_le_mul_right _ hn2
      _ = n^((q+1)+1) := (pow_succ' n (q+1)).symm
      _ = n^(q+2) := congrArg (fun k : ℕ => n^k) (by omega)
  let A := allowed H F
  let n := (Fintype.card V:ℝ)
  let X : ℕ → Bool ⊕ ξ → Finset (Finset V) → ℝ := fun ℓ =>
    Sum.elim (fun k => paddedFloorWeight A (if k then B else ∅) μ n)
      (fun k => if ℓ = 1 then WeightedClone.linearTupleWeight (W k) else fun _ => 0)
  have hX : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k S, 0 ≤ X ℓ k S := by
    intro ℓ _ _ k S
    rcases k with k | k
    · exact paddedCompletionWeight_nonneg A (if k then B else ∅) (floorWeights A μ n)
        (fun T _ => floorWeights_nonneg A μ n T) S
    · dsimp only [X,Sum.elim_inr]
      split_ifs
      · exact sum_nonneg (fun T _ => (hW k T).1)
      · exact le_rfl
  obtain ⟨P,hPsub,hP,hSparse,hLocal,hFull,hTriangles,hPasch,hControls⟩ :=
    hJoint H F μ ((le_max_left _ _).trans hn) hH1 hH3 κ ι ν bad loc full w
      hCard' hloc hfull hw (Bool ⊕ ξ) X hExtra hX
  refine ⟨P,hPsub,hP,hSparse,hLocal,hFull,hTriangles,hPasch,?_,?_⟩
  · intro k
    have hControl : floorTupleTestControl A μ P (WeightedClone.linearTupleWeight (W k)) 1 := by
      simpa [X] using hControls 1 (by omega) (by omega) (Sum.inr k)
    have hh := relative_error_of_floor_linear_control hH1
      (lt_of_lt_of_le zero_lt_one hC) hc (show 0 ≤ ε/2 by positivity)
      hn0 hRound hSqrt hρ hRatio P (W k) (hW k) (hMass k) hControl
    convert hh using 1 <;> ring
  · intro ℓ hℓ1 hℓ3
    exact mixed_floor_error_of_test_controls hH1 hH3 hα hC L
      (by omega) B P hL hB ℓ hℓ1 hℓ3
      (by simpa [X, A, n] using hControls ℓ hℓ1 (by omega) (Sum.inl false))
      (by simpa [X, A, n] using hControls ℓ hℓ1 (by omega) (Sum.inl true))

#print axioms joint_packing_with_triangle_monitors_pasch_bank_and_relative_tests
end TypedTriangle.Pasch
