module
public import RequestProject.TypedTriangle.PaschJointTuplePacking
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

/-- The actual joint packing controls its mixed Pasch interactions with a
fixed bank. Eligibility of both padded tests is discharged from H1/H3 and
the bank's incidence certificate; no test provider or mass premise remains.
The internal count of the bank itself is a separate architecture obligation. -/
theorem joint_packing_with_triangle_monitors_pasch_and_bank
    (C α η τ Λ σ : ℝ) (q L : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hη : 0 < η) (hτ : 0 < τ)
    (hΛ : 0 < Λ) (hσ : 0 < σ) :
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
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
        (∀ k, |edgeSum (loc k) (edges H\P.biUnion triEdges)| ≤ τ*Fintype.card V*(bad k).card) ∧
        (∀ k, |edgeSum (full k) (edges H\P.biUnion triEdges)| ≤ τ*(Fintype.card V:ℝ)^2) ∧
        (∀ k, |(∑ T ∈ P, w k T)-(∑ T ∈ allowed H F, μ T*w k T)| ≤
          τ*(Fintype.card V:ℝ)^2) ∧
        |(count P:ℝ)-target μ (allowed H F)| ≤ σ*(Fintype.card V:ℝ)^2 ∧
        ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 →
          let A := allowed H F
          let n := (Fintype.card V:ℝ)
          let θ := floorWeights A μ n
          |PatternStatistics.statistic (completionWeight B) ℓ P-mixedMass A B θ ℓ| ≤
            (n^2)^(-egj13Epsilon)*(2*(Nat.choose 4 ℓ:ℝ)*target θ A+mixedMass A B θ ℓ) := by
  obtain ⟨nJoint,hJoint⟩ := joint_packing_with_triangle_monitors_pasch_and_tuple_tests
    C α η τ Λ σ (q+1) hC hα hη hτ hΛ hσ
  refine ⟨max nJoint (max 2 (mixedEligibilityOrder α C L)),?_⟩
  intro V I _ H F μ hn hH1 hH3 κ ι ν _ _ _ bad loc full w hcard hloc hfull hw B hL hB
  have hn2 : 2 ≤ Fintype.card V := by omega
  have hn1 : 1 ≤ Fintype.card V := by omega
  have hCard' : ((Fintype.card κ+Fintype.card ι+Fintype.card ν:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^(q+1) :=
    hcard.trans (pow_le_pow_right₀ (by exact_mod_cast hn1) (Nat.le_succ q))
  have hBool : Fintype.card Bool ≤ (Fintype.card V)^(q+1) := by
    calc
      Fintype.card Bool = 2 := by decide
      _ ≤ Fintype.card V := hn2
      _ ≤ (Fintype.card V)^(q+1) := le_self_pow₀ hn1 (by omega)
  let A := allowed H F
  let n := (Fintype.card V:ℝ)
  let X : ℕ → Bool → Finset (Finset V) → ℝ := fun _ k =>
    paddedFloorWeight A (if k then B else ∅) μ n
  have hX : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k S, 0 ≤ X ℓ k S := by
    intro ℓ _ _ k S
    exact paddedCompletionWeight_nonneg A (if k then B else ∅) (floorWeights A μ n)
      (fun T _ => floorWeights_nonneg A μ n T) S
  obtain ⟨P,hPsub,hP,hSparse,hLocal,hFull,hTriangles,hPasch,hControls⟩ :=
    hJoint H F μ ((le_max_left _ _).trans hn) hH1 hH3 κ ι ν bad loc full w
      hCard' hloc hfull hw Bool X hBool hX
  refine ⟨P,hPsub,hP,hSparse,hLocal,hFull,hTriangles,hPasch,?_⟩
  intro ℓ hℓ1 hℓ3
  exact mixed_floor_error_of_test_controls hH1 hH3 hα hC L
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn)) B P hL hB ℓ hℓ1 hℓ3
      (by simpa [X, A, n] using hControls ℓ hℓ1 (by omega) false)
      (by simpa [X, A, n] using hControls ℓ hℓ1 (by omega) true)

#print axioms joint_packing_with_triangle_monitors_pasch_and_bank
end TypedTriangle.Pasch
