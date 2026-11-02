module
public import RequestProject.TypedTriangle.ApplicationsLatinExtraction
public import RequestProject.TypedTriangle.MainPaperIIIPasch
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin.Completion

local instance {A : Type} : DecidableEq (Vertex A) := Classical.decEq _

/-- A partial Latin square represented by its pairwise edge-disjoint triples.
The labels are rows, columns and symbols; no completion is part of this data. -/
structure PartialLatin (A : Type) [Fintype A] where
  triangles : Finset (Finset (Vertex A))
  allowed : ∀ T ∈ triangles, IsAllowed (host A) types T
  disjoint : (triangles : Set (Finset (Vertex A))).PairwiseDisjoint triEdges

def used {A : Type} [Fintype A] (P : PartialLatin A) : Finset (Sym2 (Vertex A)) :=
  P.triangles.biUnion triEdges

def Dense {A : Type} [Fintype A] (P : PartialLatin A) (θ : ℝ) : Prop :=
  ∀ v : Vertex A, ((P.triangles.filter (fun T => v ∈ T)).card : ℝ) ≤ θ*Fintype.card A

def residual {A : Type} [Fintype A] (P : PartialLatin A) : Host (Vertex A) (Fin 3) where
  G := {
    Adj := fun u v => (host A).G.Adj u v ∧ s(u,v) ∉ used P
    symm := ⟨by intro u v h; exact ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2⟩⟩
    loopless := ⟨by intro v h; exact h.1 rfl⟩ }
  lab := (host A).lab

theorem residual_edges {A : Type} [Fintype A] (P : PartialLatin A) :
    edges (residual P)=edges (host A) \ used P := by
  ext e
  refine Sym2.inductionOn e ?_
  intro u v
  simp [edges,residual]

theorem residual_allowed {A : Type} [Fintype A] (P : PartialLatin A)
    (T : Finset (Vertex A)) (hT : IsAllowed (residual P) types T) :
    IsAllowed (host A) types T :=
  ⟨hT.1,fun u hu v hv hne => (hT.2.1 u hu v hv hne).1,hT.2.2⟩

theorem used_subset {A : Type} [Fintype A] (P : PartialLatin A) : used P ⊆ edges (host A) := by
  intro e he
  obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
  refine Sym2.inductionOn e ?_ heT
  intro u v huv
  obtain ⟨hu,hv,hne⟩ := mem_triEdges.mp huv
  have hh := (P.allowed T hT).2.1 u hu v hv hne
  simpa [edges] using hh

theorem merge_residual {A : Type} [Fintype A] (P : PartialLatin A)
    {D : Finset (Finset (Vertex A))}
    (hD : IsDecomposition (residual P) types (edges (residual P)) D) :
    IsDecomposition (host A) types (edges (host A)) (P.triangles ∪ D) := by
  have hCross : ∀ T ∈ P.triangles, ∀ U ∈ D, Disjoint (triEdges T) (triEdges U) := by
    intro T hT U hU
    apply disjoint_left.mpr
    intro e heT heU
    have heUsed : e ∈ used P := mem_biUnion.mpr ⟨T,hT,heT⟩
    have heRes := hD.subset hU heU
    rw [residual_edges] at heRes
    exact (mem_sdiff.mp heRes).2 heUsed
  refine ⟨?_,?_,?_⟩
  · intro T hT
    rcases mem_union.mp hT with hT | hT
    · exact P.allowed T hT
    · exact residual_allowed P T (hD.1 T hT)
  · intro T hT U hU hne
    rcases mem_union.mp hT with hT | hT <;> rcases mem_union.mp hU with hU | hU
    · exact P.disjoint hT hU hne
    · exact hCross T hT U hU
    · exact (hCross U hU T hT).symm
    · exact hD.2.1 hT hU hne
  · rw [union_biUnion,hD.2.2,residual_edges]
    change used P ∪ (edges (host A) \ used P)=edges (host A)
    exact union_sdiff_of_subset (used_subset P)

/-- Explicit verification interface for connecting Lean Pool / Palomar.
These fields are theorem inputs, not declarations of global axioms.
In particular `seed` and the two geometry fields remain visible obligations:
the present module does not claim to derive them from the cited papers.
`seed` precedes every test family, as required by the original T. -/
structure ResidualVerificationInputs (θ C : ℝ) where
  threshold : ℕ
  seed : ∀ (A : Type) [Fintype A] (P : PartialLatin A),
    threshold ≤ Fintype.card A → Dense P θ →
    ∃ μ : Finset (Vertex A) → ℝ, IsDiffuseSeed (residual P) types C μ
  physical : ∀ (A : Type) [Fintype A] (P : PartialLatin A),
    threshold ≤ Fintype.card A → Dense P θ → IsPhysical (residual P) types (edges (residual P))
  common : ∀ (A : Type) [Fintype A] (P : PartialLatin A),
    threshold ≤ Fintype.card A → Dense P θ → CommonNbrCond (residual P) types (1/2000)
  hinge : ∀ (A : Type) [Fintype A] (P : PartialLatin A),
    threshold ≤ Fintype.card A → Dense P θ → HingeCond (residual P) types (1/2000) 6

private theorem pasch_change_decEq {V : Type} (D U : Finset (Finset V))
    (μ : Finset V → ℝ) (ε : ℝ) (d₁ d₂ : DecidableEq V)
    (h : |(@Pasch.count V d₁ D : ℝ)-@Pasch.target V d₁ μ U| ≤ ε) :
    |(@Pasch.count V d₂ D : ℝ)-@Pasch.target V d₂ μ U| ≤ ε := by
  cases Subsingleton.elim d₁ d₂
  exact h

/-- Conditional application with preservation of the partial square, a seed
chosen before the tests, signed statistics, and the original residual Pasch
target. It counts four-new-entry intercalates, not mixed intercalates. -/
theorem partial_latin_completion_with_statistics (θ C η : ℝ) (q : ℕ)
    (hC : 1 ≤ C) (hη : 0 < η) (inputs : ResidualVerificationInputs θ C) :
    ∃ N : ℕ, ∀ (A : Type) [Fintype A] (P : PartialLatin A),
      N ≤ Fintype.card A → Dense P θ →
      ∃ μ : Finset (Vertex A) → ℝ, IsDiffuseSeed (residual P) types C μ ∧
        ∀ (ν : Type) [Fintype ν] (w : ν → Finset (Vertex A) → ℝ),
          (Fintype.card ν : ℝ) ≤ (Fintype.card A : ℝ)^q →
          (∀ k T, IsAllowed (residual P) types T → |w k T| ≤ 1) →
          ∃ (L : LatinSquare A) (D : Finset (Finset (Vertex A))),
            decomposition L=P.triangles ∪ D ∧ P.triangles ⊆ decomposition L ∧
            IsDecomposition (residual P) types (edges (residual P)) D ∧
            (∀ k, |(∑ T ∈ D,w k T)-(∑ T ∈ allowed (residual P) types,μ T*w k T)| ≤
              η*(Fintype.card A : ℝ)^2) ∧
            |(Pasch.count D : ℝ)-Pasch.target μ (allowed (residual P) types)| ≤
              η*(Fintype.card A : ℝ)^2 := by
  obtain ⟨n₀,hMain⟩ := Vortex.main_theorem_T_with_triangle_monitors_and_pasch
    types (1/2000) C (η/9) 6 q (by norm_num) hC (by norm_num) (by positivity)
  refine ⟨max inputs.threshold n₀,?_⟩
  intro A _ P hn hDense
  have hnInput : inputs.threshold ≤ Fintype.card A := (le_max_left _ _).trans hn
  obtain ⟨μ,hSeed⟩ := inputs.seed A P hnInput hDense
  refine ⟨μ,hSeed,?_⟩
  intro ν _ w hν hw
  have hnHost : n₀ ≤ Fintype.card (Vertex A) := by
    rw [Fintype.card_prod,Fintype.card_fin]
    have hh := (le_max_right inputs.threshold n₀).trans hn
    omega
  have hTests : (Fintype.card ν : ℝ) ≤ (Fintype.card (Vertex A) : ℝ)^q := by
    apply hν.trans
    rw [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    gcongr
    have hh : (0:ℝ) ≤ Fintype.card A := Nat.cast_nonneg _
    linarith
  obtain ⟨D,hD,hStats,hPasch⟩ := hMain (residual P) μ hnHost hSeed
    (inputs.physical A P hnInput hDense) (inputs.common A P hnInput hDense)
    (inputs.hinge A P hnInput hDense) ν w hTests hw
  let L := ofDecomposition (merge_residual P hD)
  have hLD : decomposition L=P.triangles ∪ D := decomposition_ofDecomposition _
  have hScale : η/9*(Fintype.card (Vertex A) : ℝ)^2=η*(Fintype.card A : ℝ)^2 := by
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    ring
  refine ⟨L,D,hLD,?_,hD,?_,?_⟩
  · rw [hLD]; exact subset_union_left
  · intro k; exact (hStats k).trans_eq hScale
  · exact pasch_change_decEq D (allowed (residual P) types) μ
      (η*(Fintype.card A : ℝ)^2) (Classical.decEq _) (inferInstance)
      (hPasch.trans_eq hScale)

#print axioms merge_residual
#print axioms partial_latin_completion_with_statistics
end TypedTriangle.Applications.Latin.Completion
