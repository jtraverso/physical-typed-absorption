module
public import RequestProject.TypedTriangle.PaschCoverDownFixedUniverseWindow
public import RequestProject.TypedTriangle.BasalStockEntry
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.StockEntry
open BasalIncidence
variable {V I : Type*} [Fintype V]

/-- The original stock-entry operation, using the actual basal-incidence
candidates, with a Pasch increment bound against the fixed previous universe. -/
theorem enter_stock_native_with_fixed_universe_pasch {H : Host V I} {F : Set (Multiset I)}
    {D P0 : Finset (Finset V)} {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η)
    (hP0 : IsPacking H F P0)
    (Rfixed : Finset (Finset V)) (hP0fixed : P0 ⊆ Rfixed)
    (L : ℕ) (hL : Pasch.PairCodegreeBound Rfixed L)
    (J : Finset (Sym2 V)) (hJH : J ⊆ edges H) (hXJ : cover D ⊆ J)
    (hProtected : Disjoint (P0.biUnion triEdges) J)
    (hphys : IsPhysical H F J)
    (hSupply : ∀ u v, s(u,v) ∈ J\cover D → H.G.Adj u v →
      κ*Fintype.card V ≤ (good H F D u v).card) {d : ℕ}
    (hdeg : ∀ x, ((J\cover D).filter (fun e => x ∈ e)).card ≤ d)
    (hOrder : Explicit.coverDownOrder κ η ≤ Fintype.card V)
    (hCard : (J\cover D).card ≤ Fintype.card V*d)
    (hSparse : (d : ℝ) ≤ Explicit.coverDownBudget κ η*Fintype.card V) :
    ∃ C : Finset (Finset V), IsPacking H F C ∧ IsPacking H F (P0∪C) ∧
      C.biUnion triEdges ⊆ J ∧ (J\C.biUnion triEdges) ⊆ cover D ∧
      IsPhysical H F (J\C.biUnion triEdges) ∧
      (∀ x, (((C.biUnion triEdges).filter (fun e => x ∈ e)).card : ℝ) ≤
        η*Fintype.card V) ∧
      (Pasch.count (Rfixed∪C) : ℝ) ≤ Pasch.count Rfixed+
        2*((J\cover D).card : ℝ)*((L+1 : ℕ) : ℝ)^3/κ := by
  have hUH : J\cover D ⊆ edges H := sdiff_subset.trans hJH
  have hdiag : ∀ e ∈ J\cover D, ¬ e.IsDiag := by
    intro e he
    exact H.G.not_isDiag_of_mem_edgeSet (by simpa [edges] using hUH he)
  have hSup : ∀ e ∈ J\cover D,
      κ*(Fintype.card V : ℝ) ≤ (candidates H F (cover D) e).card := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      have huv : H.G.Adj u v := by simpa [edges] using hUH he
      exact (hSupply u v he huv).trans (by
        exact_mod_cast card_le_card (good_subset_candidates H F D u v))
  obtain ⟨C,hC,hPC,hcov,hsub,hcd,hStat⟩ := Pasch.cover_down_native_with_fixed_universe_pasch κ η hκ hη
    H F P0 hP0 Rfixed hP0fixed L hL (J\cover D) (cover D) sdiff_disjoint
    (hProtected.mono_right (union_subset sdiff_subset hXJ)) hdiag
    (candidates H F (cover D)) (fun _ _ _ hw => (mem_filter.mp hw).2)
    hdeg hOrder hCard hSparse hSup
  have hCJ : C.biUnion triEdges ⊆ J := hsub.trans (union_subset sdiff_subset hXJ)
  refine ⟨C,hC,hPC,hCJ,?_,
    isPhysical_sdiff_of_decomposition hphys hC.isDecomposition hCJ,hcd,hStat⟩
  intro e he
  by_contra heX
  exact (mem_sdiff.mp he).2 (hcov (mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,heX⟩))

end TypedTriangle.StockEntry

#print axioms TypedTriangle.StockEntry.enter_stock_native_with_fixed_universe_pasch
