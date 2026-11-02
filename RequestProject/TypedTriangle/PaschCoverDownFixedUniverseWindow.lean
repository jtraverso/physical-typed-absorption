module
public import RequestProject.TypedTriangle.PaschCoverDownWindow
public import RequestProject.TypedTriangle.PaschCoverDownFixedUniverse
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace TypedTriangle.Pasch
open StockEntry.Explicit
variable {V I : Type*} [Fintype V]

/-- The native cover-down budgets already leave the half-density margin used
by the actual low-Pasch-cost greedy. No cost-selection oracle is an input. -/
theorem cover_down_native_with_fixed_universe_pasch (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η)
    (H : Host V I) (F : Set (Multiset I)) (P0 : Finset (Finset V))
    (hP0 : IsPacking H F P0)
    (Rfixed : Finset (Finset V)) (hP0fixed : P0 ⊆ Rfixed)
    (L : ℕ) (hL : PairCodegreeBound Rfixed L) (U X : Finset (Sym2 V)) (hUX : Disjoint U X)
    (hProtected : Disjoint (P0.biUnion triEdges) (U∪X)) (hU : ∀ e ∈ U, ¬ e.IsDiag)
    (Cand : Sym2 V → Finset V)
    (hCand : ∀ e ∈ U, ∀ w ∈ Cand e,
      w ∉ e ∧ IsAllowed H F (insert w e.toFinset) ∧ ∀ x ∈ e, s(x,w) ∈ X)
    {d : ℕ} (hdeg : ∀ x, (U.filter (x ∈ ·)).card ≤ d)
    (hOrder : coverDownOrder κ η ≤ Fintype.card V)
    (hCard : U.card ≤ Fintype.card V*d)
    (hSparse : (d : ℝ) ≤ coverDownBudget κ η*Fintype.card V)
    (hSupply : ∀ e ∈ U, κ*(Fintype.card V : ℝ) ≤ (Cand e).card) :
    ∃ C : Finset (Finset V), IsPacking H F C ∧ IsPacking H F (P0∪C) ∧
      U ⊆ C.biUnion triEdges ∧ C.biUnion triEdges ⊆ U∪X ∧
      (∀ v, (((C.biUnion triEdges).filter (v ∈ ·)).card : ℝ) ≤ η*Fintype.card V) ∧
      (count (Rfixed∪C) : ℝ) ≤ count Rfixed+2*(U.card : ℝ)*((L+1 : ℕ) : ℝ)^3/κ := by
  let q := coverDownQuota κ η (Fintype.card V)
  obtain ⟨hq,hMargin,hDegree⟩ := cover_down_window_pasch_margin κ η hκ hη
    (Fintype.card V) U.card d hOrder hCard hSparse
  change 0 < q at hq
  change ((U.card+q*(2*d+4*q) : ℕ) : ℝ)+(q : ℝ)*(κ/2)*Fintype.card V ≤
    (q : ℝ)*κ*Fintype.card V at hMargin
  change ((2*d+2*q : ℕ) : ℝ) ≤ η*Fintype.card V at hDegree
  have hn : 0 < Fintype.card V := by
    by_contra h
    have hz : Fintype.card V = 0 := by omega
    simpa [q,coverDownQuota,hz] using hq
  have hMargin' : ∀ e ∈ U,
      (U.card : ℝ)+(q : ℝ)*(2*(d+2*q) : ℕ)+(q : ℝ)*(κ/2)*Fintype.card V ≤
        (q : ℝ)*(Cand e).card := by
    intro e he
    calc
      _ = ((U.card+q*(2*d+4*q) : ℕ) : ℝ)+(q : ℝ)*(κ/2)*Fintype.card V := by
        push_cast
        ring
      _ ≤ (q : ℝ)*κ*Fintype.card V := hMargin
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (hSupply e he) (Nat.cast_nonneg q)
        convert hh using 1 <;> ring
  obtain ⟨C,hC,hPC,hCover,hSub,hDeg,hStat⟩ := cover_down_with_fixed_universe_pasch H F P0 hP0 Rfixed hP0fixed L hL U X hUX
    hProtected hU Cand hCand hq (κ/2) (half_pos hκ) hn hdeg hMargin'
  refine ⟨C,hC,hPC,hCover,hSub,?_,?_⟩
  · intro v
    exact (by exact_mod_cast hDeg v : (((C.biUnion triEdges).filter (v ∈ ·)).card : ℝ) ≤
      (2*d+2*q : ℕ)).trans hDegree
  · have hEq : (U.card : ℝ)*((L+1 : ℕ) : ℝ)^3/(κ/2) =
        2*(U.card : ℝ)*((L+1 : ℕ) : ℝ)^3/κ := by
      field_simp [ne_of_gt hκ] <;> ring
    simpa only [hEq] using hStat

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.cover_down_native_with_fixed_universe_pasch
