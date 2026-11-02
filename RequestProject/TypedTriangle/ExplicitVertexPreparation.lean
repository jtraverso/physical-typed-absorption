module
public import RequestProject.TypedTriangle.ExplicitVertexWindows
public import RequestProject.TypedTriangle.ExplicitPhysicalQuotientBounds
public import RequestProject.TypedTriangle.VortexIntrinsicFirstEntry
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex.Explicit
open ExplicitGeometry ExplicitSample

def preparationRank (α : ℝ) (h : ℕ) : ℕ := physicalRankBound (α / 2) h
def preparationTorsion (α : ℝ) (h : ℕ) : ℕ := physicalTorsionBound (α / 2) h
def entryTolerance (α : ℝ) (h : ℕ) : ℝ := nestedBudget α h
def entryOrder (α : ℝ) (h : ℕ) : ℕ :=
  max (nestedOrder α h) (2 * compressionOrder (α / 2) h)

theorem vertex_deleted_bounds_explicit {α : ℝ} (h : ℕ) (hα : 0 < α)
    {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (Z : Finset V)
    (hn : 2 * compressionOrder (α / 2) h ≤ Fintype.card V)
    (h3 : CommonNbrCond H F α) (h4 : HingeCond H F α h)
    (hZ : (Z.card : ℝ) ≤ deletionBudget α h * Fintype.card V) :
    Module.finrank ℤ (physQuot (vertexDeleted H Z) F) ≤ preparationRank α h ∧
      Nat.card (Submodule.torsion ℤ (physQuot (vertexDeleted H Z) F)) ≤
        preparationTorsion α h := by
  obtain ⟨_, hδhalf, hbudget⟩ := deletionBudget_spec hα h
  obtain ⟨hZ3, hZ4⟩ := hbudget (show (0 : ℝ) ≤ Fintype.card V by positivity) hZ
  have hhalf : (Z.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 := by
    have := mul_le_mul_of_nonneg_right hδhalf
      (show (0 : ℝ) ≤ Fintype.card V by positivity)
    linarith
  have hhalfN : 2 * Z.card ≤ Fintype.card V := by
    exact_mod_cast (show (2 : ℝ) * Z.card ≤ Fintype.card V by linarith)
  have hcard := card_survivors_add_card Z
  have hN : compressionOrder (α / 2) h ≤ Fintype.card (Survivors Z) := by omega
  have hg := original_geometry_restrictedHost hα.le h3 h4 Z hZ3 hZ4
  obtain ⟨hr, ht⟩ := physQuot_bounds_of_H3H4_explicit (α / 2) h (by positivity)
    (restrictedHost H Z) F hN hg.1 hg.2
  exact physQuot_bounds_surviving_ambient H F Z _ _ hr ht

/-- Finite maximization on one host; the numerical producer below supplies
    both controls from the original geometry at its specified threshold. -/
theorem intrinsic_entry_from_control {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (ε : ℝ) (d T : ℕ)
    (hε : 0 < ε) (β : ℕ → ℝ) (hβ : ∀ j, 0 ≤ β j)
    (hBudget : (∑ j ∈ range (d + (d + 1) * Nat.log 2 T + 1), β j) ≤ ε)
    (hBounds : ∀ A : Finset V, (A.card : ℝ) ≤ ε * Fintype.card V →
      Module.finrank ℤ (physQuot (vertexDeleted H A) F) ≤ d ∧
        Nat.card (Submodule.torsion ℤ (physQuot (vertexDeleted H A) F)) ≤ T)
    (hSurj : ∀ A B : Finset V, (A.card : ℝ) ≤ ε * Fintype.card V →
      (B.card : ℝ) ≤ ε * Fintype.card V → Function.Surjective (nestedVertexQuotMap H F A B)) :
    ∃ r ≤ d + (d + 1) * Nat.log 2 T, ∃ A : Finset V,
      physicalPotential H F T ≤ r ∧ physicalPotential (restrictedHost H A) F T = r ∧
      (A.card : ℝ) ≤ Fintype.card V *
        ((∑ j ∈ range r, β j) - ∑ j ∈ range (physicalPotential H F T), β j) ∧
      ∀ B : Finset V, (B.card : ℝ) ≤ β r * Fintype.card (Survivors A) →
        Function.Injective (nestedVertexQuotMap H F A B) := by
  let L := d + (d + 1) * Nat.log 2 T
  let n : ℝ := Fintype.card V
  let p₀ := physicalPotential H F T
  let p : Finset V → ℕ := fun A => physicalPotential (vertexDeleted H A) F T
  let S : ℕ → ℝ := fun r => ∑ j ∈ range r, β j
  have hn0 : 0 ≤ n := by positivity
  have hS0 (r : ℕ) : 0 ≤ S r := sum_nonneg (by intro j _; exact hβ j)
  have hSmono {r s : ℕ} (hrs : r ≤ s) : S r ≤ S s :=
    sum_le_sum_of_subset_of_nonneg (range_mono hrs) (by intro j _ _; exact hβ j)
  have hpBound (A : Finset V) (hA : (A.card : ℝ) ≤ ε * n) : p A ≤ L :=
    physicalPotential_le _ F d T (hBounds A hA).1 (hBounds A hA).2
  have heq : vertexDeleted H ∅ = H := by
    have hg : (vertexDeleted H ∅).G = H.G := by ext u v; simp [vertexDeleted]
    exact congrArg (fun G => (⟨G, H.lab⟩ : Host V I)) hg
  have hpEmpty : p ∅ = p₀ := by dsimp [p, p₀]; rw [heq]
  have hp₀ : p₀ ≤ L := by
    rw [← hpEmpty]
    exact hpBound ∅ (by simp only [card_empty, Nat.cast_zero]; positivity)
  let C := univ.powerset.filter (fun A : Finset V =>
    p₀ ≤ p A ∧ p A ≤ L ∧ (A.card : ℝ) ≤ n * (S (p A) - S p₀))
  have hEmpty : ∅ ∈ C := by
    simp only [C, mem_filter, mem_powerset, empty_subset, hpEmpty,
      le_refl, hp₀, card_empty, Nat.cast_zero, sub_self, mul_zero, and_self]
  obtain ⟨A, hAC, hMax⟩ := Finset.exists_max_image C p ⟨∅, hEmpty⟩
  obtain ⟨hp₀A, hpAL, hA⟩ := (mem_filter.mp hAC).2
  have hAsmall : (A.card : ℝ) ≤ ε * n := by
    have hSum := hSmono (show p A ≤ L + 1 by omega)
    have hTot : S (L + 1) ≤ ε := hBudget
    have hCap := mul_le_mul_of_nonneg_left hSum hn0
    have hCap' := mul_le_mul_of_nonneg_left hTot hn0
    have hPrior := mul_nonneg hn0 (hS0 p₀)
    nlinarith
  refine ⟨p A, hpAL, A, hp₀A, (physicalPotential_vertexDeleted_eq H F A T).symm, hA, ?_⟩
  intro B hB
  by_contra hBad
  have hSurv : (Fintype.card (Survivors A) : ℝ) ≤ n := by
    have hc := card_survivors_add_card A
    have hcR : (Fintype.card (Survivors A) : ℝ) + A.card = n := by
      dsimp only [n]
      exact_mod_cast hc
    have hANonneg : (0 : ℝ) ≤ A.card := by positivity
    linarith
  have hBroot : (B.card : ℝ) ≤ β (p A) * n :=
    hB.trans (mul_le_mul_of_nonneg_left hSurv (hβ _))
  have hStepPrefix : S (p A) + β (p A) ≤ S (L + 1) := by
    simpa only [S, sum_range_succ] using hSmono (show p A + 1 ≤ L + 1 by omega)
  have hTot : S (L + 1) ≤ ε := hBudget
  have hBsmall : (B.card : ℝ) ≤ ε * n := by
    have hRadius : β (p A) ≤ ε := by linarith [hS0 (p A)]
    exact hBroot.trans (mul_le_mul_of_nonneg_right hRadius hn0)
  have hUnion : ((A ∪ B).card : ℝ) ≤ (A.card : ℝ) + B.card := by exact_mod_cast card_union_le A B
  have hABsmall : ((A ∪ B).card : ℝ) ≤ ε * n := by
    have hCap := mul_le_mul_of_nonneg_left (hStepPrefix.trans hTot) hn0
    have hPrior := mul_nonneg hn0 (hS0 p₀)
    nlinarith
  have hStrict : p A < p (A ∪ B) := physicalPotential_map_strict F T
    (vertexDeleted_antitone H subset_union_left) rfl (hSurj A B hAsmall hBsmall)
    (hBounds A hAsmall).2 hBad
  have hpABL : p (A ∪ B) ≤ L := hpBound (A ∪ B) hABsmall
  have hPrefix : S (p A) + β (p A) ≤ S (p (A ∪ B)) := by
    simpa only [S, sum_range_succ] using hSmono (show p A + 1 ≤ p (A ∪ B) by omega)
  have hABbudget : ((A ∪ B).card : ℝ) ≤ n * (S (p (A ∪ B)) - S p₀) := by
    have hCap := mul_le_mul_of_nonneg_left hPrefix hn0
    nlinarith
  have hABC : A ∪ B ∈ C := mem_filter.mpr
    ⟨mem_powerset.mpr (subset_univ _), hp₀A.trans hStrict.le, hpABL, hABbudget⟩
  have hContr := hMax (A ∪ B) hABC
  omega

/-- First entry with every host-independent numerical parameter specified. -/
theorem intrinsic_first_entry_explicit (α : ℝ) (h : ℕ) (hα : 0 < α)
    (β : ℕ → ℝ) (hβ : ∀ j, 0 ≤ β j)
    (hBudget : (∑ j ∈ range (preparationRank α h +
      (preparationRank α h + 1) * Nat.log 2 (preparationTorsion α h) + 1), β j) ≤
      entryTolerance α h)
    {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (hn : entryOrder α h ≤ Fintype.card V)
    (h3 : CommonNbrCond H F α) (h4 : HingeCond H F α h) :
    ∃ r ≤ preparationRank α h + (preparationRank α h + 1) * Nat.log 2 (preparationTorsion α h),
      ∃ A : Finset V, physicalPotential H F (preparationTorsion α h) ≤ r ∧
        physicalPotential (restrictedHost H A) F (preparationTorsion α h) = r ∧
        (A.card : ℝ) ≤ Fintype.card V * ((∑ j ∈ range r, β j) -
          ∑ j ∈ range (physicalPotential H F (preparationTorsion α h)), β j) ∧
        ∀ B : Finset V, (B.card : ℝ) ≤ β r * Fintype.card (Survivors A) →
          Function.Injective (nestedVertexQuotMap H F A B) := by
  apply intrinsic_entry_from_control H F (entryTolerance α h) (preparationRank α h)
    (preparationTorsion α h) (nestedBudget_pos hα h) β hβ hBudget
  · intro A hA
    exact vertex_deleted_bounds_explicit h hα H F A ((le_max_right _ _).trans hn) h3 h4
      (hA.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)))
  · intro A B hA hB
    obtain ⟨hA3, hA4, hB1, hB2⟩ := nested_windows_explicit α h hα A B
      ((le_max_left _ _).trans hn) hA hB
    exact nestedVertexQuotMap_surjective hα h3 h4 A B hA3 hA4 hB1 hB2

#print axioms vertex_deleted_bounds_explicit
#print axioms intrinsic_first_entry_explicit
end TypedTriangle.Vortex.Explicit
