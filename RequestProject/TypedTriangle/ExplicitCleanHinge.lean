module
public import RequestProject.TypedTriangle.VortexCleanHinge
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex.Explicit

/-- Only one forbidden edge is removed when cleaning the original hinge. -/
def cleanHingeOrder (α : ℝ) (h : ℕ) : ℕ :=
  ⌈max (48 / α) (8 * ((h : ℝ) + 6) * 2 ^ (h.choose 2) / α)⌉₊

theorem clean_hinge_of_H3H4_explicit (α : ℝ) (h : ℕ)
    (hα : 0 < α) (hh : 6 ≤ h) :
    ∀ {V I : Type*} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
      cleanHingeOrder α h ≤ Fintype.card V →
      CommonNbrCond H F α → HingeCond H F α h →
      CleanHingeCond H F (S07V49.hingeConstB α 1 h) (2 * h - 3) := by
  intro V I _ H F hn h3 h4
  have hnCast : (cleanHingeOrder α h : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_le.mpr hn
  have hnR : max (48 / α) (8 * ((h : ℝ) + 6) * 2 ^ (h.choose 2) / α) ≤
      (Fintype.card V : ℝ) := (Nat.le_ceil _).trans hnCast
  have hw1 : 2 + 4 * (1 : ℝ) ≤ α * Fintype.card V / 8 := by
    have ht := (div_le_iff₀ hα).mp ((le_max_left _ _).trans hnR)
    nlinarith
  have hw2 : (5 * (1 : ℝ) + h + 1) * 2 ^ (h.choose 2) ≤
      α * Fintype.card V / 8 := by
    have ht := (div_le_iff₀ hα).mp ((le_max_right _ _).trans hnR)
    nlinarith
  intro u v a b hab hTa hTb
  obtain ⟨huv, hua, hva, hub, hvb, _⟩ :=
    S07V24.roots_distinct (show S07V24.HingeTest H.G H.lab F u v a b from
      ⟨hab, hTa, hTb⟩)
  let C : Finset (Sym2 V) := {s(a, b)} ∩ edges H
  let J := subHost H (edges H \ C)
  have hCE : C ⊆ edges H := inter_subset_right
  have hCcard : C.card ≤ 1 := by
    exact (card_le_card (show C ⊆ {s(a, b)} from inter_subset_left)).trans (by simp)
  have hCdeg : ∀ x, SparseEdge.degIn C x ≤ 1 := by
    intro x
    exact (Finset.card_filter_le _ _).trans hCcard
  have h4J := hinge_after_edge_set_deletion_no_seed H F α h hα hh h3 h4
    C 1 hCE hCdeg (by simpa only [Nat.cast_one] using hw1)
      (by simpa only [Nat.cast_one] using hw2)
  have hAllowed {T : Finset V} (hT : IsAllowed H F T)
      (hMissing : a ∉ T ∨ b ∉ T) : IsAllowed J F T := by
    apply isAllowed_subHost_of hT
    intro e he
    refine mem_sdiff.mpr ⟨triEdges_subset_edges hT he, ?_⟩
    intro hc
    have heab : e = s(a, b) := mem_singleton.mp (mem_inter.mp hc).1
    subst e
    have hends := mem_triEdges.mp he
    rcases hMissing with ha | hb
    · exact ha hends.1
    · exact hb hends.2.1
  have hTaJ : IsAllowed J F {u, v, a} :=
    hAllowed hTa (Or.inr (by simp [hub.symm, hvb.symm, hab.symm]))
  have hTbJ : IsAllowed J F {u, v, b} :=
    hAllowed hTb (Or.inl (by simp [hua.symm, hva.symm, hab]))
  obtain ⟨i, hi, hih, hcount⟩ := h4J u v a b hab hTaJ hTbJ
  refine ⟨i, hi, hih, hcount.trans ?_⟩
  have hIncl : hinges J F u v a b i ⊆
      (SparseEdge.hinges H.G H.lab F u v a b i).filter
        (fun E => s(a, b) ∉ E) := by
    intro E hE
    obtain ⟨_, hHingeJ, hOrder⟩ := mem_filter.mp hE
    have hSub : E ⊆ edges H := by
      intro e he
      have heJ := hHingeJ.1 he
      rw [Residual.edges_subHost_eq (sdiff_subset : edges H \ C ⊆ edges H)] at heJ
      exact (mem_sdiff.mp heJ).1
    have hUp {A : Finset (Sym2 V)} {D : Finset (Finset V)}
        (hD : IsDecomposition J F A D) : IsDecomposition H F A D :=
      ⟨fun T hT => isAllowed_mono (subHost_le H _) rfl (hD.1 T hT), hD.2⟩
    have hHinge : IsHinge H F u v a b E :=
      ⟨hSub, hHingeJ.2.1,
        (by obtain ⟨D, hD⟩ := hHingeJ.2.2.1; exact ⟨D, hUp hD⟩),
        (by obtain ⟨D, hD⟩ := hHingeJ.2.2.2; exact ⟨D, hUp hD⟩)⟩
    have hClean : s(a, b) ∉ E := by
      intro he
      have heJ := hHingeJ.1 he
      rw [Residual.edges_subHost_eq (sdiff_subset : edges H \ C ⊆ edges H)] at heJ
      exact (mem_sdiff.mp heJ).2
        (mem_inter.mpr ⟨mem_singleton_self _, (mem_sdiff.mp heJ).1⟩)
    refine mem_filter.mpr ⟨?_, hClean⟩
    change E ∈ hinges H F u v a b i
    exact mem_filter.mpr ⟨mem_univ E, hHinge, hOrder⟩
  exact_mod_cast Finset.card_le_card hIncl

#print axioms clean_hinge_of_H3H4_explicit
end TypedTriangle.Vortex.Explicit
