/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExplicitUniformCompression
public import RequestProject.TypedTriangle.PhysicalQuotientBounds
public import RequestProject.TypedTriangle.QuotientBoxExplicitBound
@[expose] public section
noncomputable section
namespace TypedTriangle.ExplicitSample

def physicalRankBound (α : ℝ) (h : ℕ) : ℕ := (compressionSampleSize α h+1)^2

def physicalTorsionBound (α : ℝ) (h : ℕ) : ℕ :=
  max 1 (QuotientBox.explicitTorsionBound (physicalRankBound α h)
    (3*compD0 (min α 1) (compressionSampleSize α h)))

theorem physicalTorsionBound_pos (α : ℝ) (h : ℕ) : 1 ≤ physicalTorsionBound α h :=
  le_max_left _ _

/-- Original H3--H4, with specified rank, torsion and order bounds. -/
theorem physQuot_bounds_of_H3H4_explicit (α : ℝ) (h : ℕ) (hα : 0 < α)
    {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (hn : compressionOrder α h ≤ Fintype.card V)
    (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h) :
    Module.finrank ℤ (physQuot H F) ≤ physicalRankBound α h ∧
      Nat.card (Submodule.torsion ℤ (physQuot H F)) ≤ physicalTorsionBound α h := by
  obtain ⟨cmp⟩ := compression_of_H3H4_explicit α h hα H F hn hH3 hH4
  obtain ⟨hrank,htor⟩ := physQuot_bounds_of_compression H F cmp
  refine ⟨hrank,?_⟩
  exact htor.trans ((QuotientBox.torBound_le_explicit _ _).trans (le_max_right _ _))

#print axioms physQuot_bounds_of_H3H4_explicit
end TypedTriangle.ExplicitSample
