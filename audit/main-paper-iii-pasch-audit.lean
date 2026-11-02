module
public import RequestProject.TypedTriangle.MainPaperIIIPasch
open Finset Classical TypedTriangle
example {I : Type} (F : Set (Multiset I)) (α C η : ℝ) (h q : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hh : 6 ≤ h) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {V : Type} [Fintype V] (H : Host V I) (μ : Finset V → ℝ),
      N ≤ Fintype.card V → IsDiffuseSeed H F C μ →
      IsPhysical H F (edges H) → CommonNbrCond H F α → HingeCond H F α h →
      ∀ (ν : Type) [Fintype ν] (w : ν → Finset V → ℝ),
      (Fintype.card ν : ℝ) ≤ (Fintype.card V : ℝ)^q →
      (∀ k Q, IsAllowed H F Q → |w k Q| ≤ 1) →
      ∃ D : Finset (Finset V), IsDecomposition H F (edges H) D ∧
        (∀ k, |(∑ Q ∈ D, w k Q)-(∑ Q ∈ allowed H F, μ Q*w k Q)| ≤
          η*(Fintype.card V : ℝ)^2) ∧
        |(Pasch.count D : ℝ)-Pasch.target μ (allowed H F)| ≤ η*(Fintype.card V : ℝ)^2 :=
  Vortex.main_theorem_T_with_triangle_monitors_and_pasch F α C η h q hα hC hh hη
#check @TypedTriangle.Vortex.main_theorem_T_with_triangle_monitors_and_pasch
#print axioms TypedTriangle.Vortex.main_theorem_T_with_triangle_monitors_and_pasch
