module
public import RequestProject.TypedTriangle.TowerTriangleThresholdAssembly
public import RequestProject.TypedTriangle.MainPaperIIIExplicitTriangleMonitors
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Vortex.Explicit
open TowerBounds

/-- The height is an integer program of the normalized inputs and q. -/
def paperIIITriangleTowerThreshold (α C η : ℝ) (h q : ℕ) : ℕ :=
  tower2 (paperIIITriangleTowerHeight (triangleParameterScale α C η h q) h q)

theorem paperIIITriangleThreshold_le_towerThreshold (α C η : ℝ) (h q : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hh : 6 ≤ h) (hη : 0 < η) :
    paperIIITriangleThreshold α C η h q ≤ paperIIITriangleTowerThreshold α C η h q := by
  have hbase := triangleParameterScale_base α C η h q
  have hhK := (parameterScale_bounds α C h).2.1.trans hbase
  exact (paperIIITriangleThreshold_le_naturalMajorant
    ((alpha_magnitude h hα).mono hbase) ((seed_constant_magnitude h hC).mono hbase)
    (triangle_eta_magnitude h q hη) hhK hh).trans (self_le_tower2 _)

theorem main_theorem_T_with_triangle_monitors_at_tower_order {I : Type} (F : Set (Multiset I))
    (α C η : ℝ) (h q : ℕ) (hα : 0 < α) (hC : 1 ≤ C) (hh : 6 ≤ h) (hη : 0 < η) :
    ∀ {X : Type} [Fintype X] (H : Host X I) (μ : Finset X → ℝ),
      paperIIITriangleTowerThreshold α C η h q ≤ Fintype.card X →
      IsDiffuseSeed H F C μ → IsPhysical H F (edges H) →
      CommonNbrCond H F α → HingeCond H F α h →
      ∀ (ν : Type) [Fintype ν] (w : ν → Finset X → ℝ),
      (Fintype.card ν:ℝ) ≤ (Fintype.card X:ℝ)^q →
      (∀ k Q, IsAllowed H F Q → |w k Q| ≤ 1) →
      ∃ D : Finset (Finset X), IsDecomposition H F (edges H) D ∧
        ∀ k, |(∑ Q ∈ D, w k Q)-(∑ Q ∈ allowed H F, μ Q*w k Q)| ≤ η*(Fintype.card X:ℝ)^2 := by
  intro X _ H μ hn
  exact main_theorem_T_with_triangle_monitors_at_explicit_order F α C η h q hα hC hh hη H μ
    ((paperIIITriangleThreshold_le_towerThreshold α C η h q hα hC hh hη).trans hn)

#print axioms paperIIITriangleThreshold_le_towerThreshold
#print axioms main_theorem_T_with_triangle_monitors_at_tower_order
end TypedTriangle.Vortex.Explicit
