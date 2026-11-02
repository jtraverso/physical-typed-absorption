module
public import RequestProject.TypedTriangle.TowerThresholdAssembly
public import RequestProject.TypedTriangle.TowerParameterScale
public import RequestProject.TypedTriangle.MainPaperIIIExplicit
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Vortex.Explicit
open TowerBounds

/-- A base-two tower whose height is specified by a pure natural-number program. -/
def paperIIITowerThreshold (α C : ℝ) (h : ℕ) : ℕ :=
  tower2 (paperIIITowerHeight (parameterScale α C h) h)

theorem rational_example_tower_threshold :
    paperIIITowerThreshold (1/100 : ℝ) 2 6 = tower2 (paperIIITowerHeight 100 6) := by
  change tower2 (paperIIITowerHeight (parameterScale (1/100 : ℝ) 2 6) 6) = _
  exact congrArg (fun K => tower2 (paperIIITowerHeight K 6)) rational_example_scale

theorem paperIIIThreshold_le_towerThreshold (α C : ℝ) (h : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hh : 6 ≤ h) :
    paperIIIThreshold α C h ≤ paperIIITowerThreshold α C h := by
  have hK := parameterScale_bounds α C h
  exact (paperIIIThreshold_le_naturalMajorant
    (alpha_magnitude h hα) (seed_constant_magnitude h hC) hK.2.1 hh).trans
    (self_le_tower2 _)

/-- T with its original H1--H4 at the specified base-two tower threshold. -/
theorem main_theorem_T_at_tower_order {I : Type} (F : Set (Multiset I))
    (α C : ℝ) (h : ℕ) (hα : 0 < α) (hC : 1 ≤ C) (hh : 6 ≤ h) :
    ∀ {X : Type} [Fintype X] (H : Host X I),
      paperIIITowerThreshold α C h ≤ Fintype.card X →
      (∃ μ : Finset X → ℝ, IsDiffuseSeed H F C μ) →
      IsPhysical H F (edges H) → CommonNbrCond H F α →
      HingeCond H F α h →
      ∃ D : Finset (Finset X), IsDecomposition H F (edges H) D := by
  intro X _ H hn
  exact main_theorem_T_at_explicit_order F α C h hα hC hh H
    ((paperIIIThreshold_le_towerThreshold α C h hα hC hh).trans hn)

#print axioms paperIIIThreshold_le_towerThreshold
#print axioms main_theorem_T_at_tower_order
end TypedTriangle.Vortex.Explicit
