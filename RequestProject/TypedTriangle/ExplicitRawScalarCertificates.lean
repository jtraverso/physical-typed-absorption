module
public import RequestProject.TypedTriangle.ExplicitRawPathsPreparedVortex
public import RequestProject.TypedTriangle.ExplicitNativeOuterTests
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex.ExplicitRaw

theorem rawMinimumOrder_required (α q : ℝ) (h N M : ℕ) :
    M ≤ rawMinimumOrder α q h N M :=
  (le_max_right _ _).trans (le_max_left _ _)

theorem rawMinimumOrder_one (α q : ℝ) (h N M : ℕ) :
    1 ≤ rawMinimumOrder α q h N M :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem rawTerminalOrder_pos (α C q : ℝ) (h N M : ℕ) :
    0 < rawTerminalOrder α C q h N M := by
  have hs : (0:ℝ) < rawMinimumOrder α q h N M := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one (rawMinimumOrder_one α q h N M))
  exact hs.trans_le (le_max_right _ _)

theorem nativeRoutePrecision_pos (α q : ℝ) (h : ℕ) (hα : 0 < α) (hq : 0 < q) :
    0 < nativeRoutePrecision α q h := by
  obtain ⟨hm,ha,_⟩ := nativePathScalars_spec α h hα
  dsimp only [nativeRoutePrecision,S07V24.epsOf]
  positivity

theorem nativeOuterAvoidBudget_pos (α : ℝ) (h : ℕ) (hα : 0 < α) :
    0 < nativeOuterAvoidBudget α h := by
  obtain ⟨_,_,hδ,_⟩ := nativePathScalars_spec α h hα
  exact lt_min hδ (lt_min (by positivity) (by norm_num))

#print axioms rawTerminalOrder_pos
#print axioms nativeRoutePrecision_pos
end TypedTriangle.Vortex.ExplicitRaw
