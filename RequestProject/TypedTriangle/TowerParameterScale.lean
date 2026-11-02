module
public import RequestProject.TypedTriangle.TowerMagnitude
@[expose] public section
noncomputable section
namespace TypedTriangle.TowerBounds

/-- Only input normalization uses real ceilings. The eventual tower height
will be an integer program of this single natural scale. -/
def parameterScale (α C : ℝ) (h : ℕ) : ℕ :=
  max 2 (max h (max ⌈α⌉₊ (max ⌈1/α⌉₊ ⌈C⌉₊)))

theorem parameterScale_bounds (α C : ℝ) (h : ℕ) :
    2 ≤ parameterScale α C h ∧ h ≤ parameterScale α C h ∧
    ⌈α⌉₊ ≤ parameterScale α C h ∧ ⌈1/α⌉₊ ≤ parameterScale α C h ∧
    ⌈C⌉₊ ≤ parameterScale α C h := by
  unfold parameterScale
  omega

theorem alpha_magnitude {α C : ℝ} (h : ℕ) (hα : 0 < α) :
    Magnitude (parameterScale α C h) α := by
  obtain ⟨_,_,ha,hi,_⟩ := parameterScale_bounds α C h
  exact ⟨hα,(Nat.le_ceil α).trans (by exact_mod_cast ha),
    (Nat.le_ceil (1/α)).trans (by exact_mod_cast hi)⟩

theorem seed_constant_magnitude {α C : ℝ} (h : ℕ) (hC : 1 ≤ C) :
    Magnitude (parameterScale α C h) C := by
  obtain ⟨h2,_,_,_,hc⟩ := parameterScale_bounds α C h
  have h1 : (1 : ℝ) ≤ parameterScale α C h := by exact_mod_cast (by omega : 1 ≤ parameterScale α C h)
  have hi : 1/C ≤ 1 := by
    simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hC
  exact ⟨lt_of_lt_of_le (by norm_num) hC,
    (Nat.le_ceil C).trans (by exact_mod_cast hc),hi.trans h1⟩

/-- An illustrative rational instance fixes the scale without evaluating
any of the enormous integer operations in the resulting tower height. -/
theorem rational_example_scale : parameterScale (1/100 : ℝ) 2 6 = 100 := by
  norm_num [parameterScale]

#print axioms alpha_magnitude
#print axioms seed_constant_magnitude
#print axioms rational_example_scale
end TypedTriangle.TowerBounds
