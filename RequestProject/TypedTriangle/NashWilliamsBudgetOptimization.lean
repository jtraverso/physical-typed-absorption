module
public import RequestProject.TypedTriangle.CompletionRegularizationNumerics
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Completion.NashWilliamsOptimization

/-- A sharpened version of the local arithmetic budget `aux_bip` in
Nash-Williams FracStab/Main.lean. This does not modify that repository or
claim that all downstream stability estimates have been reassembled. -/
theorem bip_budget_576 {γ r : ℝ} (h : γ ≤ r^4/576) :
    36*(4*γ)+(r^2)^2/4 ≤ (r^2)^2/2 := by
  have he : (r^2)^2=r^4 := by ring
  rw [he]
  nlinarith only [h]

theorem gamma_cap_strictly_larger {r : ℝ} (hr : 0 < r) : r^4/600 < r^4/576 := by
  have hh := pow_pos hr 4
  nlinarith only [hh]

/-- If the other caps are inactive and t=gamma^2/2, the displayed epsilon
formula scales by (25/24)^5. This algebraic statement is conditional on
that branch and is not an improved global stability theorem. -/
theorem epsilon_scaling (r γ : ℝ) :
    ((((25/24:ℝ)*γ)^2/2)^2*r^2*((25/24:ℝ)*γ)/1000)=
      (25/24:ℝ)^5*((γ^2/2)^2*r^2*γ/1000) := by ring

theorem cap_improvement_ratio : (600:ℝ)/576=25/24 := by norm_num

#print axioms bip_budget_576
#print axioms gamma_cap_strictly_larger
#print axioms epsilon_scaling
end TypedTriangle.Completion.NashWilliamsOptimization
