module
public import RequestProject.TypedTriangle.CompletionRegularizationNumerics
@[expose] public section
open Finset
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Completion

def finiteRegularization {T : Type} (m : ℕ) (ν : ℕ → T → ℝ) (ρ : T → ℝ) : T → ℝ :=
  (∑ i ∈ range m, (1/(2:ℝ)^(i+1)) • ν i)+(1/(2:ℝ)^m) • ρ

@[simp] theorem finiteRegularization_apply {T : Type} (m : ℕ)
    (ν : ℕ → T → ℝ) (ρ : T → ℝ) (t : T) :
    finiteRegularization m ν ρ t =
      (∑ i ∈ range m, (1/(2:ℝ)^(i+1))*ν i t)+(1/(2:ℝ)^m)*ρ t := by
  simp [finiteRegularization,Finset.sum_apply]

theorem geometric_telescoping (m : ℕ) (w : ℕ → ℝ) :
    (∑ i ∈ range m, (1/(2:ℝ)^(i+1))*(2*w i-w (i+1)))=
      w 0-(1/(2:ℝ)^m)*w m := by
  induction m with
  | zero =>  simp
  | succ m ih => 
    rw [sum_range_succ,ih,pow_succ]
    have hp : (2:ℝ)^m ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp <;> ring

/-- Exactness of the finite correction. Approximate packings and the terminal
fractional decomposition are explicit inputs; there is no limiting argument. -/
theorem finiteRegularization_exact {T E : Type} (L : (T → ℝ) →ₗ[ℝ] (E → ℝ))
    (m : ℕ) (ν : ℕ → T → ℝ) (ρ : T → ℝ) (w : ℕ → E → ℝ)
    (hStep : ∀ i < m, L (ν i)=2 • w i-w (i+1))
    (hTerminal : L ρ=w m) : L (finiteRegularization m ν ρ)=w 0 := by
  ext e
  simp only [finiteRegularization,map_add,map_sum,map_smul,Pi.add_apply,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hTerminal]
  have hSum : (∑ i ∈ range m, (1/(2:ℝ)^(i+1))*L (ν i) e)=
      ∑ i ∈ range m, (1/(2:ℝ)^(i+1))*(2*w i e-w (i+1) e) := by
    apply sum_congr rfl
    intro i hi
    rw [hStep i (mem_range.mp hi)]
    simp [two_smul,Pi.sub_apply,Pi.add_apply,two_mul]
  rw [hSum,geometric_telescoping]
  ring

theorem finiteRegularization_nonneg {T : Type} (m : ℕ)
    (ν : ℕ → T → ℝ) (ρ : T → ℝ)
    (hν : ∀ i < m, ∀ t, 0 ≤ ν i t) (hρ : ∀ t,0 ≤ ρ t) :
    ∀ t,0 ≤ finiteRegularization m ν ρ t := by
  intro t
  rw [finiteRegularization_apply]
  apply add_nonneg
  · apply sum_nonneg
    intro i hi
    exact mul_nonneg (by positivity) (hν i (mem_range.mp hi) t)
  · exact mul_nonneg (by positivity) (hρ t)

theorem finiteRegularization_bound {T : Type} (m : ℕ)
    (ν : ℕ → T → ℝ) (ρ : T → ℝ) (n A z : ℝ)
    (hn : 0 < n) (hA : 0 ≤ A) (hz : 0 ≤ z)
    (hTail : 1/(2:ℝ)^m ≤ 1/n)
    (hν : ∀ i < m, ∀ t, ν i t ≤ (1+z)*A*((i:ℝ)+1)^8/n)
    (hρ : ∀ t,ρ t ≤ 1+z) :
    ∀ t,finiteRegularization m ν ρ t ≤ (1+z)*(1+A*1091670)/n := by
  intro t
  rw [finiteRegularization_apply]
  have hSum : (∑ i ∈ range m,(1/(2:ℝ)^(i+1))*ν i t) ≤ 
      ((1+z)*A/n)*(∑ i ∈ range m,((i:ℝ)+1)^8/2^(i+1)) := by
    calc
      _  ≤  ∑ i ∈ range m,(1/(2:ℝ)^(i+1))*((1+z)*A*((i:ℝ)+1)^8/n) := by
        apply sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hν i (mem_range.mp hi) t) (by positivity)
      _ = _ := by rw [mul_sum]; apply sum_congr rfl; intros; ring
  have hMoment := mul_le_mul_of_nonneg_left (geometric_eighth_moment_bound m)
    (by positivity : 0 ≤ (1+z)*A/n)
  have hT : (1/(2:ℝ)^m)*ρ t ≤ (1/n)*(1+z) :=
    (mul_le_mul_of_nonneg_left (hρ t) (by positivity)).trans
      (mul_le_mul_of_nonneg_right hTail (by positivity))
  calc
    _  ≤  ((1+z)*A/n)*1091670+(1/n)*(1+z) := add_le_add (hSum.trans hMoment) hT
    _ = _ := by ring

/-- Adding a uniform positive floor preserves exact loads after rescaling
the normalized residual; this closes both sides of a diffuse seed. -/
theorem add_floor_exact {T E : Type} (L : (T → ℝ) →ₗ[ℝ] (E → ℝ))
    (base Ψ : T → ℝ) (target : E → ℝ) (a : ℝ)
    (hExact : L Ψ=(1/(1-a)) • (target-L base)) (ha : a ≠ 1) :
    L (base+(1-a) • Ψ)=target := by
  rw [map_add,map_smul,hExact,smul_smul]
  have hne : 1-a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have h : (1-a)*(1/(1-a))=1 := by field_simp
  rw [h,one_smul]
  abel

#print axioms finiteRegularization_exact
#print axioms finiteRegularization_bound
#print axioms add_floor_exact
end TypedTriangle.Completion
