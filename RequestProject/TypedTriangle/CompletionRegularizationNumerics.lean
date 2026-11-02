module
public import RequestProject.TypedTriangle.Defs
@[expose] public section
open Finset
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Completion

def momentPotential (x : ℝ) : ℝ :=
  x^8+16*x^7+168*x^6+1456*x^5+10500*x^4+60592*x^3+
    262248*x^2+756688*x+1091670

theorem momentPotential_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ momentPotential x := by
  unfold momentPotential
  positivity

theorem momentPotential_step (x : ℝ) :
    2*momentPotential x-momentPotential (x+1)=(x+1)^8 := by
  unfold momentPotential
  ring

theorem geometric_eighth_moment_identity (m : ℕ) :
    (∑ i ∈ range m, ((i:ℝ)+1)^8/2^(i+1))=
      1091670-momentPotential m/2^m := by
  induction m with
  | zero =>  norm_num [momentPotential]
  | succ m ih => 
    rw [sum_range_succ,ih]
    push_cast
    have hs : momentPotential ((m:ℝ)+1)=2*momentPotential m-((m:ℝ)+1)^8 := by
      have hh := momentPotential_step (m:ℝ)
      linarith only [hh]
    have hp : (2:ℝ)^m ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [hs]
    simp only [pow_succ]
    field_simp
    <;> ring

/-- The earlier bound 10321920 can be replaced by the exact infinite
moment 1091670; this finite inequality uses no infinite-series theorem. -/
theorem geometric_eighth_moment_bound (m : ℕ) :
    (∑ i ∈ range m, ((i:ℝ)+1)^8/2^(i+1)) ≤ 1091670 := by
  rw [geometric_eighth_moment_identity]
  have hh := div_nonneg (momentPotential_nonneg m (Nat.cast_nonneg _))
    (by positivity : (0:ℝ) ≤ 2^m)
  linarith

def regularizationCoefficient : ℕ := 4096*10^44

theorem sample_growth (m : ℕ) (hm : 16 ≤ m) : (m+1)^8 ≤ 2*m^8 := by
  have hmul : (m+1)*16 ≤ 17*m := by omega
  have hp : ((m+1)*16)^8 ≤ (17*m)^8 := Nat.pow_le_pow_left hmul 8
  simp only [mul_pow] at hp
  have hc : 17^8 ≤ 2*16^8 := by norm_num
  have hh := Nat.mul_le_mul_right (m^8) hc
  omega

theorem all_samples_fit (m : ℕ) (hm : 256 ≤ m) :
    regularizationCoefficient*m^8 ≤ 2^(m-1) := by
  induction m,hm using Nat.le_induction with
  | base =>  norm_num [regularizationCoefficient]
  | succ m hm ih => 
    have hg := sample_growth m (by omega)
    have hh := Nat.mul_le_mul_left regularizationCoefficient hg
    have hk := Nat.mul_le_mul_left 2 ih
    have he : 2^(m+1-1)=2*2^(m-1) := by
      have hm0 : 0 < m := by omega
      have hs : m=m-1+1 := by omega
      conv_lhs =>  rw [show m+1-1=m by omega,hs,pow_succ]
      omega
    rw [he]
    nlinarith

theorem seed_constant_improvement :
    (1/(800000000:ℝ))+
      (1+1/100000000)*(1+(regularizationCoefficient:ℝ)*1091670) < 10^55/3 ∧
    1/(3*(10:ℝ)^55) ≤ 1/800000000 := by
  norm_num [regularizationCoefficient]

#print axioms geometric_eighth_moment_bound
#print axioms all_samples_fit
#print axioms seed_constant_improvement
end TypedTriangle.Completion
