module
public import RequestProject.TypedTriangle.CompletionRegularizationNumerics
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Completion

theorem samples_fit_from_base (L : ℕ) (hL : 16 ≤ L)
    (hBase : regularizationCoefficient*L^8 ≤ 2^(L-1))
    (m : ℕ) (hm : L ≤ m) : regularizationCoefficient*m^8 ≤ 2^(m-1) := by
  induction m,hm using Nat.le_induction with
  | base => exact hBase
  | succ m hm ih =>
    have hg := sample_growth m (hL.trans hm)
    have hh := Nat.mul_le_mul_left regularizationCoefficient hg
    have hk := Nat.mul_le_mul_left 2 ih
    have he : 2^(m+1-1)=2*2^(m-1) := by
      have hm0 : 0 < m := by omega
      have hs : m=m-1+1 := by omega
      conv_lhs => rw [show m+1-1=m by omega,hs,pow_succ]
      omega
    rw [he]
    nlinarith only [hh,hk]

/-- All sample sizes fit for n >= 2^222, and the terminal correction is
at most 1/n. This threshold concerns regularization only. -/
theorem explicit_sample_threshold (n : ℕ) (hn : 2^222 ≤ n) :
    regularizationCoefficient*(Nat.clog 2 n)^8 ≤ n ∧
      1/(2:ℝ)^(Nat.clog 2 n) ≤ 1/(n:ℝ) := by
  have hnTwo : 2 ≤ n := (by norm_num : 2 ≤ 2^222).trans hn
  have hm : 222 ≤ Nat.clog 2 n := by
    have hh := Nat.clog_mono_right 2 hn
    simpa only [Nat.clog_pow 2 222 (by norm_num)] using hh
  have hFit := samples_fit_from_base 222 (by norm_num)
    (by norm_num [regularizationCoefficient]) (Nat.clog 2 n) hm
  have hSmall : 2^(Nat.clog 2 n-1) < n := by
    simpa only [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self
      (by norm_num : 1 < 2) (by omega : 1 < n)
  refine ⟨hFit.trans hSmall.le,?_⟩
  apply one_div_le_one_div_of_le (by exact_mod_cast (by omega : 0 < n))
  exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) n

#print axioms explicit_sample_threshold
end TypedTriangle.Completion
