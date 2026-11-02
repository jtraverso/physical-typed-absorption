module
public import Mathlib
@[expose] public section
namespace TypedTriangle.TowerBounds

/-- Base-two towers are specified by their finite natural height. -/
def tower2 : ℕ → ℕ
  | 0 => 1
  | n+1 => 2 ^ tower2 n

theorem tower2_pos (n : ℕ) : 0 < tower2 n := by
  cases n <;> simp [tower2]

theorem self_le_tower2 (n : ℕ) : n ≤ tower2 n := by
  induction n with
  | zero => simp [tower2]
  | succ n ih =>
      change n+1 ≤ 2 ^ tower2 n
      exact (Nat.succ_le_of_lt n.lt_two_pow_self).trans
        (Nat.pow_le_pow_right (by decide) ih)

/-- Simultaneously controls the size and reciprocal of a positive real.
The bound is natural, so compositions can be majorized by integer programs. -/
structure Magnitude (M : ℕ) (x : ℝ) : Prop where
  pos : 0 < x
  upper : x ≤ (M : ℝ)
  inv_upper : 1 / x ≤ (M : ℝ)

namespace Magnitude

theorem bound_pos {M : ℕ} {x : ℝ} (hx : Magnitude M x) : 0 < M := by
  exact_mod_cast hx.pos.trans_le hx.upper

theorem mono {M N : ℕ} {x : ℝ} (hx : Magnitude M x) (hMN : M ≤ N) :
    Magnitude N x := by
  have h : (M : ℝ) ≤ N := by exact_mod_cast hMN
  exact ⟨hx.pos,hx.upper.trans h,hx.inv_upper.trans h⟩

theorem one : Magnitude 1 (1 : ℝ) := by
  constructor <;> norm_num

theorem natCast {M n : ℕ} (hn : 1 ≤ n) (hnM : n ≤ M) :
    Magnitude M (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast hn.trans hnM
  refine ⟨by positivity,by exact_mod_cast hnM,?_⟩
  have hi : 1/(n : ℝ) ≤ 1 := by
    simpa only [one_div_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnR
  exact hi.trans hM

theorem inv {M : ℕ} {x : ℝ} (hx : Magnitude M x) : Magnitude M (1/x) := by
  refine ⟨div_pos (by norm_num) hx.pos,hx.inv_upper,?_⟩
  simpa only [one_div_one_div] using hx.upper

theorem add {M N : ℕ} {x y : ℝ} (hx : Magnitude M x) (hy : Magnitude N y) :
    Magnitude (M+N) (x+y) := by
  refine ⟨add_pos hx.pos hy.pos,?_,?_⟩
  · exact_mod_cast add_le_add hx.upper hy.upper
  · have h : 1/(x+y) ≤ 1/x := one_div_le_one_div_of_le hx.pos (le_add_of_nonneg_right hy.pos.le)
    exact h.trans (hx.inv_upper.trans (by exact_mod_cast Nat.le_add_right M N))

theorem mul {M N : ℕ} {x y : ℝ} (hx : Magnitude M x) (hy : Magnitude N y) :
    Magnitude (M*N) (x*y) := by
  refine ⟨mul_pos hx.pos hy.pos,?_,?_⟩
  · simpa only [Nat.cast_mul] using
      mul_le_mul hx.upper hy.upper hy.pos.le (Nat.cast_nonneg M)
  · simpa only [one_div_mul_one_div,Nat.cast_mul] using
      mul_le_mul hx.inv_upper hy.inv_upper (div_nonneg (by norm_num) hy.pos.le) (Nat.cast_nonneg M)

theorem div {M N : ℕ} {x y : ℝ} (hx : Magnitude M x) (hy : Magnitude N y) :
    Magnitude (M*N) (x/y) := by
  simpa only [div_eq_mul_inv,one_div,one_mul] using hx.mul hy.inv

theorem min {M N : ℕ} {x y : ℝ} (hx : Magnitude M x) (hy : Magnitude N y) :
    Magnitude (max M N) (min x y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    exact hx.mono (le_max_left _ _)
  · rw [min_eq_right h]
    exact hy.mono (le_max_right _ _)

theorem max {M N : ℕ} {x y : ℝ} (hx : Magnitude M x) (hy : Magnitude N y) :
    Magnitude (max M N) (max x y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]
    exact hy.mono (le_max_right _ _)
  · rw [max_eq_left h]
    exact hx.mono (le_max_left _ _)

theorem pow {M : ℕ} {x : ℝ} (hx : Magnitude M x) (n : ℕ) :
    Magnitude (M^n) (x^n) := by
  refine ⟨pow_pos hx.pos n,?_,?_⟩
  · simpa only [Nat.cast_pow] using pow_le_pow_left₀ hx.pos.le hx.upper n
  · simpa only [one_div_pow,Nat.cast_pow] using
      pow_le_pow_left₀ (div_nonneg (by norm_num) hx.pos.le) hx.inv_upper n

theorem ceil_le {M : ℕ} {x : ℝ} (hx : Magnitude M x) : ⌈x⌉₊ ≤ M :=
  Nat.ceil_le.mpr hx.upper

theorem ceil_pos {M : ℕ} {x : ℝ} (hx : Magnitude M x) : 0 < ⌈x⌉₊ :=
  Nat.ceil_pos.mpr hx.pos

theorem lower {M : ℕ} {x : ℝ} (hx : Magnitude M x) : 1/(M : ℝ) ≤ x := by
  have hM : (0 : ℝ) < M := by exact_mod_cast hx.bound_pos
  exact (div_le_iff₀ hM).mpr (by
    have h := (div_le_iff₀ hx.pos).mp hx.inv_upper
    simpa only [mul_comm] using h)

end Magnitude

#print axioms self_le_tower2
#print axioms Magnitude.mul
#print axioms Magnitude.pow
end TypedTriangle.TowerBounds
