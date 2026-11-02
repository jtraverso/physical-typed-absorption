module
public import RequestProject.TypedTriangle.ApplicationsTwoScaleAlgebra
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TypedTriangle.Applications.Latin.TwoScale

/-- The fine sign is balanced in each coarse half. These are intermediate
construction data, not extra hypotheses of the final Latin-square statement. -/
structure OrthogonalSigns {A : Type} [Fintype A] (u v : A → ℝ) : Prop where
  sign_u : ∀ a, u a = 1 ∨ u a = -1
  sign_v : ∀ a, v a = 1 ∨ v a = -1
  sum_u : ∑ a, u a = 0
  sum_v : ∑ a, v a = 0
  sum_uv : ∑ a, u a * v a = 0

def avgPair (f : ℝ → ℝ → ℝ) : ℝ :=
  avgSign (fun u => avgSign (fun v => f u v))

/-- Exact quadrature for arbitrary functions of a coarse/fine sign pair.
In particular, no independence between different vertices is postulated. -/
theorem sum_sign_pair {A : Type} [Fintype A] {u v : A → ℝ}
    (h : OrthogonalSigns u v) (f : ℝ → ℝ → ℝ) :
    (∑ a, f (u a) (v a)) = (Fintype.card A : ℝ) * avgPair f := by
  have point (a : A) : f (u a) (v a) =
      (f 1 1 * ((1+u a)*(1+v a)) +
       f 1 (-1) * ((1+u a)*(1-v a)) +
       f (-1) 1 * ((1-u a)*(1+v a)) +
       f (-1) (-1) * ((1-u a)*(1-v a))) / 4 := by
    rcases h.sign_u a with hu | hu <;> rcases h.sign_v a with hv | hv <;>
      rw [hu, hv] <;> ring
  have moments (x y : ℝ) := sum_two_factors u v x y h.sum_u h.sum_v h.sum_uv
  have mm := moments (-1) (-1)
  have mp := moments (-1) 1
  have pm := moments 1 (-1)
  have pp := moments 1 1
  simp only [neg_one_mul, one_mul, ← sub_eq_add_neg] at mm mp pm pp
  simp_rw [point]
  rw [← sum_div]
  simp only [sum_add_distrib, ← mul_sum, mm, mp, pm, pp]
  dsimp [avgPair, avgSign]
  ring

theorem sign_factor_bounds (θ a b c : ℝ) (hθ : 0 ≤ θ)
    (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1) (hc : c=1 ∨ c= -1) :
    1-θ ≤ 1+θ*a*b*c ∧ 1+θ*a*b*c ≤ 1+θ := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> constructor <;> nlinarith

theorem profile_bounds {A : Type} [Fintype A]
    (θ t : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (ht : 0≤t) (ht1 : t≤1)
    (σ τ υ ξ ζ χ : A → ℝ)
    (hσ : ∀ a, σ a=1 ∨ σ a= -1) (hτ : ∀ a, τ a=1 ∨ τ a= -1)
    (hυ : ∀ a, υ a=1 ∨ υ a= -1) (hξ : ∀ a, ξ a=1 ∨ ξ a= -1)
    (hζ : ∀ a, ζ a=1 ∨ ζ a= -1) (hχ : ∀ a, χ a=1 ∨ χ a= -1) :
    ∀ r c s, (1-θ)*(1-t)/(Fintype.card A : ℝ) ≤ profile θ t σ τ υ ξ ζ χ r c s ∧
      profile θ t σ τ υ ξ ζ χ r c s ≤ (1+θ)*(1+t)/(Fintype.card A : ℝ) := by
  intro r c s
  obtain ⟨ha, hb⟩ := sign_factor_bounds θ (σ r) (τ c) (υ s) hθ (hσ r) (hτ c) (hυ s)
  obtain ⟨hc, hd⟩ := sign_factor_bounds t (ξ r) (ζ c) (χ s) ht (hξ r) (hζ c) (hχ s)
  have hleft := mul_le_mul ha hc (sub_nonneg.mpr ht1) (by linarith : 0≤1+θ*σ r*τ c*υ s)
  have hright := mul_le_mul hb hd (by linarith : 0≤1+t*ξ r*ζ c*χ s) (by linarith : 0≤1+θ)
  exact ⟨div_le_div_of_nonneg_right hleft (Nat.cast_nonneg _),
    div_le_div_of_nonneg_right hright (Nat.cast_nonneg _)⟩

/-- The two lower-order moment identities imply exact balance in each half. -/
theorem sum_fine_on_half {A : Type} [Fintype A] {u v : A → ℝ}
    (h : OrthogonalSigns u v) (s : ℝ) (hs : s=1 ∨ s= -1) :
    ∑ a ∈ univ.filter (fun a => u a=s), v a = 0 := by
  rw [sum_filter]
  rw [sum_sign_pair h (fun x y => if x=s then y else 0)]
  rcases hs with rfl | rfl <;> norm_num [avgPair, avgSign]

theorem card_coarse_half {A : Type} [Fintype A] {u v : A → ℝ}
    (h : OrthogonalSigns u v) (s : ℝ) (hs : s=1 ∨ s= -1) :
    ((univ.filter (fun a => u a=s)).card : ℝ) = (Fintype.card A : ℝ)/2 := by
  have he := sum_sign_pair h (fun x _ => if x=s then 1 else 0)
  have hc : (∑ a : A, if u a=s then (1:ℝ) else 0) =
      ((univ.filter (fun a => u a=s)).card : ℝ) := by
    rw [← sum_filter]
    simp
  rw [hc] at he
  rcases hs with rfl | rfl <;> norm_num [avgPair, avgSign] at he <;> linarith

set_option pp.fullNames true
#print axioms sum_sign_pair
#print axioms profile_bounds
#print axioms sum_fine_on_half
#print axioms card_coarse_half
end TypedTriangle.Applications.Latin.TwoScale
