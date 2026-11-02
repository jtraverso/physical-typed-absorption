module
public import RequestProject.TypedTriangle.ApplicationsTwoScalePairing
public import RequestProject.TypedTriangle.ApplicationsTwoScaleSelection
public import RequestProject.TypedTriangle.ApplicationsLatinSignedProfile
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace TypedTriangle.Applications.Latin.TwoScale

theorem exists_fine_sign_retaining_forms {A J : Type} [Fintype A] [Nonempty A] [Fintype J]
    (σ : A → ℝ) (hsign : ∀ a, σ a=1 ∨ σ a= -1) (hsum : ∑ a, σ a=0)
    (hfour : 4 ∣ Fintype.card A) (a : J → A → ℝ)
    (ha : ∀ j r, |a j r|≤(Fintype.card A : ℝ))
    (t δ : ℝ) (ht : 0≤t) (ht1 : t≤1) (hδ : 0≤δ)
    (hsmall : (Fintype.card J : ℝ)*
      (2*Real.exp (-δ^2*(Fintype.card A : ℝ)/4)) < 1) :
    ∃ ξ : A → ℝ, OrthogonalSigns σ ξ ∧
      ∀ j, |t*∑ r, ξ r*a j r|<δ*(Fintype.card A : ℝ)^2 := by
  obtain ⟨P⟩ := exists_coarse_pairing σ hsign hsum hfour
  let n : ℝ := Fintype.card A
  have hn : 0<n := Nat.cast_pos.mpr Fintype.card_pos
  let d : J → (Bool × Fin P.k) → ℝ :=
    fun j i => t*(a j (P.equiv (i,true))-a j (P.equiv (i,false)))
  have hd (j : J) (i : Bool × Fin P.k) : |d j i|≤2*n := by
    dsimp [d]
    rw [abs_mul,abs_of_nonneg ht]
    calc
      _ ≤ t*(|a j (P.equiv (i,true))|+|a j (P.equiv (i,false))|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) ht
      _ ≤ t*(n+n) := mul_le_mul_of_nonneg_left (add_le_add (ha j _) (ha j _)) ht
      _ ≤ _ := by nlinarith
  have hcard : (Fintype.card (Bool × Fin P.k) : ℝ)=n/2 := by
    have hncard : n=2*(Fintype.card (Bool × Fin P.k) : ℝ) := by
      dsimp [n]
      exact_mod_cast P.card
    linarith
  have hexp : -(δ*n^2)^2/(2*(Fintype.card (Bool × Fin P.k) : ℝ)*(2*n)^2)= -δ^2*n/4 := by
    rw [hcard]
    field_simp [hn.ne']
    <;> ring
  obtain ⟨e,he,hforms⟩ := exists_signs_for_linear_forms d (2*n) (δ*n^2)
    (by positivity) (by positivity) hd (by rw [hexp]; exact hsmall)
  refine ⟨P.fine e, P.fine_orthogonal hsign hsum e he, ?_⟩
  intro j
  have heq : t*(∑ r, P.fine e r*a j r)=∑ i, e i*d j i := by
    rw [P.linear_form e (a j),mul_sum]
    apply sum_congr rfl
    intro i _
    dsimp [d]
    ring
  rw [heq]
  exact hforms j

def rowCoefficient {A : Type} [Fintype A] (θ : ℝ)
    (σ τ υ ζ χ : A → ℝ) (w : A → A → A → ℝ) (r : A) : ℝ :=
  ∑ c,∑ s, signedProfile θ σ τ υ r c s*ζ c*χ s*w r c s

theorem profile_target_difference {A : Type} [Fintype A]
    (θ t : ℝ) (σ τ υ ξ ζ χ : A → ℝ) (w : A → A → A → ℝ) :
    (∑ r,∑ c,∑ s, profile θ t σ τ υ ξ ζ χ r c s*w r c s)-
      (∑ r,∑ c,∑ s, signedProfile θ σ τ υ r c s*w r c s) =
      t*∑ r, ξ r*rowCoefficient θ σ τ υ ζ χ w r := by
  have hp (r c s : A) : profile θ t σ τ υ ξ ζ χ r c s*w r c s-
      signedProfile θ σ τ υ r c s*w r c s =
      t*ξ r*(signedProfile θ σ τ υ r c s*ζ c*χ s*w r c s) := by
    dsimp [profile,signedProfile]
    ring
  calc
    _ = ∑ r,∑ c,∑ s, (profile θ t σ τ υ ξ ζ χ r c s*w r c s-
        signedProfile θ σ τ υ r c s*w r c s) := by simp only [sum_sub_distrib]
    _ = _ := by simp_rw [hp]; simp only [rowCoefficient,mul_sum,mul_assoc]

theorem rowCoefficient_bound {A : Type} [Fintype A] [Nonempty A]
    (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (σ τ υ ζ χ : A → ℝ)
    (hσ : ∀ a, σ a=1 ∨ σ a= -1) (hτ : ∀ a, τ a=1 ∨ τ a= -1)
    (hυ : ∀ a, υ a=1 ∨ υ a= -1) (hζ : ∀ a, ζ a=1 ∨ ζ a= -1)
    (hχ : ∀ a, χ a=1 ∨ χ a= -1) (hυSum : ∑ s, υ s=0)
    (w : A → A → A → ℝ) (hw : ∀ r c s, |w r c s|≤1) (r : A) :
    |rowCoefficient θ σ τ υ ζ χ w r|≤(Fintype.card A : ℝ) := by
  have hp (c s : A) : 0 ≤ signedProfile θ σ τ υ r c s :=
    (div_nonneg (sub_nonneg.mpr hθ1) (Nat.cast_nonneg _)).trans
      (signedProfile_bounds θ hθ σ τ υ hσ hτ hυ r c s).1
  have habsζ (c : A) : |ζ c|=1 := by rcases hζ c with h | h <;> rw [h] <;> norm_num
  have habsχ (s : A) : |χ s|=1 := by rcases hχ s with h | h <;> rw [h] <;> norm_num
  have hline (c : A) : ∑ s, signedProfile θ σ τ υ r c s=1 := by
    have hn : (Fintype.card A : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [signedProfile,←sum_div,sum_add_distrib,←mul_sum,hυSum,hn]
  calc
    _ ≤ ∑ c, |∑ s, signedProfile θ σ τ υ r c s*ζ c*χ s*w r c s| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ c,∑ s, |signedProfile θ σ τ υ r c s*ζ c*χ s*w r c s| :=
      sum_le_sum (fun c _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ c,∑ s, signedProfile θ σ τ υ r c s := by
      apply sum_le_sum
      intro c _
      apply sum_le_sum
      intro s _
      simp only [abs_mul, abs_of_nonneg (hp c s), habsζ, habsχ, mul_one]
      exact (mul_le_mul_of_nonneg_left (hw r c s) (hp c s)).trans_eq (mul_one _)
    _ = _ := by simp [hline]

set_option pp.fullNames true
#print axioms exists_fine_sign_retaining_forms
#print axioms profile_target_difference
#print axioms rowCoefficient_bound
end TypedTriangle.Applications.Latin.TwoScale
