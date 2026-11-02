module
public import RequestProject.TypedTriangle.ApplicationsLatinProfile
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace TypedTriangle.Applications.Latin

/-- A bounded rank-one perturbation of the uniform stochastic array. -/
def signedProfile {A : Type} [Fintype A] (θ : ℝ) (σ τ υ : A → ℝ) (x y z : A) : ℝ :=
  (1+θ*σ x*τ y*υ z)/(Fintype.card A : ℝ)

theorem signedProfile_marginals {A : Type} [Fintype A] [Nonempty A]
    (θ : ℝ) (σ τ υ : A → ℝ)
    (hσ : ∑ x,σ x=0) (hτ : ∑ y,τ y=0) (hυ : ∑ z,υ z=0) :
    (∀ x y,∑ z,signedProfile θ σ τ υ x y z=1) ∧
    (∀ x z,∑ y,signedProfile θ σ τ υ x y z=1) ∧
    (∀ y z,∑ x,signedProfile θ σ τ υ x y z=1) := by
  have hn : (Fintype.card A : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨?_,?_,?_⟩
  · intro x y
    simp only [signedProfile,←Finset.sum_div]
    simp [Finset.sum_add_distrib,←Finset.mul_sum,hυ,hn]
  · intro x z
    simp only [signedProfile,←Finset.sum_div]
    have he (y : A) : 1+θ*σ x*τ y*υ z=1+(θ*σ x*υ z)*τ y := by ring
    simp_rw [he]
    simp [Finset.sum_add_distrib,←Finset.mul_sum,hτ,hn]
  · intro y z
    simp only [signedProfile,←Finset.sum_div]
    have he (x : A) : 1+θ*σ x*τ y*υ z=1+(θ*τ y*υ z)*σ x := by ring
    simp_rw [he]
    simp [Finset.sum_add_distrib,←Finset.mul_sum,hσ,hn]

theorem signedProfile_bounds {A : Type} [Fintype A] [Nonempty A]
    (θ : ℝ) (hθ : 0≤θ) (σ τ υ : A → ℝ)
    (hσ : ∀ x,σ x=1 ∨ σ x= -1) (hτ : ∀ y,τ y=1 ∨ τ y= -1)
    (hυ : ∀ z,υ z=1 ∨ υ z= -1) :
    ∀ x y z,(1-θ)/Fintype.card A ≤ signedProfile θ σ τ υ x y z ∧
      signedProfile θ σ τ υ x y z ≤ (1+θ)/Fintype.card A := by
  intro x y z
  have hn : (0:ℝ)≤Fintype.card A := Nat.cast_nonneg _
  have hProd : -1≤σ x*τ y*υ z ∧ σ x*τ y*υ z≤1 := by
    rcases hσ x with hs|hs <;> rcases hτ y with ht|ht <;>
      rcases hυ z with hu|hu <;> simp [hs,ht,hu]
  have hLow : 1-θ ≤ 1+θ*σ x*τ y*υ z := by
    have hh := mul_le_mul_of_nonneg_left hProd.1 hθ
    nlinarith only [hh]
  have hHigh : 1+θ*σ x*τ y*υ z ≤ 1+θ := by
    have hh := mul_le_mul_of_nonneg_left hProd.2 hθ
    nlinarith only [hh]
  exact ⟨div_le_div_of_nonneg_right hLow hn,div_le_div_of_nonneg_right hHigh hn⟩

theorem signedProfile_diffuse {A : Type} [Fintype A] [Nonempty A]
    (θ : ℝ) (hθ : 0≤θ) (hθOne : θ<1) (σ τ υ : A → ℝ)
    (hσ : ∀ x,σ x=1 ∨ σ x= -1) (hτ : ∀ y,τ y=1 ∨ τ y= -1)
    (hυ : ∀ z,υ z=1 ∨ υ z= -1)
    (hσSum : ∑ x,σ x=0) (hτSum : ∑ y,τ y=0) (hυSum : ∑ z,υ z=0) :
    IsDiffuseSeed (host A) types (profileConstant (1-θ) (1+θ))
      (weight (signedProfile θ σ τ υ)) := by
  obtain ⟨h01,h02,h12⟩ := signedProfile_marginals θ σ τ υ hσSum hτSum hυSum
  exact diffuse_of_profile (1-θ) (1+θ) (by linarith only [hθOne])
    (signedProfile θ σ τ υ) (signedProfile_bounds θ hθ σ τ υ hσ hτ hυ) h01 h02 h12

#print axioms signedProfile_diffuse
end TypedTriangle.Applications.Latin
