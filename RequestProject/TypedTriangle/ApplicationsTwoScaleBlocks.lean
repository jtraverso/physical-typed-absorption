module
public import RequestProject.TypedTriangle.ApplicationsTwoScalePairing
public import RequestProject.TypedTriangle.ApplicationsLatinSignedProfile
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace TypedTriangle.Applications.Latin.TwoScale

def blockWeight {A : Type} (σ τ υ : A → ℝ) (a b d : ℝ) (r c s : A) : ℝ :=
  if σ r=a ∧ τ c=b ∧ υ s=d then 1 else 0

theorem blockWeight_bound {A : Type} (σ τ υ : A → ℝ) (a b d : ℝ) (r c s : A) :
    |blockWeight σ τ υ a b d r c s| ≤ 1 := by
  unfold blockWeight
  split <;> norm_num

theorem block_target {A : Type} [Fintype A] [Nonempty A]
    {σ τ υ ξ ζ χ : A → ℝ} (hr : OrthogonalSigns σ ξ)
    (hc : OrthogonalSigns τ ζ) (hs : OrthogonalSigns υ χ)
    (θ a b d : ℝ) (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1)
    (hd : d=1 ∨ d= -1) :
    (∑ r,∑ c,∑ s, signedProfile θ σ τ υ r c s*blockWeight σ τ υ a b d r c s) =
      (1+θ*a*b*d)*(Fintype.card A : ℝ)^2/8 := by
  have hp (r c s : A) : signedProfile θ σ τ υ r c s*blockWeight σ τ υ a b d r c s =
      if σ r=a then (if τ c=b then (if υ s=d then
        (1+θ*a*b*d)/(Fintype.card A : ℝ) else 0) else 0) else 0 := by
    by_cases hr : σ r=a <;> by_cases hc : τ c=b <;> by_cases hs : υ s=d <;>
      simp [blockWeight,signedProfile,hr,hc,hs]
  simp_rw [hp]
  have hsum (u : A → ℝ) (x z : ℝ) :
      (∑ y, if u y=x then z else 0) = ((univ.filter (fun y => u y=x)).card : ℝ)*z := by
    rw [← sum_filter]
    simp
  simp_rw [sum_ite_irrel, sum_const_zero, hsum]
  rw [card_coarse_half hs d hd, card_coarse_half hc b hb, card_coarse_half hr a ha]
  have hn : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  <;> ring

set_option pp.fullNames true
#print axioms block_target
end TypedTriangle.Applications.Latin.TwoScale
