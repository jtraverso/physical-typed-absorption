module
public import Mathlib
@[expose] public section
open Finset
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PaperIII.Research.TwoScale

/-- Uniform average over a single sign; not a probabilistic assumption. -/
def avgSign (f : ℝ → ℝ) : ℝ := (f 1 + f (-1)) / 2

def parityBox (θ a a' b b' c c' : ℝ) : ℝ :=
  (1+θ*a*b*c)*(1+θ*a*b'*c')*(1+θ*a'*b*c')*(1+θ*a'*b'*c)

theorem full_moment (θ : ℝ) :
    avgSign (fun a => avgSign (fun a' => avgSign (fun b => avgSign (fun b' =>
      avgSign (fun c => avgSign (fun c' => parityBox θ a a' b b' c c')))))) = 1+θ^4 := by
  dsimp [avgSign, parityBox]
  ring

theorem one_collision_moment (θ : ℝ) :
    avgSign (fun a => avgSign (fun b => avgSign (fun b' =>
      avgSign (fun c => avgSign (fun c' => parityBox θ a a b b' c c'))))) = 1+θ^4 := by
  dsimp [avgSign, parityBox]
  ring

theorem two_collision_moment (θ : ℝ) :
    avgSign (fun a => avgSign (fun b => avgSign (fun c =>
      avgSign (fun c' => parityBox θ a a b b c c')))) = (1+θ^2)^2 := by
  dsimp [avgSign, parityBox]
  ring

theorem three_collision_moment (θ : ℝ) :
    avgSign (fun a => avgSign (fun b => avgSign (fun c =>
      parityBox θ a a b b c c))) = 1+6*θ^2+θ^4 := by
  dsimp [avgSign, parityBox]
  ring

/-- Orthogonality of the two signs is the precise marginal hypothesis. -/
theorem sum_two_factors {A : Type} [Fintype A] (u v : A → ℝ) (x y : ℝ)
    (hu : ∑ a,u a=0) (hv : ∑ a,v a=0) (huv : ∑ a,u a*v a=0) :
    (∑ a,(1+x*u a)*(1+y*v a)) = (Fintype.card A : ℝ) := by
  have he (a : A) : (1+x*u a)*(1+y*v a) =
      1+x*u a+y*v a+(x*y)*(u a*v a) := by ring
  simp_rw [he]
  simp only [sum_add_distrib, ←mul_sum, hu, hv, huv, mul_zero, add_zero]
  simp

def profile {A : Type} [Fintype A] (θ t : ℝ)
    (σ τ υ ξ ζ χ : A → ℝ) (r c s : A) : ℝ :=
  ((1+θ*σ r*τ c*υ s)*(1+t*ξ r*ζ c*χ s))/(Fintype.card A : ℝ)

theorem profile_marginals {A : Type} [Fintype A] [Nonempty A] (θ t : ℝ)
    (σ τ υ ξ ζ χ : A → ℝ)
    (hσ : ∑ x,σ x=0) (hτ : ∑ x,τ x=0) (hυ : ∑ x,υ x=0)
    (hξ : ∑ x,ξ x=0) (hζ : ∑ x,ζ x=0) (hχ : ∑ x,χ x=0)
    (hσξ : ∑ x,σ x*ξ x=0) (hτζ : ∑ x,τ x*ζ x=0) (hυχ : ∑ x,υ x*χ x=0) :
    (∀ r c,∑ s,profile θ t σ τ υ ξ ζ χ r c s=1) ∧
    (∀ r s,∑ c,profile θ t σ τ υ ξ ζ χ r c s=1) ∧
    (∀ c s,∑ r,profile θ t σ τ υ ξ ζ χ r c s=1) := by
  have hn : (Fintype.card A : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨?_,?_,?_⟩
  · intro r c
    simp only [profile,←sum_div]
    rw [sum_two_factors υ χ (θ*σ r*τ c) (t*ξ r*ζ c) hυ hχ hυχ]
    exact div_self hn
  · intro r s
    simp only [profile,←sum_div]
    have he (c : A) : (1+θ*σ r*τ c*υ s)*(1+t*ξ r*ζ c*χ s)=
        (1+(θ*σ r*υ s)*τ c)*(1+(t*ξ r*χ s)*ζ c) := by ring
    simp_rw [he]
    rw [sum_two_factors τ ζ (θ*σ r*υ s) (t*ξ r*χ s) hτ hζ hτζ]
    exact div_self hn
  · intro c s
    simp only [profile,←sum_div]
    have he (r : A) : (1+θ*σ r*τ c*υ s)*(1+t*ξ r*ζ c*χ s)=
        (1+(θ*τ c*υ s)*σ r)*(1+(t*ζ c*χ s)*ξ r) := by ring
    simp_rw [he]
    rw [sum_two_factors σ ξ (θ*τ c*υ s) (t*ζ c*χ s) hσ hξ hσξ]
    exact div_self hn

/-- Closed expression proposed for the target. Its combinatorial identification
is proved in PROOF_es.txt, not asserted as a formal theorem in this module. -/
def targetExpression (n θ t : ℝ) : ℝ :=
  ((1+θ^4)*(1+t^4)*(n^2-3*n)+
    3*(1+θ^2)^2*(1+t^2)^2-(1+6*θ^2+θ^4)*(1+6*t^2+t^4)/n)/4

theorem target_inclusion_exclusion_algebra (n θ t : ℝ) (hn : n≠0) :
    ((n^6-3*n^5)*((1+θ^4)*(1+t^4))+
      3*n^4*((1+θ^2)^2*(1+t^2)^2)-
      n^3*((1+6*θ^2+θ^4)*(1+6*t^2+t^4)))/(4*n^4)=
        targetExpression n θ t := by
  unfold targetExpression
  field_simp

theorem half_profile_target (n t : ℝ) :
    targetExpression n (1/2) t =
      (17*(1+t^4)*(n^2-3*n)+75*(1+t^2)^2-41*(1+6*t^2+t^4)/n)/64 := by
  unfold targetExpression
  ring

theorem half_profile_leading_gain (t : ℝ) (ht : t^4=1/2) :
    (1+(1/2 : ℝ)^4)*(1+t^4)/4=51/128 ∧
      (51/128 : ℝ)=(3/2)*(17/64) := by
  rw [ht]
  norm_num

#print axioms full_moment
#print axioms one_collision_moment
#print axioms two_collision_moment
#print axioms three_collision_moment
#print axioms sum_two_factors
#print axioms profile_marginals
#print axioms target_inclusion_exclusion_algebra
#print axioms half_profile_target
#print axioms half_profile_leading_gain
end PaperIII.Research.TwoScale
