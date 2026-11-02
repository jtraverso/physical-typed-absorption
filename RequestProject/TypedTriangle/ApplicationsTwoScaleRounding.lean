module
public import RequestProject.TypedTriangle.ApplicationsTwoScaleTarget
public import RequestProject.TypedTriangle.ApplicationsLatinCorollaries
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin.TwoScale

def kappa (θ t : ℝ) : ℝ := (1+θ^4)*(1+t^4)/4

def linearTarget {A : Type} [Fintype A]
    (p w : A → A → A → ℝ) : ℝ := ∑ r,∑ c,∑ s,p r c s*w r c s

def linearStatistic {A : Type} [Fintype A]
    (L : LatinSquare A) (w : A → A → A → ℝ) : ℝ := ∑ r,∑ c,w r c (L r c)

/-- A single two-scale seed rounded by T+, with the finite diagonal loss retained. -/
theorem round_two_scale_profile (θ t η : ℝ) (q : ℕ)
    (hθ : 0≤θ) (hθ1 : θ<1) (ht : 0≤t) (ht1 : t<1) (hη : 0<η) :
    ∃ N : ℕ, 2≤N ∧ ∀ (A : Type) [Fintype A], N≤Fintype.card A →
      ∀ (σ τ υ ξ ζ χ : A → ℝ),
      OrthogonalSigns σ ξ → OrthogonalSigns τ ζ → OrthogonalSigns υ χ →
      ∀ (J : Type) [Fintype J] (w : J → A → A → A → ℝ),
      (Fintype.card J : ℝ)≤(Fintype.card A : ℝ)^q →
      (∀ j r c s, |w j r c s|≤1) →
      ∃ L : LatinSquare A,
        (∀ j, |linearStatistic L (w j)-linearTarget (profile θ t σ τ υ ξ ζ χ) (w j)|≤
          η*(Fintype.card A : ℝ)^2) ∧
        |((intercalates L).card : ℝ)-kappa θ t*(Fintype.card A : ℝ)^2|≤
          η*(Fintype.card A : ℝ)^2+3*((1+θ)*(1+t))^4*(Fintype.card A : ℝ)/4 := by
  obtain ⟨N,hN,hMain⟩ := latin_square_with_profile_statistics
    ((1-θ)*(1-t)) ((1+θ)*(1+t)) η q
    (mul_pos (sub_pos.mpr hθ1) (sub_pos.mpr ht1)) hη
  refine ⟨N,hN,?_⟩
  intro A _ hn σ τ υ ξ ζ χ hr hc hs J _ w hJ hw
  letI : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨hm1,hm2,hm3⟩ := profile_marginals θ t σ τ υ ξ ζ χ
    hr.sum_u hc.sum_u hs.sum_u hr.sum_v hc.sum_v hs.sum_v hr.sum_uv hc.sum_uv hs.sum_uv
  obtain ⟨L,hstat,hcount⟩ := hMain A hn (profile θ t σ τ υ ξ ζ χ)
    (profile_bounds θ t hθ hθ1.le ht ht1.le σ τ υ ξ ζ χ
      hr.sign_u hc.sign_u hs.sign_u hr.sign_v hc.sign_v hs.sign_v)
    hm1 hm2 hm3 J w hJ hw
  rw [count_decomposition_eq_intercalates] at hcount
  obtain ⟨hlo,hup⟩ := two_scale_target_error hr hc hs θ t hθ hθ1.le ht ht1.le
  have herr : |Pasch.target (weight (profile θ t σ τ υ ξ ζ χ)) (allowed (host A) types)-
      kappa θ t*(Fintype.card A : ℝ)^2|≤3*((1+θ)*(1+t))^4*(Fintype.card A : ℝ)/4 := by
    rw [abs_sub_comm]
    unfold kappa
    rw [abs_of_nonneg hlo]
    exact hup
  refine ⟨L,hstat,?_⟩
  exact (abs_sub_le _ _ _).trans (add_le_add hcount herr)

theorem polynomial_sign_budget (δ : ℝ) (q : ℕ) (hδ : 0<δ) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n → 2*(n:ℝ)^q*Real.exp (-δ^2*(n:ℝ)/4)<1 := by
  have hc : 0<δ^2/4 := by positivity
  have hlim : Filter.Tendsto (fun x : ℝ => x^q*Real.exp (-(δ^2/4)*x))
      Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (q:ℕ) (δ^2/4) hc
  have hlim2 := (hlim.const_mul 2).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1
    (hlim2.eventually (gt_mem_nhds (by norm_num : (2:ℝ)*0<1)))
  refine ⟨N,fun n hn => ?_⟩
  have he : -(δ^2/4)*(n:ℝ)= -δ^2*(n:ℝ)/4 := by ring
  simpa only [Function.comp_apply,he,mul_assoc] using hN n hn

set_option pp.fullNames true
#print axioms round_two_scale_profile
#print axioms polynomial_sign_budget
end TypedTriangle.Applications.Latin.TwoScale
