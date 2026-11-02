module
public import RequestProject.TypedTriangle.ApplicationsTwoScaleQuadrature
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace TypedTriangle.Applications.Latin.TwoScale

theorem sum_scaled_pair_product {A : Type} [Fintype A] {u v : A → ℝ}
    (h : OrthogonalSigns u v) (c : ℝ) (f g : ℝ → ℝ) :
    (∑ a, c*(f (u a)*g (v a))) =
      (c*(Fintype.card A : ℝ))*(avgSign f*avgSign g) := by
  rw [← mul_sum, sum_sign_pair h (fun x y => f x*g y)]
  dsimp [avgPair, avgSign]
  ring

def avgSix (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ :=
  avgSign (fun a => avgSign (fun b => avgSign (fun c => avgSign (fun d =>
    avgSign (fun e => avgSign (fun z => f a b c d e z))))))

/-- Tensorization of the finite quadrature, before excluding diagonal tuples. -/
theorem sum_six_pair_products {A : Type} [Fintype A] {σ τ υ ξ ζ χ : A → ℝ}
    (hr : OrthogonalSigns σ ξ) (hc : OrthogonalSigns τ ζ) (hs : OrthogonalSigns υ χ)
    (f g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) :
    (∑ r,∑ r',∑ c,∑ c',∑ s,∑ s',
      f (σ r) (σ r') (τ c) (τ c') (υ s) (υ s') *
      g (ξ r) (ξ r') (ζ c) (ζ c') (χ s) (χ s')) =
      (Fintype.card A : ℝ)^6 * (avgSix f*avgSix g) := by
  let n : ℝ := Fintype.card A
  let f5 a b c d e := avgSign (fun z => f a b c d e z)
  let g5 a b c d e := avgSign (fun z => g a b c d e z)
  let f4 a b c d := avgSign (fun e => f5 a b c d e)
  let g4 a b c d := avgSign (fun e => g5 a b c d e)
  let f3 a b c := avgSign (fun d => f4 a b c d)
  let g3 a b c := avgSign (fun d => g4 a b c d)
  let f2 a b := avgSign (fun c => f3 a b c)
  let g2 a b := avgSign (fun c => g3 a b c)
  let f1 a := avgSign (fun b => f2 a b)
  let g1 a := avgSign (fun b => g2 a b)
  have h6 (r r' c c' s : A) :
      (∑ s', f (σ r) (σ r') (τ c) (τ c') (υ s) (υ s') *
        g (ξ r) (ξ r') (ζ c) (ζ c') (χ s) (χ s')) =
      n*(f5 (σ r) (σ r') (τ c) (τ c') (υ s)*g5 (ξ r) (ξ r') (ζ c) (ζ c') (χ s)) := by
    simpa [f5,g5,n] using sum_scaled_pair_product hs 1
      (f (σ r) (σ r') (τ c) (τ c') (υ s))
      (g (ξ r) (ξ r') (ζ c) (ζ c') (χ s))
  simp_rw [h6]
  have h5 (r r' c c' : A) :
      (∑ s, n*(f5 (σ r) (σ r') (τ c) (τ c') (υ s)*g5 (ξ r) (ξ r') (ζ c) (ζ c') (χ s))) =
      (n*n)*(f4 (σ r) (σ r') (τ c) (τ c')*g4 (ξ r) (ξ r') (ζ c) (ζ c')) :=
    sum_scaled_pair_product hs n _ _
  simp_rw [h5]
  have h4 (r r' c : A) :
      (∑ c', (n*n)*(f4 (σ r) (σ r') (τ c) (τ c')*g4 (ξ r) (ξ r') (ζ c) (ζ c'))) =
      (n*n*n)*(f3 (σ r) (σ r') (τ c)*g3 (ξ r) (ξ r') (ζ c)) :=
    sum_scaled_pair_product hc (n*n) _ _
  simp_rw [h4]
  have h3 (r r' : A) :
      (∑ c, (n*n*n)*(f3 (σ r) (σ r') (τ c)*g3 (ξ r) (ξ r') (ζ c))) =
      (n*n*n*n)*(f2 (σ r) (σ r')*g2 (ξ r) (ξ r')) :=
    sum_scaled_pair_product hc (n*n*n) _ _
  simp_rw [h3]
  have h2 (r : A) :
      (∑ r', (n*n*n*n)*(f2 (σ r) (σ r')*g2 (ξ r) (ξ r'))) =
      (n*n*n*n*n)*(f1 (σ r)*g1 (ξ r)) :=
    sum_scaled_pair_product hr (n*n*n*n) _ _
  simp_rw [h2]
  rw [sum_scaled_pair_product hr (n*n*n*n*n) f1 g1]
  change (n*n*n*n*n*n)*(avgSix f*avgSix g)=n^6*(avgSix f*avgSix g)
  ring

theorem full_two_scale_moment {A : Type} [Fintype A] {σ τ υ ξ ζ χ : A → ℝ}
    (hr : OrthogonalSigns σ ξ) (hc : OrthogonalSigns τ ζ) (hs : OrthogonalSigns υ χ)
    (θ t : ℝ) :
    (∑ r,∑ r',∑ c,∑ c',∑ s,∑ s',
      parityBox θ (σ r) (σ r') (τ c) (τ c') (υ s) (υ s') *
      parityBox t (ξ r) (ξ r') (ζ c) (ζ c') (χ s) (χ s')) =
      (Fintype.card A : ℝ)^6*((1+θ^4)*(1+t^4)) := by
  rw [sum_six_pair_products hr hc hs]
  change _*(avgSix (parityBox θ)*avgSix (parityBox t))=_
  have hθ : avgSix (parityBox θ)=1+θ^4 := full_moment θ
  have ht : avgSix (parityBox t)=1+t^4 := full_moment t
  rw [hθ,ht]

set_option pp.fullNames true
#print axioms sum_six_pair_products
#print axioms full_two_scale_moment
end TypedTriangle.Applications.Latin.TwoScale
