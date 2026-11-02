module
public import RequestProject.TypedTriangle.ApplicationsTwoScaleMoments
public import RequestProject.TypedTriangle.ApplicationsLatinPaschTarget
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace TypedTriangle.Applications.Latin.TwoScale

abbrev SixTuple (A : Type) := (A×A) × (A×A) × (A×A)

def goodTuples (A : Type) [Fintype A] : Finset (SixTuple A) :=
  (univ : Finset A).offDiag ×ˢ ((univ : Finset A).offDiag ×ˢ (univ : Finset A).offDiag)

def boxWeight {A : Type} (p : A → A → A → ℝ) (x : SixTuple A) : ℝ :=
  p x.1.1 x.2.1.1 x.2.2.1 * p x.1.1 x.2.1.2 x.2.2.2 *
  p x.1.2 x.2.1.1 x.2.2.2 * p x.1.2 x.2.1.2 x.2.2.1

theorem pair_sum_eq_offDiag {A : Type} [Fintype A] (f : A → A → ℝ) :
    distinctPairSum f = ∑ p ∈ (univ : Finset A).offDiag, f p.1 p.2 := by
  have ho : (univ : Finset A).offDiag =
      (univ : Finset (A×A)).filter (fun p => p.1≠p.2) := by ext p; simp
  rw [ho, sum_filter, Fintype.sum_prod_type]
  unfold distinctPairSum
  apply sum_congr rfl
  intro x _
  have he : (univ : Finset A).erase x=univ.filter (fun y => x≠y) := by
    ext y
    simp [ne_comm]
  rw [he,sum_filter]

theorem four_mul_target_eq_good_sum {A : Type} [Fintype A] (p : A → A → A → ℝ) :
    4*Pasch.target (weight p) (allowed (host A) types) =
      ∑ x ∈ goodTuples A, boxWeight p x := by
  rw [four_mul_target_eq_rooted, sum_allowed_eq]
  simp_rw [rooted_target_sum]
  rw [root_first_sum_eq_pair_sums]
  simp only [pair_sum_eq_offDiag, goodTuples, sum_product, boxWeight]

theorem card_bad_tuples {A : Type} [Fintype A] :
    ((univ : Finset (SixTuple A)) \ goodTuples A).card ≤ 3*(Fintype.card A)^5 := by
  let D := (univ : Finset A).diag
  let U := (univ : Finset (A×A))
  let B₁ := D ×ˢ (U ×ˢ U)
  let B₂ := U ×ˢ (D ×ˢ U)
  let B₃ := U ×ˢ (U ×ˢ D)
  have hs : (univ : Finset (SixTuple A)) \ goodTuples A ⊆ B₁ ∪ B₂ ∪ B₃ := by
    intro x hx
    simp only [mem_sdiff,mem_univ,true_and,goodTuples,mem_product,mem_offDiag] at hx
    simp only [B₁,B₂,B₃,D,U,mem_union,mem_product,mem_diag,mem_univ,true_and]
    tauto
  have h₁ : B₁.card=(Fintype.card A)^5 := by
    simp only [B₁,D,U,card_product,diag_card,card_univ,Fintype.card_prod]
    ring
  have h₂ : B₂.card=(Fintype.card A)^5 := by
    simp only [B₂,D,U,card_product,diag_card,card_univ,Fintype.card_prod]
    ring
  have h₃ : B₃.card=(Fintype.card A)^5 := by
    simp only [B₃,D,U,card_product,diag_card,card_univ,Fintype.card_prod]
    ring
  calc
    _ ≤ (B₁ ∪ B₂ ∪ B₃).card := card_le_card hs
    _ ≤ B₁.card+B₂.card+B₃.card := (card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _)
    _ = _ := by rw [h₁,h₂,h₃]; omega

theorem unrestricted_minus_good_bound {A : Type} [Fintype A]
    (f : SixTuple A → ℝ) (B : ℝ) (hB : 0≤B) (hf : ∀ x, 0≤f x ∧ f x≤B) :
    0 ≤ (∑ x, f x)-(∑ x ∈ goodTuples A, f x) ∧
      (∑ x, f x)-(∑ x ∈ goodTuples A, f x) ≤ 3*(Fintype.card A : ℝ)^5*B := by
  have hsplit := sum_sdiff (f := f) (subset_univ (goodTuples A))
  rw [← hsplit]
  simp only [add_sub_cancel_right]
  refine ⟨sum_nonneg (fun x _ => (hf x).1), ?_⟩
  calc
    _ ≤ ∑ _x ∈ ((univ : Finset (SixTuple A)) \ goodTuples A), B :=
      sum_le_sum (fun x _ => (hf x).2)
    _ = (((univ : Finset (SixTuple A)) \ goodTuples A).card : ℝ)*B := by simp
    _ ≤ 3*(Fintype.card A : ℝ)^5*B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast (card_bad_tuples (A := A))

theorem full_profile_box_sum {A : Type} [Fintype A] [Nonempty A]
    {σ τ υ ξ ζ χ : A → ℝ}
    (hr : OrthogonalSigns σ ξ) (hc : OrthogonalSigns τ ζ) (hs : OrthogonalSigns υ χ)
    (θ t : ℝ) :
    (∑ x : SixTuple A, boxWeight (profile θ t σ τ υ ξ ζ χ) x) =
      (Fintype.card A : ℝ)^2*((1+θ^4)*(1+t^4)) := by
  let n : ℝ := Fintype.card A
  have hn : n≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have point (x : SixTuple A) : boxWeight (profile θ t σ τ υ ξ ζ χ) x =
      (parityBox θ (σ x.1.1) (σ x.1.2) (τ x.2.1.1) (τ x.2.1.2) (υ x.2.2.1) (υ x.2.2.2) *
       parityBox t (ξ x.1.1) (ξ x.1.2) (ζ x.2.1.1) (ζ x.2.1.2) (χ x.2.2.1) (χ x.2.2.2))/n^4 := by
    dsimp [boxWeight,profile,parityBox,n]
    ring
  simp_rw [point]
  rw [← sum_div]
  simp only [Fintype.sum_prod_type]
  rw [full_two_scale_moment hr hc hs θ t]
  change n^6*((1+θ^4)*(1+t^4))/n^4=n^2*((1+θ^4)*(1+t^4))
  field_simp
  <;> ring

theorem two_scale_target_error {A : Type} [Fintype A] [Nonempty A]
    {σ τ υ ξ ζ χ : A → ℝ}
    (hr : OrthogonalSigns σ ξ) (hc : OrthogonalSigns τ ζ) (hs : OrthogonalSigns υ χ)
    (θ t : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (ht : 0≤t) (ht1 : t≤1) :
    let n : ℝ := Fintype.card A
    let b := (1+θ)*(1+t)
    0 ≤ ((1+θ^4)*(1+t^4)/4)*n^2-
      Pasch.target (weight (profile θ t σ τ υ ξ ζ χ)) (allowed (host A) types) ∧
    ((1+θ^4)*(1+t^4)/4)*n^2-
      Pasch.target (weight (profile θ t σ τ υ ξ ζ χ)) (allowed (host A) types) ≤ 3*b^4*n/4 := by
  dsimp only
  let n : ℝ := Fintype.card A
  let b := (1+θ)*(1+t)
  let p := profile θ t σ τ υ ξ ζ χ
  have hn : 0<n := Nat.cast_pos.mpr Fintype.card_pos
  have hb : 0≤b := mul_nonneg (by linarith) (by linarith)
  have hbounds := profile_bounds θ t hθ hθ1 ht ht1 σ τ υ ξ ζ χ
    hr.sign_u hc.sign_u hs.sign_u hr.sign_v hc.sign_v hs.sign_v
  have hp (r c s : A) : 0≤p r c s ∧ p r c s≤b/n := by
    refine ⟨le_trans ?_ (hbounds r c s).1, (hbounds r c s).2⟩
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hθ1) (sub_nonneg.mpr ht1)) hn.le
  have hbox (x : SixTuple A) : 0≤boxWeight p x ∧ boxWeight p x≤(b/n)^4 := by
    dsimp [boxWeight]
    refine ⟨mul_nonneg (mul_nonneg (mul_nonneg (hp _ _ _).1 (hp _ _ _).1) (hp _ _ _).1) (hp _ _ _).1, ?_⟩
    calc
      _ ≤ (b/n)*(b/n)*(b/n)*(b/n) := by
        gcongr <;> first | exact (hp _ _ _).1 | exact (hp _ _ _).2
      _ = _ := by ring
  obtain ⟨hl,hu⟩ := unrestricted_minus_good_bound (boxWeight p) ((b/n)^4) (by positivity) hbox
  rw [full_profile_box_sum hr hc hs θ t, ← four_mul_target_eq_good_sum p] at hl hu
  have he : 3*n^5*(b/n)^4=3*b^4*n := by field_simp [hn.ne'] <;> ring
  change _ ≤ 3*n^5*(b/n)^4 at hu
  rw [he] at hu
  constructor <;> dsimp [n,b,p] at * <;> nlinarith only [hl,hu]

set_option pp.fullNames true
#print axioms two_scale_target_error
end TypedTriangle.Applications.Latin.TwoScale
