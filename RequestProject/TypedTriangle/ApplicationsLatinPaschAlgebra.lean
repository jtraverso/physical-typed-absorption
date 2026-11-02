module
public import Mathlib
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace TypedTriangle.Applications.Latin

/-- Sum over the two distinct entries of an ordered pair. -/
def distinctPairSum {A : Type} [Fintype A] (f : A → A → ℝ) : ℝ :=
  ∑ x, ∑ y ∈ (univ : Finset A).erase x, f x y

theorem distinctPairSum_add {A : Type} [Fintype A] (f g : A → A → ℝ) :
    distinctPairSum (fun x y => f x y+g x y)=distinctPairSum f+distinctPairSum g := by
  simp [distinctPairSum,sum_add_distrib]

theorem distinctPairSum_mul_left {A : Type} [Fintype A] (a : ℝ) (f : A → A → ℝ) :
    distinctPairSum (fun x y => a*f x y)=a*distinctPairSum f := by
  simp only [distinctPairSum,mul_sum]

theorem distinctPairSum_mul_right {A : Type} [Fintype A] (f : A → A → ℝ) (a : ℝ) :
    distinctPairSum (fun x y => f x y*a)=distinctPairSum f*a := by
  simp only [distinctPairSum,sum_mul]

theorem distinctPairSum_neg {A : Type} [Fintype A] (f : A → A → ℝ) :
    distinctPairSum (fun x y => -f x y)= -distinctPairSum f := by
  simp only [distinctPairSum,sum_neg_distrib]

theorem distinctPairSum_const {A : Type} [Fintype A] [Nonempty A] (a : ℝ) :
    distinctPairSum (A:=A) (fun _ _ => a)=
      (Fintype.card A : ℝ)*((Fintype.card A : ℝ)-1)*a := by
  have hn : 1 ≤ Fintype.card A := Fintype.card_pos
  simp [distinctPairSum,card_erase_of_mem,Nat.cast_sub hn,mul_assoc,mul_comm,mul_left_comm]

theorem balanced_distinctPairSum_first {A : Type} [Fintype A] [Nonempty A]
    (σ : A → ℝ) (hσ : ∑ x,σ x=0) :
    distinctPairSum (fun x _ => σ x)=0 := by
  have hn : 1 ≤ Fintype.card A := Fintype.card_pos
  simp only [distinctPairSum,sum_const,card_erase_of_mem (mem_univ _),card_univ,
    nsmul_eq_mul,Nat.cast_sub hn,Nat.cast_one,←mul_sum,hσ,mul_zero]

theorem balanced_distinctPairSum_second {A : Type} [Fintype A]
    (σ : A → ℝ) (hσ : ∑ x,σ x=0) :
    distinctPairSum (fun _ y => σ y)=0 := by
  have he (x : A) : ∑ y ∈ (univ : Finset A).erase x,σ y = -σ x := by
    have hh := sum_erase_add (univ : Finset A) σ (mem_univ x)
    rw [hσ] at hh
    linarith only [hh]
  simp [distinctPairSum,he,hσ]

theorem balanced_distinctPairSum_product {A : Type} [Fintype A]
    (σ : A → ℝ) (hσ : ∑ x,σ x=0) (hSquare : ∀ x,(σ x)^2=1) :
    distinctPairSum (fun x y => σ x*σ y)=-(Fintype.card A : ℝ) := by
  have he (x : A) : ∑ y ∈ (univ : Finset A).erase x,σ y = -σ x := by
    have hh := sum_erase_add (univ : Finset A) σ (mem_univ x)
    rw [hσ] at hh
    linarith only [hh]
  have hp (x : A) : ∑ y ∈ (univ : Finset A).erase x,σ x*σ y = -1 := by
    rw [←mul_sum,he]
    nlinarith only [hSquare x]
  simp [distinctPairSum,hp]

theorem balanced_distinctPairSum_scaled_product {A : Type} [Fintype A]
    (σ : A → ℝ) (hσ : ∑ x,σ x=0) (hSquare : ∀ x,(σ x)^2=1) (a : ℝ) :
    distinctPairSum (fun x y => a*σ x*σ y)= -a*(Fintype.card A : ℝ) := by
  simp only [mul_assoc,distinctPairSum_mul_left,balanced_distinctPairSum_product σ hσ hSquare]
  ring

theorem balanced_distinctPairSum_product_scaled {A : Type} [Fintype A]
    (σ : A → ℝ) (hσ : ∑ x,σ x=0) (hSquare : ∀ x,(σ x)^2=1) (a : ℝ) :
    distinctPairSum (fun x y => σ x*σ y*a)= -(Fintype.card A : ℝ)*a := by
  rw [distinctPairSum_mul_right,balanced_distinctPairSum_product σ hσ hSquare]

/-- Exact expansion of the four parity corners of a signed box. -/
theorem signed_parity_box_product (θ a a' b b' c c' : ℝ)
    (ha : a^2=1) (ha' : a'^2=1) (hb : b^2=1) (hb' : b'^2=1)
    (hc : c^2=1) (hc' : c'^2=1) :
    (1+θ*a*b*c)*(1+θ*a*b'*c')*(1+θ*a'*b*c')*(1+θ*a'*b'*c) =
      (1+θ^4)+(θ+θ^3)*(a*b*c+a*b'*c'+a'*b*c'+a'*b'*c)+
        2*θ^2*((a*a')*(b*b')+(a*a')*(c*c')+(b*b')*(c*c')) := by
  ring_nf
  simp only [ha,ha',hb,hb',hc,hc',one_mul,mul_one]
  ring

def signedBoxSum {A : Type} [Fintype A] (θ : ℝ) (σ τ υ : A → ℝ) : ℝ :=
  distinctPairSum (fun r r' => distinctPairSum (fun c c' => distinctPairSum (fun s s' =>
    (1+θ*σ r*τ c*υ s)*(1+θ*σ r*τ c'*υ s')*
      (1+θ*σ r'*τ c*υ s')*(1+θ*σ r'*τ c'*υ s))))

/-- Balanced signs give a closed polynomial for the genuine ordered-box
sum. The Pasch classification supplies the separate multiplicity-four
conversion from this sum to the unordered Pasch target. -/
theorem balanced_signedBoxSum {A : Type} [Fintype A] [Nonempty A]
    (θ : ℝ) (σ τ υ : A → ℝ)
    (hσ : ∑ x,σ x=0) (hτ : ∑ x,τ x=0) (hυ : ∑ x,υ x=0)
    (hσ2 : ∀ x,(σ x)^2=1) (hτ2 : ∀ x,(τ x)^2=1) (hυ2 : ∀ x,(υ x)^2=1) :
    signedBoxSum θ σ τ υ =
      (1+θ^4)*(Fintype.card A : ℝ)^3*((Fintype.card A : ℝ)-1)^3+
        6*θ^2*(Fintype.card A : ℝ)^3*((Fintype.card A : ℝ)-1) := by
  have hExpand r r' c c' s s' := signed_parity_box_product θ (σ r) (σ r')
    (τ c) (τ c') (υ s) (υ s') (hσ2 r) (hσ2 r') (hτ2 c) (hτ2 c') (hυ2 s) (hυ2 s')
  dsimp only [signedBoxSum]
  simp_rw [hExpand]
  simp only [distinctPairSum_add,distinctPairSum_mul_left,distinctPairSum_mul_right,
    distinctPairSum_neg,mul_assoc,mul_neg,neg_mul,distinctPairSum_const,balanced_distinctPairSum_first σ hσ,
    balanced_distinctPairSum_second σ hσ,balanced_distinctPairSum_product σ hσ hσ2,
    balanced_distinctPairSum_first τ hτ,balanced_distinctPairSum_second τ hτ,
    balanced_distinctPairSum_product τ hτ hτ2,balanced_distinctPairSum_first υ hυ,
    balanced_distinctPairSum_second υ hυ,balanced_distinctPairSum_product υ hυ hυ2,
    mul_zero,zero_mul,add_zero,zero_add]
  ring_nf
  simp only [distinctPairSum_add,distinctPairSum_neg,
    balanced_distinctPairSum_scaled_product σ hσ hσ2,
    balanced_distinctPairSum_product_scaled σ hσ hσ2,
    balanced_distinctPairSum_scaled_product τ hτ hτ2,
    balanced_distinctPairSum_product_scaled τ hτ hτ2,
    balanced_distinctPairSum_scaled_product υ hυ hυ2,
    balanced_distinctPairSum_product_scaled υ hυ hυ2]
  ring

#print axioms balanced_distinctPairSum_product
#print axioms signed_parity_box_product
#print axioms balanced_signedBoxSum
end TypedTriangle.Applications.Latin
