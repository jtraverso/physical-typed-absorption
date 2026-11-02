module
public import RequestProject.TypedTriangle.ApplicationsTwoScaleMain
public import RequestProject.TypedTriangle.ApplicationsTwoScaleBlocks
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin.TwoScale

def bitSign (a : Bool) : ℝ := if a then 1 else -1
theorem bitSign_sign (a : Bool) : bitSign a=1 ∨ bitSign a= -1 := by
  cases a <;> simp [bitSign]

def blockCount {A : Type} [Fintype A] (L : LatinSquare A)
    (σ τ υ : A → ℝ) (a b d : ℝ) : ℕ :=
  ((univ : Finset (A × A)).filter (fun rc =>
    σ rc.1=a ∧ τ rc.2=b ∧ υ (L rc.1 rc.2)=d)).card

theorem block_statistic {A : Type} [Fintype A] (L : LatinSquare A)
    (σ τ υ : A → ℝ) (a b d : ℝ) :
    linearStatistic L (blockWeight σ τ υ a b d) = (blockCount L σ τ υ a b d : ℝ) := by
  simp only [linearStatistic,blockWeight,blockCount,Finset.card_filter,
    Nat.cast_sum,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro c _
  split_ifs <;> norm_num

/-- Full two-scale application: all prescribed tests and all eight coarse
blocks are retained, while the two intercalate targets are controlled.
No fine signs or concentration statement are assumed. -/
theorem latin_two_scale_with_blocks (θ t ε : ℝ) (q : ℕ)
    (hθ : 0≤θ) (hθ1 : θ<1) (ht : 0≤t) (ht1 : t<1) (hε : 0<ε) :
    ∃ N : ℕ, 12≤N ∧ ∀ (A : Type) [Fintype A], N≤Fintype.card A →
      4 ∣ Fintype.card A → ∀ (σ τ υ : A → ℝ),
      (∀ a, σ a=1 ∨ σ a= -1) → (∀ a, τ a=1 ∨ τ a= -1) → (∀ a, υ a=1 ∨ υ a= -1) →
      (∑ a,σ a)=0 → (∑ a,τ a)=0 → (∑ a,υ a)=0 →
      ∀ (J : Type) [Fintype J] (w : J → A → A → A → ℝ),
      (Fintype.card J : ℝ)≤(Fintype.card A : ℝ)^q →
      (∀ j r c s, |w j r c s|≤1) →
      ∃ L₀ Lₜ : LatinSquare A,
        (∀ j, |linearStatistic L₀ (w j)-linearTarget (signedProfile θ σ τ υ) (w j)|≤
          ε*(Fintype.card A : ℝ)^2) ∧
        (∀ j, |linearStatistic Lₜ (w j)-linearTarget (signedProfile θ σ τ υ) (w j)|≤
          ε*(Fintype.card A : ℝ)^2) ∧
        (∀ a b d : Bool,
          |(blockCount L₀ σ τ υ (bitSign a) (bitSign b) (bitSign d) : ℝ)-
            (1+θ*bitSign a*bitSign b*bitSign d)*(Fintype.card A : ℝ)^2/8|≤ε*(Fintype.card A : ℝ)^2) ∧
        (∀ a b d : Bool,
          |(blockCount Lₜ σ τ υ (bitSign a) (bitSign b) (bitSign d) : ℝ)-
            (1+θ*bitSign a*bitSign b*bitSign d)*(Fintype.card A : ℝ)^2/8|≤ε*(Fintype.card A : ℝ)^2) ∧
        |((intercalates L₀).card : ℝ)-kappa θ 0*(Fintype.card A : ℝ)^2|≤ε*(Fintype.card A : ℝ)^2 ∧
        |((intercalates Lₜ).card : ℝ)-kappa θ t*(Fintype.card A : ℝ)^2|≤ε*(Fintype.card A : ℝ)^2 := by
  obtain ⟨N,hN,hMain⟩ := two_scale_latin_separation θ t ε (q+1) hθ hθ1 ht ht1 hε
  refine ⟨N,hN,?_⟩
  intro A _ hn hfour σ τ υ hσ hτ hυ hσsum hτsum hυsum J _ w hJ hw
  have hn12 : (12:ℝ)≤Fintype.card A := by exact_mod_cast hN.trans hn
  letI : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  let tests : (J ⊕ (Bool × Bool × Bool)) → A → A → A → ℝ :=
    Sum.elim w (fun i => blockWeight σ τ υ (bitSign i.1) (bitSign i.2.1) (bitSign i.2.2))
  have htests : (Fintype.card (J ⊕ (Bool × Bool × Bool)) : ℝ)≤(Fintype.card A : ℝ)^(q+1) := by
    have hp : 1≤(Fintype.card A : ℝ)^q := one_le_pow₀ (by linarith)
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    rw [pow_succ]
    nlinarith
  obtain ⟨L₀,Lₜ,hs₀,hsₜ,hc₀,hcₜ⟩ := hMain A hn hfour σ τ υ hσ hτ hυ hσsum hτsum hυsum
    (J ⊕ (Bool × Bool × Bool)) tests htests (by
      intro j r c s
      cases j with
      | inl j => exact hw j r c s
      | inr i => exact blockWeight_bound σ τ υ _ _ _ r c s)
  obtain ⟨Pr⟩ := exists_coarse_pairing σ hσ hσsum hfour
  obtain ⟨Pc⟩ := exists_coarse_pairing τ hτ hτsum hfour
  obtain ⟨Ps⟩ := exists_coarse_pairing υ hυ hυsum hfour
  have hr := Pr.fine_orthogonal hσ hσsum (fun _ => 1) (fun _ => Or.inl rfl)
  have hc := Pc.fine_orthogonal hτ hτsum (fun _ => 1) (fun _ => Or.inl rfl)
  have hs := Ps.fine_orthogonal hυ hυsum (fun _ => 1) (fun _ => Or.inl rfl)
  have hblock (a b d : Bool) : linearTarget (signedProfile θ σ τ υ)
      (blockWeight σ τ υ (bitSign a) (bitSign b) (bitSign d)) =
      (1+θ*bitSign a*bitSign b*bitSign d)*(Fintype.card A : ℝ)^2/8 :=
    block_target hr hc hs θ _ _ _ (bitSign_sign a) (bitSign_sign b) (bitSign_sign d)
  refine ⟨L₀,Lₜ,(fun j => hs₀ (.inl j)),(fun j => hsₜ (.inl j)),?_,?_,hc₀,hcₜ⟩
  · intro a b d
    have hx := hs₀ (.inr (a,b,d))
    change |linearStatistic L₀ (blockWeight σ τ υ (bitSign a) (bitSign b) (bitSign d)) -
      linearTarget (signedProfile θ σ τ υ) (blockWeight σ τ υ (bitSign a) (bitSign b) (bitSign d))|≤_ at hx
    rwa [block_statistic,hblock] at hx
  · intro a b d
    have hx := hsₜ (.inr (a,b,d))
    change |linearStatistic Lₜ (blockWeight σ τ υ (bitSign a) (bitSign b) (bitSign d)) -
      linearTarget (signedProfile θ σ τ υ) (blockWeight σ τ υ (bitSign a) (bitSign b) (bitSign d))|≤_ at hx
    rwa [block_statistic,hblock] at hx

theorem kappa_gap (θ t : ℝ) : kappa θ t-kappa θ 0=(1+θ^4)*t^4/4 := by
  simp [kappa]
  ring

theorem intercalate_gap_of_targets {A : Type} [Fintype A]
    (L₀ Lₜ : LatinSquare A) (θ t ε : ℝ)
    (h₀ : |((intercalates L₀).card : ℝ)-kappa θ 0*(Fintype.card A : ℝ)^2|≤ε*(Fintype.card A : ℝ)^2)
    (hₜ : |((intercalates Lₜ).card : ℝ)-kappa θ t*(Fintype.card A : ℝ)^2|≤ε*(Fintype.card A : ℝ)^2) :
    ((1+θ^4)*t^4/4-2*ε)*(Fintype.card A : ℝ)^2 ≤
      ((intercalates Lₜ).card : ℝ)-(intercalates L₀).card := by
  obtain ⟨_,hupper⟩ := abs_le.mp h₀
  obtain ⟨hlower,_⟩ := abs_le.mp hₜ
  have heq := kappa_gap θ t
  have heqmul := congrArg (fun x : ℝ => x*(Fintype.card A : ℝ)^2) heq
  nlinarith only [hupper,hlower,heqmul]

set_option pp.fullNames true
#print axioms latin_two_scale_with_blocks
#print axioms kappa_gap
#print axioms intercalate_gap_of_targets
end TypedTriangle.Applications.Latin.TwoScale
