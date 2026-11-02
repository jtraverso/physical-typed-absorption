module
public import RequestProject.TypedTriangle.ApplicationsLatinMain
public import RequestProject.TypedTriangle.ApplicationsLatinSignedProfile
public import RequestProject.TypedTriangle.ApplicationsLatinPaschIntercalates
public import RequestProject.TypedTriangle.ApplicationsLatinPaschTarget
public import RequestProject.TypedTriangle.ApplicationsBalancedSigns
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin

/-- One Latin square has the prescribed signed statistics and the exact
uniform finite-order intercalate target. -/
theorem uniform_with_intercalates (η : ℝ) (q : ℕ) (hη : 0<η) :
    ∃ N : ℕ, 2≤N ∧ ∀ (A : Type) [Fintype A],
      N≤Fintype.card A → ∀ (ν : Type) [Fintype ν] (w : ν → A → A → A → ℝ),
      (Fintype.card ν : ℝ)≤(Fintype.card A : ℝ)^q →
      (∀ k x y z,|w k x y z|≤1) →
      ∃ L : LatinSquare A,
        (∀ k,|(∑ x,∑ y,w k x y (L x y))-
          (∑ x,∑ y,∑ z,(1/(Fintype.card A : ℝ))*w k x y z)|≤η*(Fintype.card A : ℝ)^2) ∧
        |((intercalates L).card : ℝ)-
          ((Fintype.card A : ℝ)-1)^3/(4*(Fintype.card A : ℝ))|≤η*(Fintype.card A : ℝ)^2 := by
  obtain ⟨N,hN,hMain⟩ := latin_square_with_uniform_statistics η q hη
  refine ⟨N,hN,?_⟩
  intro A _ hn ν _ w hν hw
  letI : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨L,hStats,hCount⟩ := hMain A hn ν w hν hw
  rw [count_decomposition_eq_intercalates,uniform_weight_target] at hCount
  exact ⟨L,hStats,hCount⟩

/-- The same Latin square realizes a balanced positive rank-one profile
and the explicitly computed intercalate target of that original profile. -/
theorem signed_profile_with_intercalates (θ η : ℝ) (q : ℕ)
    (hθ : 0≤θ) (hθOne : θ<1) (hη : 0<η) :
    ∃ N : ℕ, 2≤N ∧ ∀ (A : Type) [Fintype A],
      N≤Fintype.card A → ∀ (σ τ υ : A → ℝ),
      (∀ x,σ x=1 ∨ σ x= -1) → (∀ x,τ x=1 ∨ τ x= -1) →
      (∀ x,υ x=1 ∨ υ x= -1) →
      (∑ x,σ x)=0 → (∑ x,τ x)=0 → (∑ x,υ x)=0 →
      ∀ (ν : Type) [Fintype ν] (w : ν → A → A → A → ℝ),
      (Fintype.card ν : ℝ)≤(Fintype.card A : ℝ)^q →
      (∀ k x y z,|w k x y z|≤1) →
      ∃ L : LatinSquare A,
        (∀ k,|(∑ x,∑ y,w k x y (L x y))-
          (∑ x,∑ y,∑ z,signedProfile θ σ τ υ x y z*w k x y z)|≤η*(Fintype.card A : ℝ)^2) ∧
        |((intercalates L).card : ℝ)-
          ((1+θ^4)*((Fintype.card A : ℝ)-1)^3/(4*(Fintype.card A : ℝ))+
            3*θ^2*((Fintype.card A : ℝ)-1)/(2*(Fintype.card A : ℝ)))|≤η*(Fintype.card A : ℝ)^2 := by
  obtain ⟨N,hN,hMain⟩ := latin_square_with_profile_statistics (1-θ) (1+θ) η q
    (by linarith only [hθOne]) hη
  refine ⟨N,hN,?_⟩
  intro A _ hn σ τ υ hσ hτ hυ hσSum hτSum hυSum ν _ w hν hw
  letI : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨h01,h02,h12⟩ := signedProfile_marginals θ σ τ υ hσSum hτSum hυSum
  obtain ⟨L,hStats,hCount⟩ := hMain A hn (signedProfile θ σ τ υ)
    (signedProfile_bounds θ hθ σ τ υ hσ hτ hυ) h01 h02 h12 ν w hν hw
  have hσ2 : ∀ x,(σ x)^2=1 := by intro x; rcases hσ x with h|h <;> rw [h] <;> norm_num
  have hτ2 : ∀ x,(τ x)^2=1 := by intro x; rcases hτ x with h|h <;> rw [h] <;> norm_num
  have hυ2 : ∀ x,(υ x)^2=1 := by intro x; rcases hυ x with h|h <;> rw [h] <;> norm_num
  have ht : Pasch.target (weight (signedProfile θ σ τ υ)) (allowed (host A) types)=
      (1+θ^4)*((Fintype.card A : ℝ)-1)^3/(4*(Fintype.card A : ℝ))+
        3*θ^2*((Fintype.card A : ℝ)-1)/(2*(Fintype.card A : ℝ)) := by
    have hp : signedProfile θ σ τ υ =
        (fun x y z => (1+θ*σ x*τ y*υ z)/(Fintype.card A : ℝ)) := by
      funext x y z
      rfl
    rw [hp]
    exact balanced_signed_target θ σ τ υ hσSum hτSum hυSum hσ2 hτ2 hυ2
  rw [count_decomposition_eq_intercalates,ht] at hCount
  exact ⟨L,hStats,hCount⟩

/-- Every sufficiently large even order admits the concrete half-biased
profile; balanced signs are constructed internally before the tests. -/
theorem half_profile_with_intercalates (η : ℝ) (q : ℕ) (hη : 0<η) :
    ∃ N : ℕ, 2≤N ∧ ∀ (A : Type) [Fintype A],
      N≤Fintype.card A → Even (Fintype.card A) →
      ∃ σ : A → ℝ, (∀ x,σ x=1 ∨ σ x= -1) ∧ (∑ x,σ x)=0 ∧
      ∀ (ν : Type) [Fintype ν] (w : ν → A → A → A → ℝ),
      (Fintype.card ν : ℝ)≤(Fintype.card A : ℝ)^q →
      (∀ k x y z,|w k x y z|≤1) →
      ∃ L : LatinSquare A,
        (∀ k,|(∑ x,∑ y,w k x y (L x y))-
          (∑ x,∑ y,∑ z,signedProfile (1/2) σ σ σ x y z*w k x y z)|≤η*(Fintype.card A : ℝ)^2) ∧
        |((intercalates L).card : ℝ)-
          (17*((Fintype.card A : ℝ)-1)^3/(64*(Fintype.card A : ℝ))+
            3*((Fintype.card A : ℝ)-1)/(8*(Fintype.card A : ℝ)))|≤η*(Fintype.card A : ℝ)^2 := by
  obtain ⟨N,hN,hMain⟩ := signed_profile_with_intercalates (1/2) η q (by norm_num) (by norm_num) hη
  refine ⟨N,hN,?_⟩
  intro A _ hn hEven
  obtain ⟨σ,hσ,hSum⟩ := Applications.exists_balanced_signs A hEven
  refine ⟨σ,hσ,hSum,?_⟩
  intro ν _ w hν hw
  obtain ⟨L,hStats,hCount⟩ := hMain A hn σ σ σ hσ hσ hσ hSum hSum hSum ν w hν hw
  refine ⟨L,hStats,?_⟩
  have hTarget : (1+(1/2 : ℝ)^4)*((Fintype.card A : ℝ)-1)^3/(4*(Fintype.card A : ℝ))+
      3*(1/2 : ℝ)^2*((Fintype.card A : ℝ)-1)/(2*(Fintype.card A : ℝ)) =
      17*((Fintype.card A : ℝ)-1)^3/(64*(Fintype.card A : ℝ))+
        3*((Fintype.card A : ℝ)-1)/(8*(Fintype.card A : ℝ)) := by
    have hn0 : (Fintype.card A : ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hn0]
    <;> ring
  simpa only [hTarget] using hCount

#print axioms uniform_with_intercalates
#print axioms signed_profile_with_intercalates
#print axioms half_profile_with_intercalates
end TypedTriangle.Applications.Latin
