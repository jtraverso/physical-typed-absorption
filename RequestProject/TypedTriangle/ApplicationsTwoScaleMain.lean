module
public import RequestProject.TypedTriangle.ApplicationsTwoScaleRounding
public import RequestProject.TypedTriangle.ApplicationsTwoScaleRetention
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin.TwoScale

/-- Prescribed linear tests coexist with two intercalate targets. The threshold
precedes the finite host, the balanced coarse signs, and the test family.
Fine signs, their balance, their concentration and their Pasch estimate are
constructed in the proof; none is a hypothesis of this theorem. -/
theorem two_scale_latin_separation (θ t ε : ℝ) (q : ℕ)
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
        |((intercalates L₀).card : ℝ)-kappa θ 0*(Fintype.card A : ℝ)^2|≤ε*(Fintype.card A : ℝ)^2 ∧
        |((intercalates Lₜ).card : ℝ)-kappa θ t*(Fintype.card A : ℝ)^2|≤ε*(Fintype.card A : ℝ)^2 := by
  have hη : 0<ε/4 := by positivity
  obtain ⟨N₀,hN₀,round₀⟩ := round_two_scale_profile θ 0 (ε/4) q hθ hθ1 (by norm_num) (by norm_num) hη
  obtain ⟨Nₜ,hNₜ,roundₜ⟩ := round_two_scale_profile θ t (ε/4) q hθ hθ1 ht ht1 hη
  obtain ⟨Nsign,hSign⟩ := polynomial_sign_budget (ε/4) q hη
  let b := (1+θ)*(1+t)
  let N := max 12 (max N₀ (max Nₜ (max Nsign ⌈3*b^4/ε⌉₊)))
  refine ⟨N,le_max_left _ _,?_⟩
  intro A _ hn hfour σ τ υ hσ hτ hυ hσsum hτsum hυsum J _ w hJ hw
  have hn12 : 12≤Fintype.card A := (le_max_left _ _).trans hn
  have hn0 : N₀≤Fintype.card A := by dsimp [N] at hn; omega
  have hnt : Nₜ≤Fintype.card A := by dsimp [N] at hn; omega
  have hnsign : Nsign≤Fintype.card A := by dsimp [N] at hn; omega
  have hnceil : ⌈3*b^4/ε⌉₊≤Fintype.card A := by dsimp [N] at hn; omega
  letI : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  let n : ℝ := Fintype.card A
  have hnpos : 0<n := Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨Pτ⟩ := exists_coarse_pairing τ hτ hτsum hfour
  obtain ⟨Pυ⟩ := exists_coarse_pairing υ hυ hυsum hfour
  let ζ := Pτ.fine (fun _ => 1)
  let χ := Pυ.fine (fun _ => 1)
  have hc : OrthogonalSigns τ ζ := Pτ.fine_orthogonal hτ hτsum _ (fun _ => Or.inl rfl)
  have hs : OrthogonalSigns υ χ := Pυ.fine_orthogonal hυ hυsum _ (fun _ => Or.inl rfl)
  have hsmall : (Fintype.card J : ℝ)*(2*Real.exp (-(ε/4)^2*n/4))<1 := by
    calc
      _ ≤ n^q*(2*Real.exp (-(ε/4)^2*n/4)) := mul_le_mul_of_nonneg_right hJ (by positivity)
      _ = 2*n^q*Real.exp (-(ε/4)^2*n/4) := by ring
      _ < 1 := hSign _ hnsign
  obtain ⟨ξ,hr,hretain⟩ := exists_fine_sign_retaining_forms σ hσ hσsum hfour
    (fun j => rowCoefficient θ σ τ υ ζ χ (w j))
    (fun j => rowCoefficient_bound θ hθ hθ1.le σ τ υ ζ χ hσ hτ hυ
      hc.sign_v hs.sign_v hυsum (w j) (hw j)) t (ε/4) ht ht1.le hη.le hsmall
  obtain ⟨L₀,hs₀,hc₀⟩ := round₀ A hn0 σ τ υ ξ ζ χ hr hc hs J w hJ hw
  obtain ⟨Lₜ,hsₜ,hcₜ⟩ := roundₜ A hnt σ τ υ ξ ζ χ hr hc hs J w hJ hw
  have hp0 : profile θ 0 σ τ υ ξ ζ χ=signedProfile θ σ τ υ := by
    funext r c s
    simp [profile,signedProfile]
  rw [hp0] at hs₀
  have hbudget : 3*b^4≤ε*n := by
    have hbN : 3*b^4/ε≤n := (Nat.le_ceil _).trans (by dsimp [n]; exact_mod_cast hnceil)
    exact (div_le_iff₀ hε).mp hbN |>.trans_eq (mul_comm n ε)
  have hcorr : ε/4*n^2+3*b^4*n/4≤ε*n^2 := by
    have hmul := mul_le_mul_of_nonneg_right hbudget hnpos.le
    nlinarith [sq_nonneg n]
  have hb0 : ((1+θ)*(1+(0:ℝ)))^4≤b^4 := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [b]
    nlinarith
  refine ⟨L₀,Lₜ,?_,?_,?_,hcₜ.trans hcorr⟩
  · intro j
    exact (hs₀ j).trans (by nlinarith [sq_nonneg (Fintype.card A : ℝ)])
  · intro j
    have hd : |linearTarget (profile θ t σ τ υ ξ ζ χ) (w j)-
        linearTarget (signedProfile θ σ τ υ) (w j)|≤ε/4*n^2 := by
      dsimp [linearTarget]
      rw [profile_target_difference]
      exact (hretain j).le
    exact (abs_sub_le _ _ _).trans ((add_le_add (hsₜ j) hd).trans (by nlinarith [sq_nonneg n]))
  · apply hc₀.trans
    apply le_trans _ hcorr
    gcongr

set_option pp.fullNames true
#print axioms two_scale_latin_separation
end TypedTriangle.Applications.Latin.TwoScale
