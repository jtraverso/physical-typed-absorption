module
public import RequestProject.TypedTriangle.Defs
@[expose] public section
open Finset
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Completion.Hybrid

def mix {B R : Type} (θ : B → ℝ) (P Q : B → R → ℝ) (b : B) (r : R) : ℝ :=
  θ b*P b r+(1-θ b)*Q b r

theorem mix_nonneg {B R : Type} (θ : B → ℝ) (P Q : B → R → ℝ)
    (hθ : ∀ b,0 ≤ θ b ∧ θ b ≤ 1)
    (hP : ∀ b r,0 ≤ P b r) (hQ : ∀ b r,0 ≤ Q b r) :
    ∀ b r,0 ≤ mix θ P Q b r := by
  intro b r
  exact add_nonneg (mul_nonneg (hθ b).1 (hP b r))
    (mul_nonneg (sub_nonneg.mpr (hθ b).2) (hQ b r))

/-- Sender-dependent mixing preserves each positive edge's capacity.
No receiver guarantee is silently assumed here. -/
theorem sender_budget {B R : Type} (receivers : Finset R)
    (θ : B → ℝ) (P Q : B → R → ℝ) (capacity : B → ℝ)
    (hθ : ∀ b,0 ≤ θ b ∧ θ b ≤ 1)
    (hP : ∀ b,∑ r ∈ receivers,P b r ≤ capacity b)
    (hQ : ∀ b,∑ r ∈ receivers,Q b r ≤ capacity b) :
    ∀ b,∑ r ∈ receivers,mix θ P Q b r ≤ capacity b := by
  intro b
  simp only [mix,sum_add_distrib,←mul_sum]
  have hp := mul_le_mul_of_nonneg_left (hP b) (hθ b).1
  have hq := mul_le_mul_of_nonneg_left (hQ b) (sub_nonneg.mpr (hθ b).2)
  nlinarith only [hp,hq]

theorem received_constant {B R : Type} (senders : Finset B)
    (P Q : B → R → ℝ) (ell : ℝ) (r : R) :
    (∑ b ∈ senders,mix (fun _ => ell) P Q b r)=
      ell*(∑ b ∈ senders,P b r)+(1-ell)*(∑ b ∈ senders,Q b r) := by
  simp only [mix,sum_add_distrib,←mul_sum]

theorem total_charge_conservation {B R : Type} (senders : Finset B) (receivers : Finset R)
    (θ : B → ℝ) (P Q : B → R → ℝ) (positive : B → ℝ) (negative : R → ℝ) :
    (∑ b ∈ senders,(positive b-(∑ r ∈ receivers,mix θ P Q b r)))+
      (∑ r ∈ receivers,(negative r+(∑ b ∈ senders,mix θ P Q b r)))=
      (∑ b ∈ senders,positive b)+(∑ r ∈ receivers,negative r) := by
  have hs : (∑ b ∈ senders,∑ r ∈ receivers,mix θ P Q b r)=
      ∑ r ∈ receivers,∑ b ∈ senders,mix θ P Q b r := sum_comm
  rw [sum_sub_distrib,sum_add_distrib,←hs]
  ring

/-- A two-receiver dual certificate bounds EVERY constant mixture.
The finite rational witness uses this identity to separate adaptive mixing. -/
theorem two_receiver_upper (p₁ p₂ q₁ q₂ θ ell t : ℝ)
    (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (hBalance : θ*(p₁-q₁)+(1-θ)*(p₂-q₂)=0)
    (h₁ : t ≤ ell*p₁+(1-ell)*q₁) (h₂ : t ≤ ell*p₂+(1-ell)*q₂) :
    t ≤ θ*q₁+(1-θ)*q₂ := by
  have hh₁ := mul_le_mul_of_nonneg_left h₁ hθ.1
  have hh₂ := mul_le_mul_of_nonneg_left h₂ (sub_nonneg.mpr hθ.2)
  have hb := congrArg (fun z : ℝ => ell*z) hBalance
  nlinarith only [hh₁,hh₂,hb]

#print axioms sender_budget
#print axioms total_charge_conservation
#print axioms two_receiver_upper
end TypedTriangle.Completion.Hybrid
