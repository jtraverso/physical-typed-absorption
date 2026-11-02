module
public import RequestProject.TypedTriangle.ApplicationsTwoScaleQuadrature
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TypedTriangle.Applications.Latin.TwoScale

/-- A pairing within each coarse half, constructed from divisibility by four. -/
structure CoarsePairing {A : Type} (σ : A → ℝ) where
  k : ℕ
  equiv : ((Bool × Fin k) × Bool) ≃ A
  same : ∀ p, σ (equiv (p,false))=σ (equiv (p,true))

theorem exists_coarse_pairing {A : Type} [Fintype A] (σ : A → ℝ)
    (hsign : ∀ a, σ a=1 ∨ σ a= -1) (hsum : ∑ a, σ a=0)
    (hfour : 4 ∣ Fintype.card A) : Nonempty (CoarsePairing σ) := by
  obtain ⟨k,hk⟩ := hfour
  let P := {a : A // σ a=1}
  let N := {a : A // σ a≠1}
  have hpoint (a : A) : σ a=2*(if σ a=1 then (1:ℝ) else 0)-1 := by
    rcases hsign a with h | h <;> norm_num [h]
  have hcount : (∑ a : A, if σ a=1 then (1:ℝ) else 0)=(Fintype.card P : ℝ) := by
    simp [P, Fintype.card_subtype, Finset.sum_boole]
  have hpcard : Fintype.card P=2*k := by
    have hexp := sum_congr (s₁ := (univ : Finset A)) rfl (fun a _ => hpoint a)
    rw [hsum, sum_sub_distrib, ← mul_sum, hcount] at hexp
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at hexp
    have hkR : (Fintype.card A : ℝ)=4*(k:ℝ) := by exact_mod_cast hk
    have hpR : (Fintype.card P : ℝ)=2*(k:ℝ) := by linarith
    exact_mod_cast hpR
  have htotal : Fintype.card P+Fintype.card N=Fintype.card A := by
    simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.sumCompl (fun a : A => σ a=1))
  have hncard : Fintype.card N=2*k := by omega
  let ep : (Fin k × Bool) ≃ P := Fintype.equivOfCardEq (by simp [hpcard, Nat.mul_comm])
  let en : (Fin k × Bool) ≃ N := Fintype.equivOfCardEq (by simp [hncard, Nat.mul_comm])
  let e : ((Bool × Fin k) × Bool) ≃ A :=
    (Equiv.prodAssoc Bool (Fin k) Bool).trans
      ((Equiv.boolProdEquivSum (Fin k × Bool)).trans
        ((Equiv.sumCongr ep en).trans (Equiv.sumCompl (fun a : A => σ a=1))))
  have value (p : Bool × Fin k) (b : Bool) : σ (e (p,b))=(if p.1 then -1 else 1) := by
    rcases p with ⟨p,i⟩
    cases p
    · change σ (ep (i,b)).val=1
      exact (ep (i,b)).property
    · change σ (en (i,b)).val= -1
      exact (hsign _).resolve_left (en (i,b)).property
  exact ⟨⟨k,e,fun p => (value p false).trans (value p true).symm⟩⟩

def CoarsePairing.fine {A : Type} {σ : A → ℝ} (P : CoarsePairing σ)
    (e : Bool × Fin P.k → ℝ) (a : A) : ℝ :=
  if (P.equiv.symm a).2 then e (P.equiv.symm a).1 else -e (P.equiv.symm a).1

theorem CoarsePairing.fine_orthogonal {A : Type} [Fintype A] {σ : A → ℝ}
    (P : CoarsePairing σ) (hsign : ∀ a, σ a=1 ∨ σ a= -1)
    (hsum : ∑ a, σ a=0) (e : Bool × Fin P.k → ℝ)
    (he : ∀ i, e i=1 ∨ e i= -1) : OrthogonalSigns σ (P.fine e) := by
  refine ⟨hsign, ?_, hsum, ?_, ?_⟩
  · intro a
    dsimp [CoarsePairing.fine]
    split_ifs <;> rcases he (P.equiv.symm a).1 with h | h <;> simp [h]
  · rw [← P.equiv.sum_comp (P.fine e), Fintype.sum_prod_type]
    simp [CoarsePairing.fine, Fintype.sum_bool]
  · rw [← P.equiv.sum_comp (fun a => σ a * P.fine e a), Fintype.sum_prod_type]
    apply sum_eq_zero
    intro p _
    norm_num [CoarsePairing.fine, Fintype.sum_bool]
    rw [P.same p]
    ring

theorem CoarsePairing.linear_form {A : Type} [Fintype A] {σ : A → ℝ}
    (P : CoarsePairing σ) (e : Bool × Fin P.k → ℝ) (a : A → ℝ) :
    (∑ r, P.fine e r*a r) =
      ∑ i, e i*(a (P.equiv (i,true))-a (P.equiv (i,false))) := by
  rw [← P.equiv.sum_comp (fun r => P.fine e r*a r), Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  norm_num [CoarsePairing.fine, Fintype.sum_bool]
  ring

theorem CoarsePairing.card {A : Type} [Fintype A] {σ : A → ℝ} (P : CoarsePairing σ) :
    Fintype.card A=2*Fintype.card (Bool × Fin P.k) := by
  have hc := Fintype.card_congr P.equiv
  simpa [Fintype.card_prod, Nat.mul_comm] using hc.symm

set_option pp.fullNames true
#print axioms exists_coarse_pairing
#print axioms CoarsePairing.fine_orthogonal
#print axioms CoarsePairing.linear_form
end TypedTriangle.Applications.Latin.TwoScale
