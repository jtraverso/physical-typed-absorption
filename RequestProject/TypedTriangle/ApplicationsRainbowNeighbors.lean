module
public import RequestProject.TypedTriangle.ApplicationsRainbowDefs
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Rainbow

variable {k : ℕ} {A : Type} [Fintype A]

theorem allowed_triangle (u v w : Fin k × A)
    (huv : u.1 ≠ v.1) (huw : u.1 ≠ w.1) (hvw : v.1 ≠ w.1) :
    IsAllowed (host k A) (types k) {u,v,w} := by
  have huv' : u ≠ v := fun h => huv (congrArg Prod.fst h)
  have huw' : u ≠ w := fun h => huw (congrArg Prod.fst h)
  have hvw' : v ≠ w := fun h => hvw (congrArg Prod.fst h)
  refine ⟨by simp [huv',huw',hvw'],?_,?_⟩
  · intro x hx y hy hxy
    simp only [mem_insert,mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl <;> simp_all [host,ne_comm]
  · change (({u,v,w} : Finset (Fin k × A)).val.map Prod.fst).Nodup
    simp [Finset.insert_val_of_notMem,huv',huw',hvw',huv,huw,hvw]

theorem commonNbrs_card (u v : Fin k × A) (i : Fin k)
    (hui : u.1 ≠ i) (hvi : v.1 ≠ i) :
    (commonNbrs (host k A) i u v).card = Fintype.card A := by
  let e : A ↪ Fin k × A := ⟨fun a => (i,a), fun _ _ h => congrArg Prod.snd h⟩
  have he : commonNbrs (host k A) i u v = univ.map e := by
    ext x
    simp only [commonNbrs,mem_filter,mem_univ,true_and,host_adj,host_lab,mem_map]
    constructor
    · rintro ⟨_,_,hxi⟩
      exact ⟨x.2,Prod.ext hxi.symm rfl⟩
    · rintro ⟨a,rfl⟩
      exact ⟨hui,hvi,rfl⟩
  rw [he,card_map,card_univ]

theorem commonNbrCond (k : ℕ) (A : Type) [Fintype A] (α : ℝ)
    (hαk : α*(k:ℝ) ≤ 1) : CommonNbrCond (host k A) (types k) α := by
  intro u v _ i hi
  have hi' : (u.1 ≠ v.1 ∧ u.1 ≠ i) ∧ v.1 ≠ i := by
    simpa [types,not_or] using hi
  have hui : u.1 ≠ i := hi'.1.2
  have hvi : v.1 ≠ i := hi'.2
  rw [commonNbrs_card u v i hui hvi]
  have hc := mul_le_mul_of_nonneg_right hαk (Nat.cast_nonneg (Fintype.card A))
  simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,one_mul,mul_assoc] using hc

end TypedTriangle.Applications.Rainbow
