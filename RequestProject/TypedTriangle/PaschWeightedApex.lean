module
public import RequestProject.TypedTriangle.PaschEdgeSelection
public import RequestProject.TypedTriangle.PaschHostDensity
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

/-- H3 supplies the actual allowed, fresh, edge-avoiding candidate pool.
The chosen apex has bounded Pasch cost relative to the fixed previous family. -/
theorem exists_low_cost_fresh_apex {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) {a b c : V}
    (hT : IsAllowed H F {a,b,c}) (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) (B : Finset (Sym2 V)) (d : ℕ)
    (hdeg : ∀ v, degIn B v ≤ d) (Z : Finset V)
    (hwin : (Z.card : ℝ) + 2*d ≤ α/2 * Fintype.card V) :
    ∃ x : V, x ∉ Z ∧ IsAllowed H F {a,b,x} ∧
      s(a,x) ∉ B ∧ s(b,x) ∉ B ∧
      (rootedCount (insert {a,b,x} R) {a,b,x} : ℝ) ≤ (L : ℝ)^3/(α/2) := by
  let bad := (Z ∪ nbrIn B a) ∪ nbrIn B b
  let W := commonNbrs H (H.lab c) a b \ bad
  have hbadNat : bad.card ≤ Z.card + 2*d := by
    have ha := (card_nbrIn_le B a).trans (hdeg a)
    have hb := (card_nbrIn_le B b).trans (hdeg b)
    exact ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)).trans (by omega)
  have hbad : (bad.card : ℝ) ≤ (Z.card : ℝ) + 2*d := by exact_mod_cast hbadNat
  have hcover : commonNbrs H (H.lab c) a b ⊆ W ∪ bad := by
    intro x hx
    by_cases hxb : x ∈ bad
    · exact mem_union_right _ hxb
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hx, hxb⟩)
  have hcountNat : (commonNbrs H (H.lab c) a b).card ≤ W.card + bad.card :=
    (card_le_card hcover).trans (card_union_le _ _)
  have hcount : ((commonNbrs H (H.lab c) a b).card : ℝ) ≤ W.card + bad.card := by
    exact_mod_cast hcountNat
  have hH3count := commonNbr_card_lower hH3 hT
  have hW : α/2 * (Fintype.card V : ℝ) ≤ W.card := by
    linarith only [hcount, hH3count, hbad, hwin]
  have hnNat : 0 < Fintype.card V := by
    have hCard : 3 ≤ Fintype.card V := hT.1 ▸ card_le_univ ({a,b,c} : Finset V)
    omega
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnNat
  have hab : a ≠ b := (distinct_of_card_three hT.1).1
  obtain ⟨x, hx, hCost⟩ := exists_rooted_completion_bounded R L hL a b hab W (α/2)
    (by positivity) hn hW
  obtain ⟨hxCommon, hxBad⟩ := mem_sdiff.mp hx
  have hxZ : x ∉ Z := fun h => hxBad (mem_union_left _ (mem_union_left _ h))
  have hxA : s(a,x) ∉ B := by
    intro h
    exact hxBad (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h⟩)))
  have hxB : s(b,x) ∉ B := by
    intro h
    exact hxBad (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h⟩))
  exact ⟨x, hxZ, allowed_of_commonNbr hT hxCommon, hxA, hxB, hCost⟩

#print axioms exists_low_cost_fresh_apex
end TypedTriangle.Pasch
