module
public import RequestProject.S07V43.Activation
public import RequestProject.TypedTriangle.BasalPackingIncidence
public import RequestProject.TypedTriangle.SlotPairing
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

private theorem decomposition_biUnion {J : Type*} (s : Finset J)
    {H : Host V I} {F : Set (Multiset I)}
    (E : J → Finset (Sym2 V)) (D : J → Finset (Finset V))
    (hE : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (E i) (E j))
    (hD : ∀ i ∈ s, IsDecomposition H F (E i) (D i)) :
    IsDecomposition H F (s.biUnion E) (s.biUnion D) := by
  have hSub : ∀ i ∈ s, ∀ T ∈ D i, triEdges T ⊆ E i := by
    intro i hi T hT
    rw [← (hD i hi).2.2]
    exact subset_biUnion_of_mem triEdges hT
  refine ⟨?_,?_,?_⟩
  · intro T hT
    obtain ⟨i,hi,hT⟩ := mem_biUnion.mp hT
    exact (hD i hi).1 T hT
  · intro T hT U hU hne
    obtain ⟨i,hi,hT⟩ := mem_biUnion.mp hT
    obtain ⟨j,hj,hU⟩ := mem_biUnion.mp hU
    by_cases hij : i = j
    · subst j
      exact (hD i hi).2.1 hT hU hne
    · exact (hE i hi j hj hij).mono (hSub i hi T hT) (hSub j hj U hU)
  · rw [biUnion_biUnion]
    exact biUnion_congr rfl (fun i hi => (hD i hi).2.2)

/-- Choose both decompositions of every physical cell once, before the word to
activate. Every later bank cover can then be decomposed using only their fixed
union. The union comprises two packings, irrespective of the number of modes. -/
theorem bank_cover_decompositions_in_fixed_union
    {J C Q : Type*} [Fintype J] [Fintype C] [AddCommGroup Q] {P : ℕ}
    (H : Host V I) (F : Set (Multiset I)) (b : S07V43.Bank V J C P)
    (w : Sym2 V → Q) (g : C → Q) (hb : b.Valid (Basal H F) w g) :
    ∃ Doff Don : Finset (Finset V), IsPacking H F Doff ∧ IsPacking H F Don ∧
      ∀ (z : Fin P → C → ℤ) (hs : b.Supplies z),
        ∃ D, IsDecomposition H F (S07V43.Bank.cover hs) D ∧ D ⊆ Doff ∪ Don := by
  choose Off hOff using hb.basalA
  choose On hOn using hb.basalT
  let Doff := univ.biUnion Off
  let Don := univ.biUnion On
  have hOffDis : ∀ i ∈ (univ : Finset J), ∀ j ∈ (univ : Finset J), i ≠ j →
      Disjoint (b.A i) (b.A j) := by
    intro i _ j _ hij
    exact (hb.pw i j hij).mono subset_union_left subset_union_left
  have hOffAll := decomposition_biUnion univ b.A Off hOffDis (fun i _ => hOff i)
  have hOnAll := decomposition_biUnion univ b.tot On (fun i _ j _ hij => hb.pw i j hij)
    (fun i _ => hOn i)
  refine ⟨Doff,Don,⟨hOffAll.1,hOffAll.2.1⟩,⟨hOnAll.1,hOnAll.2.1⟩,?_⟩
  intro z hs
  let Mode : J → Finset (Finset V) := fun i =>
    if i ∈ S07V43.Bank.selJ hs then Off i else On i
  have hMode : ∀ i ∈ (univ : Finset J),
      IsDecomposition H F (S07V43.Bank.mode hs i) (Mode i) := by
    intro i _
    dsimp only [S07V43.Bank.mode,Mode]
    split_ifs <;> first | exact hOff i | exact hOn i
  have hModeDis : ∀ i ∈ (univ : Finset J), ∀ j ∈ (univ : Finset J), i ≠ j →
      Disjoint (S07V43.Bank.mode hs i) (S07V43.Bank.mode hs j) := by
    intro i _ j _ hij
    exact (hb.pw i j hij).mono (S07V43.Bank.mode_subset hs i) (S07V43.Bank.mode_subset hs j)
  refine ⟨univ.biUnion Mode,decomposition_biUnion univ _ Mode hModeDis hMode,?_⟩
  intro T hT
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hT
  by_cases hSelected : i ∈ S07V43.Bank.selJ hs
  · have hiOff : T ∈ Off i := by simpa only [Mode,if_pos hSelected] using hi
    exact mem_union_left _ (mem_biUnion.mpr ⟨i,mem_univ _,hiOff⟩)
  · have hiOn : T ∈ On i := by simpa only [Mode,if_neg hSelected] using hi
    exact mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,hiOn⟩)

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.bank_cover_decompositions_in_fixed_union
