module
public import RequestProject.TypedTriangle.ApplicationsLatinCore
public import RequestProject.TypedTriangle.PaschEmbedding
public import RequestProject.TypedTriangle.PaschRootedInfluence
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin

/-- The two-symbol rectangle, with the first symbol on its diagonal. -/
def latinPasch {A : Type} (r r' c c' s s' : A) : Finset (Finset (Vertex A)) :=
  {latinTriangle r c s, latinTriangle r c' s',
    latinTriangle r' c s', latinTriangle r' c' s}

theorem latinPasch_isPasch {A : Type} {r r' c c' s s' : A}
    (hr : r ≠ r') (hc : c ≠ c') (hs : s ≠ s') :
    Pasch.IsPasch (latinPasch r r' c c' s s') := by
  let f : Fin 6 → Vertex A := ![(0,r),(0,r'),(1,c),(1,c'),(2,s),(2,s')]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f,Prod.mk.injEq]
  have he : Pasch.gridImage f = latinPasch r r' c c' s s' := by
    simp [Pasch.gridImage,Pasch.gridPasch,f,latinPasch,latinTriangle,
      Finset.insert_comm]
  rw [←he]
  exact Pasch.gridImage_isPasch f hf

/-- In a tripartite allowed universe, every Pasch through a fixed triple
is precisely one two-symbol rectangle. The six coordinates are recovered
from its literal blocks. -/
theorem isPasch_rooted_classification {A : Type} [Fintype A]
    {S : Finset (Finset (Vertex A))} (hS : Pasch.IsPasch S)
    (hAllowed : ∀ Q ∈ S, IsAllowed (host A) types Q)
    {r c s : A} (hQ : latinTriangle r c s ∈ S) :
    ∃ r' c' s', r' ≠ r ∧ c' ≠ c ∧ s' ≠ s ∧ S=latinPasch r r' c c' s s' := by
  obtain ⟨v,B,C,hB,hC,hBQ,hCQ,hBC,hrB,hcC,hvB,hvC,hvQ⟩ :=
    Pasch.exists_rooted_witness hS hQ (a:=(0,r)) (b:=(1,c)) (by simp) (by simp)
      (by simp : ((0,r) : Vertex A) ≠ (1,c))
  obtain ⟨rB,c',s',hBEq⟩ := (allowed_iff B).mp (hAllowed B hB)
  obtain ⟨r',cC,sC,hCEq⟩ := (allowed_iff C).mp (hAllowed C hC)
  have hrBEq : r=rB := by simpa only [hBEq,mem_latinTriangle,Prod.mk.injEq,
    Fin.reduceEq,true_and,false_and,false_or,or_false] using hrB
  have hcCEq : c=cC := by simpa only [hCEq,mem_latinTriangle,Prod.mk.injEq,
    Fin.reduceEq,true_and,false_and,false_or,or_false] using hcC
  subst rB
  subst cC
  subst B
  subst C
  have hc' : c' ≠ c := by
    intro he
    subst c'
    exact hBQ (Pasch.eq_of_common_pair hS.2.2.2.2 hB hQ
      (by simp : ((0,r) : Vertex A) ≠ (1,c)) (by simp) (by simp) (by simp) (by simp))
  have hr' : r' ≠ r := by
    intro he
    subst r'
    exact hCQ (Pasch.eq_of_common_pair hS.2.2.2.2 hC hQ
      (by simp : ((0,r) : Vertex A) ≠ (1,c)) (by simp) (by simp) (by simp) (by simp))
  have hs' : s' ≠ s := by
    intro he
    subst s'
    exact hBQ (Pasch.eq_of_common_pair hS.2.2.2.2 hB hQ
      (by simp : ((0,r) : Vertex A) ≠ (2,s)) (by simp) (by simp) (by simp) (by simp))
  have hss : s'=sC := by
    simp only [mem_latinTriangle] at hvB hvC
    rcases hvB with rfl|rfl|rfl <;> rcases hvC with h|h|h <;>
      simp_all [Prod.mk.injEq]
  subst sC
  have hPattern := latinPasch_isPasch hr'.symm hc'.symm hs'.symm
  refine ⟨r',c',s',hr',hc',hs',?_⟩
  apply hS.eq_of_common_triple hPattern (K:={latinTriangle r c s,
    latinTriangle r c' s',latinTriangle r' c s'})
  · simp [latinTriangle_eq_iff,hr',hc',hs',Ne.symm hr',Ne.symm hc',Ne.symm hs']
  · simp only [insert_subset_iff,singleton_subset_iff]
    exact ⟨hQ,hB,hC⟩
  · intro Q hQ'
    simp only [mem_insert,mem_singleton] at hQ'
    rcases hQ' with rfl|rfl|rfl <;> simp [latinPasch]

theorem latinPasch_rooted_injective {A : Type} {r c s : A}
    {r₁ c₁ s₁ r₂ c₂ s₂ : A}
    (hr : r₁ ≠ r) (hc : c₁ ≠ c) (hs : s₁ ≠ s)
    (he : latinPasch r r₁ c c₁ s s₁=latinPasch r r₂ c c₂ s s₂) :
    r₁=r₂ ∧ c₁=c₂ ∧ s₁=s₂ := by
  have hR : ((0,r₁) : Vertex A) ∈ (latinPasch r r₂ c c₂ s s₂).biUnion id := by
    rw [←he]
    simp [latinPasch,latinTriangle]
  have hC : ((1,c₁) : Vertex A) ∈ (latinPasch r r₂ c c₂ s s₂).biUnion id := by
    rw [←he]
    simp [latinPasch,latinTriangle]
  have hS : ((2,s₁) : Vertex A) ∈ (latinPasch r r₂ c c₂ s s₂).biUnion id := by
    rw [←he]
    simp [latinPasch,latinTriangle]
  have hR' : r₁=r ∨ r₁=r₂ := by simpa [latinPasch,latinTriangle,or_comm] using hR
  have hC' : c₁=c ∨ c₁=c₂ := by simpa [latinPasch,latinTriangle,or_comm] using hC
  have hS' : s₁=s ∨ s₁=s₂ := by simpa [latinPasch,latinTriangle,or_comm] using hS
  exact ⟨hR'.resolve_left hr,hC'.resolve_left hc,hS'.resolve_left hs⟩

def rootedAlternatives {A : Type} [Fintype A] (r c s : A) : Finset (A×A×A) :=
  (univ.erase r).product ((univ.erase c).product (univ.erase s))

@[simp] theorem mem_rootedAlternatives {A : Type} [Fintype A] (r c s : A)
    (p : A×A×A) : p ∈ rootedAlternatives r c s ↔
      p.1 ≠ r ∧ p.2.1 ≠ c ∧ p.2.2 ≠ s := by
  simp [rootedAlternatives]

/-- This is an equality of the actual configuration finsets, rather than
an encoding whose surjectivity is an additional hypothesis. -/
theorem rooted_configurations_eq_image {A : Type} [Fintype A] (r c s : A) :
    (Pasch.configurations (allowed (host A) types)).filter (fun S => latinTriangle r c s ∈ S) =
      (rootedAlternatives r c s).image (fun p => latinPasch r p.1 c p.2.1 s p.2.2) := by
  ext S
  constructor
  · intro hS
    obtain ⟨hSC,hRoot⟩ := mem_filter.mp hS
    obtain ⟨hSub,_,hPasch⟩ := Pasch.mem_configurations.mp hSC
    obtain ⟨r',c',s',hr,hc,hs,rfl⟩ := isPasch_rooted_classification hPasch
      (fun Q hQ => isAllowed_of_mem_allowed (hSub hQ)) hRoot
    exact mem_image.mpr ⟨(r',c',s'),(mem_rootedAlternatives r c s (r',c',s')).mpr ⟨hr,hc,hs⟩,rfl⟩
  · intro hS
    obtain ⟨⟨r',c',s'⟩,hp,rfl⟩ := mem_image.mp hS
    obtain ⟨hr,hc,hs⟩ := (mem_rootedAlternatives r c s (r',c',s')).mp hp
    have hPasch := latinPasch_isPasch hr.symm hc.symm hs.symm
    apply mem_filter.mpr
    refine ⟨Pasch.mem_configurations.mpr ⟨?_,hPasch.1,hPasch⟩,by simp [latinPasch]⟩
    intro Q hQ
    simp only [latinPasch,mem_insert,mem_singleton] at hQ
    rcases hQ with rfl|rfl|rfl|rfl <;>
      simpa only [allowed,mem_filter,mem_univ,true_and] using (latinTriangle_allowed _ _ _)

theorem rootedAlternatives_injective {A : Type} [Fintype A] (r c s : A) :
    Set.InjOn (fun p : A×A×A => latinPasch r p.1 c p.2.1 s p.2.2)
      (rootedAlternatives r c s : Set (A×A×A)) := by
  intro p hp q hq he
  obtain ⟨hr,hc,hs⟩ := (mem_rootedAlternatives r c s p).mp hp
  obtain ⟨hR,hC,hS⟩ := latinPasch_rooted_injective hr hc hs he
  exact Prod.ext hR (Prod.ext hC hS)

theorem rootedCount_allowed {A : Type} [Fintype A] (r c s : A) :
    Pasch.rootedCount (allowed (host A) types) (latinTriangle r c s) =
      (Fintype.card A-1)^3 := by
  unfold Pasch.rootedCount
  rw [rooted_configurations_eq_image,card_image_iff.mpr (rootedAlternatives_injective r c s)]
  simp [rootedAlternatives,card_erase_of_mem,pow_succ,Nat.mul_assoc]

#print axioms latinPasch_isPasch
#print axioms isPasch_rooted_classification
#print axioms latinPasch_rooted_injective
#print axioms rooted_configurations_eq_image
#print axioms rootedCount_allowed
end TypedTriangle.Applications.Latin
