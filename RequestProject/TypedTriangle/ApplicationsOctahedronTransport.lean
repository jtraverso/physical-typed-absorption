module
public import RequestProject.TypedTriangle.ApplicationsOctahedronLedger
public import RequestProject.TypedTriangle.VortexEmbeddedPaidAssembly
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Octahedron

def coreImage {V : Type} (f : Fin 6 ↪ V) : Finset (Sym2 V) :=
  core.image (Sym2.map f)

theorem edge_at_zero {V : Type} (f : Fin 6 ↪ V) (x : V) :
    s(f 0,x)∈coreImage f ↔ x=f 5 := by
  simp [coreImage,core,Sym2.eq_iff,f.injective.eq_iff]

theorem edge_at_one {V : Type} (f : Fin 6 ↪ V) (x : V) :
    s(f 1,x)∈coreImage f ↔ x=f 4 := by
  simp [coreImage,core,Sym2.eq_iff,f.injective.eq_iff]

theorem support_coreImage {V : Type} [Fintype V] (f : Fin 6 ↪ V) :
    support (coreImage f)=(univ : Finset (Fin 6)).map f := by
  have hSupport : support (coreImage f)=(support core).map f := by
    ext v
    constructor
    · intro hv
      obtain ⟨_,e,he,hve⟩ := mem_filter.mp hv
      obtain ⟨e',he',rfl⟩ := mem_image.mp he
      obtain ⟨x,hx,rfl⟩ := Sym2.mem_map.mp hve
      have hs : x∈support core := by
        simpa only [support,mem_filter,mem_univ,true_and] using
          (show ∃ e∈core,x∈e from ⟨e',he',hx⟩)
      exact mem_map.mpr ⟨x,hs,rfl⟩
    · intro hv
      obtain ⟨x,hx,rfl⟩ := mem_map.mp hv
      obtain ⟨e,he,hxe⟩ : ∃ e∈core,x∈e := by
        simpa only [support,mem_filter,mem_univ,true_and] using hx
      exact mem_filter.mpr ⟨mem_univ _,Sym2.map f e,
        mem_image.mpr ⟨e,he,rfl⟩,Sym2.mem_map.mpr ⟨x,hxe,rfl⟩⟩
  rw [hSupport,core_support]

theorem card_support_coreImage {V : Type} [Fintype V] (f : Fin 6 ↪ V) :
    (support (coreImage f)).card=6 := by
  rw [support_coreImage,card_map]
  rfl

private theorem modeImage_decomposition {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (f : Fin 6 ↪ V)
    (a b : Fin 6) (hab : (a=2 ∧ b=3) ∨ (a=3 ∧ b=2))
    (hAllowed : ∀ T∈mode 2 3∪mode 3 2,IsAllowed H F (T.map f)) :
    IsDecomposition H F (coreImage f∪wedge (f 0) (f 1) (f a))
      ((mode a b).image (fun T => T.map f)) := by
  refine ⟨?_,?_,?_⟩
  · intro T hT
    obtain ⟨Q,hQ,rfl⟩ := mem_image.mp hT
    apply hAllowed
    rcases hab with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact mem_union_left _ hQ
    · exact mem_union_right _ hQ
  · intro T hT U hU hne
    obtain ⟨Q,hQ,rfl⟩ := mem_image.mp hT
    obtain ⟨R,hR,rfl⟩ := mem_image.mp hU
    change Disjoint (triEdges (Q.map f)) (triEdges (R.map f))
    rw [Vortex.triEdges_embedding,Vortex.triEdges_embedding]
    apply disjoint_left.mpr
    intro e he he'
    obtain ⟨g,hg,hge⟩ := mem_image.mp he
    obtain ⟨g',hg',hg'e⟩ := mem_image.mp he'
    have hgg : g=g' := Sym2.map.injective f.injective (hge.trans hg'e.symm)
    exact disjoint_left.mp (mode_pairwise a b hab hQ hR
      (fun heq => hne (congrArg (fun Q => Q.map f) heq))) hg (hgg ▸ hg')
  · have hCover : ((mode a b).image (fun T => T.map f)).biUnion triEdges =
        ((mode a b).biUnion triEdges).image (Sym2.map f) := by
      ext e
      simp only [mem_biUnion,mem_image]
      constructor
      · rintro ⟨Q,⟨T,hT,rfl⟩,he⟩
        rw [Vortex.triEdges_embedding] at he
        obtain ⟨g,hg,hge⟩ := mem_image.mp he
        exact ⟨g,⟨T,hT,hg⟩,hge⟩
      · rintro ⟨g,⟨T,hT,hg⟩,hge⟩
        exact ⟨T.map f,⟨T,hT,rfl⟩,by
          rw [Vortex.triEdges_embedding]
          exact mem_image.mpr ⟨g,hg,hge⟩⟩
    rw [hCover,mode_cover a b hab]
    simp [coreImage,wedge,image_union,union_comm,union_left_comm,union_assoc]

/-- An injective copy of the finite two-mode certificate is a genuine
physical hinge in the ambient host. -/
theorem hinge_of_modes {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (f : Fin 6 ↪ V)
    (hAllowed : ∀ T∈mode 2 3∪mode 3 2,IsAllowed H F (T.map f)) :
    IsHinge H F (f 0) (f 1) (f 2) (f 3) (coreImage f) := by
  have hDecA := modeImage_decomposition H F f 2 3 (Or.inl ⟨rfl,rfl⟩) hAllowed
  have hDecB := modeImage_decomposition H F f 3 2 (Or.inr ⟨rfl,rfl⟩) hAllowed
  refine ⟨?_,?_,⟨_,hDecA⟩,⟨_,hDecB⟩⟩
  · intro e he
    obtain ⟨Q,hQ,heQ⟩ := hDecA.exists_mem (mem_union_left _ he)
    exact triEdges_subset_edges (hDecA.1 Q hQ) heQ
  · have hAvoid : Disjoint (coreImage f)
        ((triEdges ({0,1,2} : Finset (Fin 6))∪triEdges {0,1,3}).image (Sym2.map f)) := by
      apply disjoint_left.mpr
      intro e he he'
      obtain ⟨g,hg,hge⟩ := mem_image.mp he
      obtain ⟨g',hg',hg'e⟩ := mem_image.mp he'
      have hgg : g=g' := Sym2.map.injective f.injective (hge.trans hg'e.symm)
      exact disjoint_left.mp core_avoids hg (hgg ▸ hg')
    have hTa : ({0,1,2} : Finset (Fin 6)).map f={f 0,f 1,f 2} := by simp
    have hTb : ({0,1,3} : Finset (Fin 6)).map f={f 0,f 1,f 3} := by simp
    rw [←hTa,←hTb,Vortex.triEdges_embedding,Vortex.triEdges_embedding]
    simpa only [image_union,Vortex.embeddedEdges] using hAvoid

#print axioms support_coreImage
#print axioms hinge_of_modes
#print axioms edge_at_zero
#print axioms edge_at_one
end TypedTriangle.Applications.Octahedron
