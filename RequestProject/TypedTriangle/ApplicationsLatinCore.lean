module
public import RequestProject.TypedTriangle.ApplicationsRainbowDefs
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin

abbrev Vertex (A : Type) := Fin 3 × A
abbrev host (A : Type) := Rainbow.host 3 A
abbrev types := Rainbow.types 3

def latinTriangle {A : Type} (x y z : A) : Finset (Vertex A) :=
  {(0,x),(1,y),(2,z)}

@[simp] theorem mem_latinTriangle {A : Type} (v : Vertex A) (x y z : A) :
    v ∈ latinTriangle x y z ↔ v=(0,x) ∨ v=(1,y) ∨ v=(2,z) := by
  simp [latinTriangle]

@[simp] theorem latinTriangle_card {A : Type} (x y z : A) :
    (latinTriangle x y z).card=3 := by simp [latinTriangle]

@[simp] theorem latinTriangle_eq_iff {A : Type} (x y z x' y' z' : A) :
    latinTriangle x y z=latinTriangle x' y' z' ↔ x=x' ∧ y=y' ∧ z=z' := by
  constructor
  · intro he
    have hx : (0,x) ∈ latinTriangle x' y' z' := he ▸ (by simp)
    have hy : (1,y) ∈ latinTriangle x' y' z' := he ▸ (by simp)
    have hz : (2,z) ∈ latinTriangle x' y' z' := he ▸ (by simp)
    simpa using And.intro hx (And.intro hy hz)
  · rintro ⟨rfl,rfl,rfl⟩; rfl

theorem latinTriangle_allowed {A : Type} [Fintype A] (x y z : A) :
    IsAllowed (host A) types (latinTriangle x y z) := by
  refine ⟨latinTriangle_card x y z,?_,?_⟩
  · intro u hu v hv hne
    simp only [mem_latinTriangle] at hu hv
    rcases hu with rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl <;>
      simp_all [host,Rainbow.host]
  · simp [types,Rainbow.types,latinTriangle,host,Rainbow.host]

theorem allowed_iff {A : Type} [Fintype A] (T : Finset (Vertex A)) :
    IsAllowed (host A) types T ↔ ∃ x y z, T=latinTriangle x y z := by
  constructor
  · intro hT
    have hinj : Set.InjOn Prod.fst (T : Set (Vertex A)) := by
      intro u hu v hv he
      by_contra hne
      exact hT.2.1 u hu v hv hne he
    have hImage : T.image Prod.fst=univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_iff.mpr hinj,hT.1]
      simp
    have hGet (i : Fin 3) : ∃ a, (i,a) ∈ T := by
      have hi : i ∈ T.image Prod.fst := by rw [hImage]; simp
      obtain ⟨⟨j,a⟩,ha,hj⟩ := Finset.mem_image.mp hi
      exact ⟨a,by simpa only using hj ▸ ha⟩
    obtain ⟨x,hx⟩ := hGet 0
    obtain ⟨y,hy⟩ := hGet 1
    obtain ⟨z,hz⟩ := hGet 2
    refine ⟨x,y,z,?_⟩
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      have hi : v.1=0 ∨ v.1=1 ∨ v.1=2 := by omega
      rcases hi with hi|hi|hi
      · exact (mem_latinTriangle _ _ _ _).mpr (Or.inl (hinj hv hx hi))
      · exact (mem_latinTriangle _ _ _ _).mpr (Or.inr (Or.inl (hinj hv hy hi)))
      · exact (mem_latinTriangle _ _ _ _).mpr (Or.inr (Or.inr (hinj hv hz hi)))
    · simp [hT.1]
  · rintro ⟨x,y,z,rfl⟩; exact latinTriangle_allowed x y z

@[simp] theorem edge01_mem {A : Type} (x y z u v : A) :
    s((0,x),(1,y)) ∈ triEdges (latinTriangle u v z) ↔ x=u ∧ y=v := by
  simp [mem_triEdges]

@[simp] theorem edge02_mem {A : Type} (x y z u v : A) :
    s((0,x),(2,z)) ∈ triEdges (latinTriangle u y v) ↔ x=u ∧ z=v := by
  simp [mem_triEdges]

@[simp] theorem edge12_mem {A : Type} (x y z u v : A) :
    s((1,y),(2,z)) ∈ triEdges (latinTriangle x u v) ↔ y=u ∧ z=v := by
  simp [mem_triEdges]

/-- A Latin square: every row and every column is a permutation. -/
structure LatinSquare (A : Type) where
  toFun : A → A → A
  row_bijective : ∀ x, Function.Bijective (toFun x)
  column_bijective : ∀ y, Function.Bijective (fun x => toFun x y)

instance {A : Type} : CoeFun (LatinSquare A) (fun _ => A → A → A) := ⟨LatinSquare.toFun⟩

def LatinSquare.add (A : Type) [AddGroup A] : LatinSquare A where
  toFun x y := x+y
  row_bijective x := ⟨fun _ _ he => add_left_cancel he,fun z => ⟨-x+z,by simp [←add_assoc]⟩⟩
  column_bijective y := ⟨fun _ _ he => add_right_cancel he,fun z => ⟨z+-y,by simp [add_assoc]⟩⟩

def decomposition {A : Type} [Fintype A] (L : LatinSquare A) : Finset (Finset (Vertex A)) :=
  univ.image (fun p : A×A => latinTriangle p.1 p.2 (L p.1 p.2))

@[simp] theorem mem_decomposition {A : Type} [Fintype A] (L : LatinSquare A) (T) :
    T ∈ decomposition L ↔ ∃ x y, T=latinTriangle x y (L x y) := by
  simp only [decomposition,mem_image,mem_univ,true_and,Prod.exists]
  constructor
  · rintro ⟨x,y,he⟩; exact ⟨x,y,he.symm⟩
  · rintro ⟨x,y,he⟩; exact ⟨x,y,he.symm⟩

theorem card_decomposition {A : Type} [Fintype A] (L : LatinSquare A) :
    (decomposition L).card=(Fintype.card A)^2 := by
  have hinj : Function.Injective (fun p : A×A => latinTriangle p.1 p.2 (L p.1 p.2)) := by
    intro p q he
    have ht := (latinTriangle_eq_iff _ _ _ _ _ _).mp he
    exact Prod.ext ht.1 ht.2.1
  simp [decomposition,Finset.card_image_of_injective _ hinj,Fintype.card_prod,pow_two]

theorem decomposition_exact {A : Type} [Fintype A] (L : LatinSquare A) :
    IsDecomposition (host A) types (edges (host A)) (decomposition L) := by
  letI : DecidableEq (Vertex A) := Classical.decEq _
  refine ⟨?_,?_,?_⟩
  · intro T hT
    obtain ⟨x,y,rfl⟩ := (mem_decomposition _ _).mp hT
    exact latinTriangle_allowed _ _ _
  · intro T hT U hU hne
    apply Finset.disjoint_left.mpr
    intro e heT heU
    obtain ⟨x,y,rfl⟩ := (mem_decomposition _ _).mp hT
    obtain ⟨u,v,rfl⟩ := (mem_decomposition _ _).mp hU
    revert heT heU
    refine Sym2.inductionOn e ?_
    intro a b ha hb
    rw [mem_triEdges] at ha hb
    have hEq : latinTriangle x y (L x y)=latinTriangle u v (L u v) := by
      rcases a with ⟨i,a⟩
      rcases b with ⟨j,b⟩
      fin_cases i <;> fin_cases j
      · have ha' : a=x := by simpa using ha.1
        have hb' : b=x := by simpa using ha.2.1
        exact False.elim (ha.2.2 (Prod.ext rfl (ha'.trans hb'.symm)))
      · have hax : a=x := by simpa using ha.1
        have hby : b=y := by simpa using ha.2.1
        have hau : a=u := by simpa using hb.1
        have hbv : b=v := by simpa using hb.2.1
        have hxu := hax.symm.trans hau
        have hyv := hby.symm.trans hbv
        rw [←hxu,←hyv]
      · have hax : a=x := by simpa using ha.1
        have hbL : b=L x y := by simpa using ha.2.1
        have hau : a=u := by simpa using hb.1
        have hbL' : b=L u v := by simpa using hb.2.1
        have hxu := hax.symm.trans hau
        rw [←hxu] at hbL'
        have hyv := (L.row_bijective x).1 (hbL.symm.trans hbL')
        rw [←hxu,←hyv]
      · have hay : a=y := by simpa using ha.1
        have hbx : b=x := by simpa using ha.2.1
        have hav : a=v := by simpa using hb.1
        have hbu : b=u := by simpa using hb.2.1
        have hxu := hbx.symm.trans hbu
        have hyv := hay.symm.trans hav
        rw [←hxu,←hyv]
      · have ha' : a=y := by simpa using ha.1
        have hb' : b=y := by simpa using ha.2.1
        exact False.elim (ha.2.2 (Prod.ext rfl (ha'.trans hb'.symm)))
      · have hay : a=y := by simpa using ha.1
        have hbL : b=L x y := by simpa using ha.2.1
        have hav : a=v := by simpa using hb.1
        have hbL' : b=L u v := by simpa using hb.2.1
        have hyv := hay.symm.trans hav
        rw [←hyv] at hbL'
        have hxu := (L.column_bijective y).1 (hbL.symm.trans hbL')
        rw [←hxu,←hyv]
      · have haL : a=L x y := by simpa using ha.1
        have hbx : b=x := by simpa using ha.2.1
        have haL' : a=L u v := by simpa using hb.1
        have hbu : b=u := by simpa using hb.2.1
        have hxu := hbx.symm.trans hbu
        rw [←hxu] at haL'
        have hyv := (L.row_bijective x).1 (haL.symm.trans haL')
        rw [←hxu,←hyv]
      · have haL : a=L x y := by simpa using ha.1
        have hby : b=y := by simpa using ha.2.1
        have haL' : a=L u v := by simpa using hb.1
        have hbv : b=v := by simpa using hb.2.1
        have hyv := hby.symm.trans hbv
        rw [←hyv] at haL'
        have hxu := (L.column_bijective y).1 (haL.symm.trans haL')
        rw [←hxu,←hyv]
      · have ha' : a=L x y := by simpa using ha.1
        have hb' : b=L x y := by simpa using ha.2.1
        exact False.elim (ha.2.2 (Prod.ext rfl (ha'.trans hb'.symm)))
    exact hne hEq
  · ext e
    refine Sym2.inductionOn e ?_
    intro a b
    constructor
    · intro he
      obtain ⟨T,hT,he⟩ := mem_biUnion.mp he
      have ha := (latinTriangle_allowed : ∀x y z,IsAllowed (host A) types (latinTriangle x y z))
      obtain ⟨x,y,rfl⟩ := (mem_decomposition _ _).mp hT
      rw [mem_triEdges] at he
      exact mem_filter.mpr ⟨mem_univ _,(ha x y (L x y)).2.1 a he.1 b he.2.1 he.2.2⟩
    · intro he
      have hij : a.1≠b.1 := (mem_filter.mp he).2
      rcases a with ⟨i,a⟩
      rcases b with ⟨j,b⟩
      have h01 (x y : A) : s((0,x),(1,y)) ∈ (decomposition L).biUnion triEdges := by
        apply mem_biUnion.mpr
        exact ⟨latinTriangle x y (L x y),(mem_decomposition _ _).mpr ⟨x,y,rfl⟩,by simp⟩
      have h02 (x z : A) : s((0,x),(2,z)) ∈ (decomposition L).biUnion triEdges := by
        obtain ⟨y,hy⟩ := (L.row_bijective x).2 z
        apply mem_biUnion.mpr
        exact ⟨latinTriangle x y (L x y),(mem_decomposition _ _).mpr ⟨x,y,rfl⟩,by simp [hy]⟩
      have h12 (y z : A) : s((1,y),(2,z)) ∈ (decomposition L).biUnion triEdges := by
        obtain ⟨x,hx⟩ := (L.column_bijective y).2 z
        apply mem_biUnion.mpr
        exact ⟨latinTriangle x y (L x y),(mem_decomposition _ _).mpr ⟨x,y,rfl⟩,by simp [hx]⟩
      have h10 (y x : A) : s((1,y),(0,x)) ∈ (decomposition L).biUnion triEdges := by
        rw [Sym2.eq_swap]
        exact h01 x y
      have h20 (z x : A) : s((2,z),(0,x)) ∈ (decomposition L).biUnion triEdges := by
        rw [Sym2.eq_swap]
        exact h02 x z
      have h21 (z y : A) : s((2,z),(1,y)) ∈ (decomposition L).biUnion triEdges := by
        rw [Sym2.eq_swap]
        exact h12 y z
      fin_cases i <;> fin_cases j <;> simp only [Fin.isValue,ne_eq,not_true_eq_false] at hij
      all_goals first | contradiction | exact h01 a b | exact h02 a b | exact h12 a b |
        exact h10 a b | exact h20 a b | exact h21 a b

theorem additive_isPhysical (A : Type) [Fintype A] [AddGroup A] :
    IsPhysical (host A) types (edges (host A)) :=
  isPhysical_of_isDecomposition (decomposition_exact (LatinSquare.add A))

#print axioms allowed_iff
#print axioms decomposition_exact
#print axioms additive_isPhysical
end TypedTriangle.Applications.Latin
