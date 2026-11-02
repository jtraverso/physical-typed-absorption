module
public import RequestProject.TypedTriangle.ApplicationsLatinPaschClassification
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin

@[simp] theorem latinTriangle_mem_decomposition {A : Type} [Fintype A]
    (L : LatinSquare A) (r c s : A) :
    latinTriangle r c s∈decomposition L ↔ s=L r c := by
  simp only [mem_decomposition,latinTriangle_eq_iff]
  constructor
  · rintro ⟨x,y,hx,hy,hs⟩
    simpa only [←hx,←hy] using hs
  · intro h
    exact ⟨r,c,rfl,rfl,h⟩

/-- The usual alternating two by two subarray, without ordering its rows
or columns. Each element of this finset is its literal four-cell set. -/
def intercalateCells {A : Type} (r r' c c' : A) : Finset (A×A) :=
  {(r,c),(r,c'),(r',c),(r',c')}

def intercalates {A : Type} [Fintype A] (L : LatinSquare A) : Finset (Finset (A×A)) :=
  ((univ : Finset (A×A×A×A)).filter (fun p =>
    p.2.1 ≠ p.1 ∧ p.2.2.2 ≠ p.2.2.1 ∧
      L p.2.1 p.2.2.1=L p.1 p.2.2.2 ∧ L p.2.1 p.2.2.2=L p.1 p.2.2.1)).image
    (fun p => intercalateCells p.1 p.2.1 p.2.2.1 p.2.2.2)

@[simp] theorem mem_intercalates {A : Type} [Fintype A]
    (L : LatinSquare A) (B : Finset (A×A)) :
    B∈intercalates L ↔ ∃ r r' c c', r'≠r ∧ c'≠c ∧
      L r' c=L r c' ∧ L r' c'=L r c ∧ B=intercalateCells r r' c c' := by
  simp only [intercalates,mem_image,mem_filter,mem_univ,true_and,Prod.exists]
  constructor
  · rintro ⟨r,r',c,c',h,he⟩
    exact ⟨r,r',c,c',h.1,h.2.1,h.2.2.1,h.2.2.2,he.symm⟩
  · rintro ⟨r,r',c,c',hr,hc,h1,h2,he⟩
    exact ⟨r,r',c,c',⟨hr,hc,h1,h2⟩,he.symm⟩

def encodeCells {A : Type} (L : LatinSquare A) (B : Finset (A×A)) :
    Finset (Finset (Vertex A)) :=
  B.image (fun p => latinTriangle p.1 p.2 (L p.1 p.2))

theorem encodeCells_injective {A : Type} (L : LatinSquare A) :
    Function.Injective (encodeCells L) := by
  apply Finset.image_injective
  intro p q he
  have hh := (latinTriangle_eq_iff _ _ _ _ _ _).mp he
  exact Prod.ext hh.1 hh.2.1

theorem encode_intercalateCells {A : Type} (L : LatinSquare A) (r r' c c' : A)
    (h1 : L r' c=L r c') (h2 : L r' c'=L r c) :
    encodeCells L (intercalateCells r r' c c')=
      latinPasch r r' c c' (L r c) (L r c') := by
  simp only [encodeCells,intercalateCells,latinPasch,image_insert,image_singleton,
    h1,h2]

theorem configurations_decomposition_iff {A : Type} [Fintype A] (L : LatinSquare A)
    (S : Finset (Finset (Vertex A))) :
    S∈Pasch.configurations (decomposition L) ↔
      ∃ r r' c c', r'≠r ∧ c'≠c ∧ L r' c=L r c' ∧ L r' c'=L r c ∧
        S=latinPasch r r' c c' (L r c) (L r c') := by
  constructor
  · intro hS
    obtain ⟨hSub,hCard,hPasch⟩ := Pasch.mem_configurations.mp hS
    obtain ⟨Q,hQ⟩ := card_pos.mp (by omega : 0<S.card)
    obtain ⟨r,c,rfl⟩ := (mem_decomposition L Q).mp (hSub hQ)
    obtain ⟨r',c',s',hr,hc,hs,hEq⟩ := isPasch_rooted_classification hPasch
      (fun Q hQ => (decomposition_exact L).1 Q (hSub hQ)) hQ
    have h1 : s'=L r c' := latinTriangle_mem_decomposition L r c' s' |>.mp
      (hSub (by rw [hEq]; simp [latinPasch]))
    have h2 : s'=L r' c := latinTriangle_mem_decomposition L r' c s' |>.mp
      (hSub (by rw [hEq]; simp [latinPasch]))
    have h3 : L r c=L r' c' := latinTriangle_mem_decomposition L r' c' (L r c) |>.mp
      (hSub (by rw [hEq]; simp [latinPasch]))
    exact ⟨r,r',c,c',hr,hc,h2.symm.trans h1,h3.symm,by simpa only [h1] using hEq⟩
  · rintro ⟨r,r',c,c',hr,hc,h1,h2,rfl⟩
    have hs : L r c≠L r c' := fun he => hc (((L.row_bijective r).1 he).symm)
    have hPasch := latinPasch_isPasch hr.symm hc.symm hs
    apply Pasch.mem_configurations.mpr
    refine ⟨?_,hPasch.1,hPasch⟩
    intro Q hQ
    simp only [latinPasch,mem_insert,mem_singleton] at hQ
    rcases hQ with rfl|rfl|rfl|rfl <;> simp [h1,h2]

theorem encodeCells_mem_configurations {A : Type} [Fintype A]
    (L : LatinSquare A) {B : Finset (A×A)} (hB : B∈intercalates L) :
    encodeCells L B∈Pasch.configurations (decomposition L) := by
  obtain ⟨r,r',c,c',hr,hc,h1,h2,rfl⟩ := mem_intercalates L B |>.mp hB
  rw [encode_intercalateCells L r r' c c' h1 h2]
  exact (configurations_decomposition_iff L _).mpr ⟨r,r',c,c',hr,hc,h1,h2,rfl⟩

/-- A literal bijection between conventional Latin intercalates and the
unoriented Pasch configurations counted by Paper III. -/
def intercalatesEquivPasch {A : Type} [Fintype A] (L : LatinSquare A) :
    {B // B∈intercalates L} ≃ {S // S∈Pasch.configurations (decomposition L)} :=
  Equiv.ofBijective (fun B => ⟨encodeCells L B.val,encodeCells_mem_configurations L B.property⟩)
    ⟨by
      intro B C he
      exact Subtype.ext (encodeCells_injective L (congrArg Subtype.val he)),by
      intro S
      obtain ⟨r,r',c,c',hr,hc,h1,h2,hEq⟩ :=
        (configurations_decomposition_iff L S.val).mp S.property
      refine ⟨⟨intercalateCells r r' c c',
        (mem_intercalates L _).mpr ⟨r,r',c,c',hr,hc,h1,h2,rfl⟩⟩,?_⟩
      apply Subtype.ext
      exact (encode_intercalateCells L r r' c c' h1 h2).trans hEq.symm⟩

theorem count_decomposition_eq_intercalates {A : Type} [Fintype A] (L : LatinSquare A) :
    Pasch.count (decomposition L)=(intercalates L).card := by
  simpa only [Pasch.count,Fintype.card_coe] using
    (Fintype.card_congr (intercalatesEquivPasch L)).symm

#print axioms intercalatesEquivPasch
#print axioms count_decomposition_eq_intercalates
end TypedTriangle.Applications.Latin
