module
public import RequestProject.TypedTriangle.ApplicationsLatinCore
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin

theorem exists_unique_symbol {A : Type} [Fintype A] {D : Finset (Finset (Vertex A))}
    (hD : IsDecomposition (host A) types (edges (host A)) D) (x y : A) :
    ∃! z,latinTriangle x y z ∈ D := by
  have he : s((0,x),(1,y)) ∈ edges (host A) := by simp [edges,host,Rainbow.host]
  obtain ⟨T,hT,heT⟩ := hD.exists_mem he
  obtain ⟨u,v,z,rfl⟩ := (allowed_iff T).mp (hD.1 T hT)
  obtain ⟨rfl,rfl⟩ := edge01_mem x y z u v |>.mp heT
  refine ⟨z,hT,?_⟩
  intro z' hz'
  have ht := hD.unique hz' hT
    (show s((0,x),(1,y)) ∈ triEdges (latinTriangle x y z') by simp)
    (show s((0,x),(1,y)) ∈ triEdges (latinTriangle x y z) by simp)
  exact ((latinTriangle_eq_iff _ _ _ _ _ _).mp ht).2.2

def symbol {A : Type} [Fintype A] {D : Finset (Finset (Vertex A))}
    (hD : IsDecomposition (host A) types (edges (host A)) D) (x y : A) : A :=
  Classical.choose (exists_unique_symbol hD x y)

theorem symbol_mem {A : Type} [Fintype A] {D : Finset (Finset (Vertex A))}
    (hD : IsDecomposition (host A) types (edges (host A)) D) (x y : A) :
    latinTriangle x y (symbol hD x y) ∈ D :=
  (Classical.choose_spec (exists_unique_symbol hD x y)).1

theorem eq_symbol_of_mem {A : Type} [Fintype A] {D : Finset (Finset (Vertex A))}
    (hD : IsDecomposition (host A) types (edges (host A)) D) (x y z : A)
    (hz : latinTriangle x y z ∈ D) : z=symbol hD x y :=
  (Classical.choose_spec (exists_unique_symbol hD x y)).2 z hz

theorem symbol_row_bijective {A : Type} [Fintype A] {D : Finset (Finset (Vertex A))}
    (hD : IsDecomposition (host A) types (edges (host A)) D) (x : A) :
    Function.Bijective (symbol hD x) := by
  constructor
  · intro y y' he
    have ht := hD.unique (symbol_mem hD x y) (symbol_mem hD x y')
      (show s((0,x),(2,symbol hD x y)) ∈ triEdges (latinTriangle x y (symbol hD x y)) by simp)
      (show s((0,x),(2,symbol hD x y)) ∈ triEdges (latinTriangle x y' (symbol hD x y')) by simp [he])
    exact ((latinTriangle_eq_iff _ _ _ _ _ _).mp ht).2.1
  · intro z
    have he : s((0,x),(2,z)) ∈ edges (host A) := by simp [edges,host,Rainbow.host]
    obtain ⟨T,hT,heT⟩ := hD.exists_mem he
    obtain ⟨u,y,v,rfl⟩ := (allowed_iff T).mp (hD.1 T hT)
    obtain ⟨rfl,rfl⟩ := edge02_mem x y z u v |>.mp heT
    exact ⟨y,(eq_symbol_of_mem hD x y z hT).symm⟩

theorem symbol_column_bijective {A : Type} [Fintype A] {D : Finset (Finset (Vertex A))}
    (hD : IsDecomposition (host A) types (edges (host A)) D) (y : A) :
    Function.Bijective (fun x => symbol hD x y) := by
  constructor
  · intro x x' he
    have ht := hD.unique (symbol_mem hD x y) (symbol_mem hD x' y)
      (show s((1,y),(2,symbol hD x y)) ∈ triEdges (latinTriangle x y (symbol hD x y)) by simp)
      (show s((1,y),(2,symbol hD x y)) ∈ triEdges (latinTriangle x' y (symbol hD x' y)) by simp [he])
    exact ((latinTriangle_eq_iff _ _ _ _ _ _).mp ht).1
  · intro z
    have he : s((1,y),(2,z)) ∈ edges (host A) := by simp [edges,host,Rainbow.host]
    obtain ⟨T,hT,heT⟩ := hD.exists_mem he
    obtain ⟨x,u,v,rfl⟩ := (allowed_iff T).mp (hD.1 T hT)
    obtain ⟨rfl,rfl⟩ := edge12_mem x y z u v |>.mp heT
    exact ⟨x,(eq_symbol_of_mem hD x y z hT).symm⟩

def ofDecomposition {A : Type} [Fintype A] {D : Finset (Finset (Vertex A))}
    (hD : IsDecomposition (host A) types (edges (host A)) D) : LatinSquare A where
  toFun := symbol hD
  row_bijective := symbol_row_bijective hD
  column_bijective := symbol_column_bijective hD

theorem decomposition_ofDecomposition {A : Type} [Fintype A] {D : Finset (Finset (Vertex A))}
    (hD : IsDecomposition (host A) types (edges (host A)) D) :
    decomposition (ofDecomposition hD)=D := by
  ext T
  constructor
  · intro hT
    obtain ⟨x,y,rfl⟩ := (mem_decomposition _ _).mp hT
    exact symbol_mem hD x y
  · intro hT
    obtain ⟨x,y,z,rfl⟩ := (allowed_iff T).mp (hD.1 T hT)
    apply (mem_decomposition _ _).mpr
    exact ⟨x,y,by rw [eq_symbol_of_mem hD x y z hT]; rfl⟩

theorem isDecomposition_iff_latinSquare {A : Type} [Fintype A] (D : Finset (Finset (Vertex A))) :
    IsDecomposition (host A) types (edges (host A)) D ↔ ∃ L : LatinSquare A,decomposition L=D := by
  constructor
  · intro hD; exact ⟨ofDecomposition hD,decomposition_ofDecomposition hD⟩
  · rintro ⟨L,rfl⟩; exact decomposition_exact L

#print axioms isDecomposition_iff_latinSquare
end TypedTriangle.Applications.Latin
