module
public import RequestProject.TypedTriangle.ApplicationsRainbowDefs
public import RequestProject.TypedTriangle.Basic
@[expose] public section
open Finset
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace TypedTriangle.Applications.FivePartite

/-- The thirty blocks of a 3-GDD of type 3^5. They are the non-ray
lines of the additive Steiner triple system on F4^2 minus zero. -/
def baseBlocks : Finset (Finset (Fin 5 × Fin 3)) :=
  {    {(0,0),(1,0),(4,0)},
    {(0,0),(1,1),(3,2)},
    {(0,0),(1,2),(2,1)},
    {(0,0),(2,0),(4,1)},
    {(0,0),(2,2),(3,1)},
    {(0,0),(3,0),(4,2)},
    {(0,1),(1,0),(2,2)},
    {(0,1),(1,1),(4,1)},
    {(0,1),(1,2),(3,0)},
    {(0,1),(2,0),(3,2)},
    {(0,1),(2,1),(4,2)},
    {(0,1),(3,1),(4,0)},
    {(0,2),(1,0),(3,1)},
    {(0,2),(1,1),(2,0)},
    {(0,2),(1,2),(4,2)},
    {(0,2),(2,1),(3,0)},
    {(0,2),(2,2),(4,0)},
    {(0,2),(3,2),(4,1)},
    {(1,0),(2,0),(4,2)},
    {(1,0),(2,1),(3,2)},
    {(1,0),(3,0),(4,1)},
    {(1,1),(2,1),(4,0)},
    {(1,1),(2,2),(3,0)},
    {(1,1),(3,1),(4,2)},
    {(1,2),(2,0),(3,1)},
    {(1,2),(2,2),(4,1)},
    {(1,2),(3,2),(4,0)},
    {(2,0),(3,0),(4,0)},
    {(2,1),(3,1),(4,1)},
    {(2,2),(3,2),(4,2)}}

theorem baseBlocks_card : baseBlocks.card = 30 := by decide

/-- Small kernel-computed certificates avoid evaluating any classical
edge-set representation. -/
theorem baseBlocks_allowed : ∀T∈baseBlocks,
    IsAllowed (Rainbow.host 5 (Fin 3)) (Rainbow.types 5) T := by
  intro T hT
  simp only [baseBlocks,mem_insert,mem_singleton] at hT
  rcases hT with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals dsimp only [IsAllowed,Rainbow.host,Rainbow.types,Set.mem_setOf_eq]
  all_goals decide

theorem baseBlocks_pair_count (u v : Fin 5 × Fin 3) (h : u.1≠v.1) :
    (baseBlocks.filter (fun T => u∈T ∧ v∈T)).card=1 := by
  revert u v h
  decide

private theorem base_pair_unique (u v : Fin 5 × Fin 3) (h : u.1≠v.1)
    (T U : Finset (Fin 5 × Fin 3)) (hT : T∈baseBlocks) (hU : U∈baseBlocks)
    (huT : u∈T) (hvT : v∈T) (huU : u∈U) (hvU : v∈U) : T=U := by
  obtain ⟨Q,hQ⟩ := Finset.card_eq_one.mp (baseBlocks_pair_count u v h)
  have hTf : T∈baseBlocks.filter (fun S => u∈S ∧ v∈S) := mem_filter.mpr ⟨hT,huT,hvT⟩
  have hUf : U∈baseBlocks.filter (fun S => u∈S ∧ v∈S) := mem_filter.mpr ⟨hU,huU,hvU⟩
  rw [hQ,mem_singleton] at hTf hUf
  exact hTf.trans hUf.symm

private theorem base_pair_exists (u v : Fin 5 × Fin 3) (h : u.1≠v.1) :
    ∃T∈baseBlocks,u∈T ∧ v∈T := by
  have hpos : 0<(baseBlocks.filter (fun T => u∈T ∧ v∈T)).card := by
    rw [baseBlocks_pair_count u v h]
    decide
  obtain ⟨T,hT⟩ := Finset.card_pos.mp hpos
  exact ⟨T,(mem_filter.mp hT).1,(mem_filter.mp hT).2⟩

theorem baseBlocks_decomposition :
    IsDecomposition (Rainbow.host 5 (Fin 3)) (Rainbow.types 5)
      (edges (Rainbow.host 5 (Fin 3))) baseBlocks := by
  classical
  letI : DecidableEq (Fin 5 × Fin 3) := Classical.decEq _
  refine ⟨baseBlocks_allowed,?_,?_⟩
  · intro T hT U hU hTU
    apply Finset.disjoint_left.mpr
    intro e heT heU
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨huT,hvT,huv⟩ := mem_triEdges.mp heT
      obtain ⟨huU,hvU,_⟩ := mem_triEdges.mp heU
      have hcolors : u.1≠v.1 := (baseBlocks_allowed T hT).2.1 u huT v hvT huv
      exact hTU (base_pair_unique u v hcolors T U hT hU huT hvT huU hvU)
  · ext e
    induction e using Sym2.ind with
    | _ u v =>
      constructor
      · intro he
        obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
        obtain ⟨hu,hv,huv⟩ := mem_triEdges.mp heT
        have hadj := (baseBlocks_allowed T hT).2.1 u hu v hv huv
        exact mem_filter.mpr ⟨mem_univ _,(SimpleGraph.mem_edgeSet _).mpr hadj⟩
      · intro he
        have hadj : (Rainbow.host 5 (Fin 3)).G.Adj u v :=
          (SimpleGraph.mem_edgeSet _).mp (mem_filter.mp he).2
        have hcolors : u.1≠v.1 := hadj
        obtain ⟨T,hT,hu,hv⟩ := base_pair_exists u v hcolors
        have huv : u≠v := fun h => hcolors (congrArg Prod.fst h)
        exact mem_biUnion.mpr ⟨T,hT,mem_triEdges.mpr ⟨hu,hv,huv⟩⟩

theorem baseBlocks_physical :
    IsPhysical (Rainbow.host 5 (Fin 3)) (Rainbow.types 5)
      (edges (Rainbow.host 5 (Fin 3))) :=
  isPhysical_of_isDecomposition baseBlocks_decomposition

#print axioms baseBlocks_decomposition
#print axioms baseBlocks_physical
end TypedTriangle.Applications.FivePartite
