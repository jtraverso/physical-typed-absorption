module
public import RequestProject.TypedTriangle.ApplicationsFivePartiteBase
public import RequestProject.TypedTriangle.SparseEdgeDefs
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Applications.FivePartite

variable {A : Type} [Fintype A] [AddCommGroup A]

abbrev Vertex (A : Type) := Fin 5 × (Fin 3 × A)

local instance : DecidableEq (Fin 5 × Fin 3) := Classical.decEq _
local instance : DecidableEq (Vertex A) := Classical.decEq _

def project (v : Vertex A) : Fin 5 × Fin 3 := (v.1,v.2.1)
def coordinate (v : Vertex A) : A := v.2.2

/-- A symmetric Latin blow-up of each of the thirty base blocks. -/
def blocks (A : Type) [Fintype A] [AddCommGroup A] : Finset (Finset (Vertex A)) :=
  univ.filter (fun T => IsAllowed (Rainbow.host 5 (Fin 3 × A)) (Rainbow.types 5) T ∧
    T.image project ∈ baseBlocks ∧ ∑ v ∈ T,coordinate v = 0)

private theorem allowed_of_colors (T : Finset (Vertex A)) (hcard : T.card=3)
    (hc : ∀u∈T,∀v∈T,u≠v → u.1≠v.1) :
    IsAllowed (Rainbow.host 5 (Fin 3 × A)) (Rainbow.types 5) T := by
  refine ⟨hcard,hc,?_⟩
  change (T.val.map Prod.fst).Nodup
  apply (Multiset.nodup_map_iff_inj_on T.nodup).2
  intro u hu v hv huv
  by_contra hne
  exact hc u hu v hv hne huv

private theorem allowed_triangle (u v w : Vertex A)
    (huv : u.1≠v.1) (huw : u.1≠w.1) (hvw : v.1≠w.1) :
    IsAllowed (Rainbow.host 5 (Fin 3 × A)) (Rainbow.types 5) {u,v,w} := by
  apply allowed_of_colors _
    (SparseEdge.card_three_of_distinct (fun h => huv (congrArg Prod.fst h))
      (fun h => huw (congrArg Prod.fst h)) (fun h => hvw (congrArg Prod.fst h)))
  intro x hx y hy hxy
  simp only [mem_insert,mem_singleton] at hx hy
  rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl
  all_goals first | exact False.elim (hxy rfl) | assumption | exact Ne.symm (by assumption)

private theorem project_ne {u v : Vertex A} (h : u.1≠v.1) : project u≠project v :=
  fun e => h (congrArg (fun t : Fin 5 × Fin 3 => t.1) e)

private theorem member_data {T : Finset (Vertex A)} (hT : T∈blocks A) :
    IsAllowed (Rainbow.host 5 (Fin 3 × A)) (Rainbow.types 5) T ∧
      T.image project ∈ baseBlocks ∧ ∑v∈T,coordinate v=0 :=
  (mem_filter.mp hT).2

/-- Each lifted edge lies in at most one of the displayed Latin triangles. -/
theorem block_unique {T U : Finset (Vertex A)} (hT : T∈blocks A) (hU : U∈blocks A)
    {u v : Vertex A} (huT : u∈T) (hvT : v∈T) (huU : u∈U) (hvU : v∈U)
    (huv : u≠v) : T=U := by
  obtain ⟨hTa,hTb,hTs⟩ := member_data hT
  obtain ⟨hUa,hUb,hUs⟩ := member_data hU
  have hcuv : u.1≠v.1 := hTa.2.1 u huT v hvT huv
  have hpT : s(project u,project v)∈triEdges (T.image project) :=
    mem_triEdges.mpr ⟨mem_image.mpr ⟨u,huT,rfl⟩,mem_image.mpr ⟨v,hvT,rfl⟩,project_ne hcuv⟩
  have hpU : s(project u,project v)∈triEdges (U.image project) :=
    mem_triEdges.mpr ⟨mem_image.mpr ⟨u,huU,rfl⟩,mem_image.mpr ⟨v,hvU,rfl⟩,project_ne hcuv⟩
  have hProj := baseBlocks_decomposition.unique hTb hUb hpT hpU
  obtain ⟨w,hwu,hwv,hTeq⟩ := SparseEdge.eq_triple_of_mem hTa.1 huT hvT huv
  obtain ⟨z,hzu,hzv,hUeq⟩ := SparseEdge.eq_triple_of_mem hUa.1 huU hvU huv
  have hwT : w∈T := by rw [hTeq]; simp
  have hzU : z∈U := by rw [hUeq]; simp
  have hwuc : w.1≠u.1 := hTa.2.1 w hwT u huT hwu
  have hwvc : w.1≠v.1 := hTa.2.1 w hwT v hvT hwv
  have hpw : project w∈U.image project := by rw [←hProj]; exact mem_image.mpr ⟨w,hwT,rfl⟩
  rw [hUeq] at hpw
  have hwpz : project w=project z := by
    simpa only [image_insert,image_singleton,mem_insert,mem_singleton,
      project_ne hwuc,project_ne hwvc,false_or] using hpw
  have hsumT : coordinate u+(coordinate v+coordinate w)=0 := by
    rw [hTeq] at hTs
    simpa [huv,Ne.symm hwu,Ne.symm hwv,add_assoc] using hTs
  have hsumU : coordinate u+(coordinate v+coordinate z)=0 := by
    rw [hUeq] at hUs
    simpa [huv,Ne.symm hzu,Ne.symm hzv,add_assoc] using hUs
  have hwz : w=z := by
    apply Prod.ext
    · exact congrArg (fun t : Fin 5 × Fin 3 => t.1) hwpz
    · apply Prod.ext
      · exact congrArg (fun t : Fin 5 × Fin 3 => t.2) hwpz
      · exact add_left_cancel (add_left_cancel (hsumT.trans hsumU.symm))
  rw [hTeq,hUeq,hwz]

/-- Every cross-part lifted edge has its unique third vertex. -/
theorem edge_has_block (u v : Vertex A) (huv : u.1≠v.1) :
    ∃T∈blocks A,s(u,v)∈triEdges T := by
  have hbEdge : s(project u,project v)∈edges (Rainbow.host 5 (Fin 3)) := by
    exact mem_filter.mpr ⟨mem_univ _,(SimpleGraph.mem_edgeSet _).mpr huv⟩
  obtain ⟨Q,hQ,hQedge⟩ := baseBlocks_decomposition.exists_mem hbEdge
  obtain ⟨huQ,hvQ,hpuv⟩ := mem_triEdges.mp hQedge
  have hQa := baseBlocks_decomposition.1 Q hQ
  obtain ⟨z,hzu,hzv,hQeq⟩ := SparseEdge.eq_triple_of_mem hQa.1 huQ hvQ hpuv
  have hzQ : z∈Q := by rw [hQeq]; simp
  have hzuc : z.1≠u.1 := hQa.2.1 z hzQ (project u) huQ hzu
  have hzvc : z.1≠v.1 := hQa.2.1 z hzQ (project v) hvQ hzv
  let w : Vertex A := (z.1,(z.2,-coordinate u-coordinate v))
  have huw : u.1≠w.1 := Ne.symm hzuc
  have hvw : v.1≠w.1 := Ne.symm hzvc
  have hwu : w≠u := fun h => huw (congrArg Prod.fst h).symm
  have hwv : w≠v := fun h => hvw (congrArg Prod.fst h).symm
  have huv' : u≠v := fun h => huv (congrArg Prod.fst h)
  refine ⟨{u,v,w},mem_filter.mpr ⟨mem_univ _,allowed_triangle u v w huv huw hvw,?_,?_⟩,
    mem_triEdges.mpr ⟨by simp,by simp,huv'⟩⟩
  · rw [hQeq] at hQ
    simpa only [image_insert,image_singleton,show project w=z from rfl] using hQ
  · rw [Finset.sum_insert (by simp [huv',Ne.symm hwu]),
      Finset.sum_insert (by simp [Ne.symm hwv]),Finset.sum_singleton]
    dsimp only [coordinate,w]
    abel

/-- The blow-up is an actual exact rainbow decomposition. -/
theorem decomposition :
    IsDecomposition (Rainbow.host 5 (Fin 3 × A)) (Rainbow.types 5)
      (edges (Rainbow.host 5 (Fin 3 × A))) (blocks A) := by
  refine ⟨fun T hT => (member_data hT).1,?_,?_⟩
  · intro T hT U hU hTU
    apply disjoint_left.mpr
    intro e heT heU
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨huT,hvT,huv⟩ := mem_triEdges.mp heT
      obtain ⟨huU,hvU,_⟩ := mem_triEdges.mp heU
      exact hTU (block_unique hT hU huT hvT huU hvU huv)
  · ext e
    induction e using Sym2.ind with
    | _ u v =>
      constructor
      · intro he
        obtain ⟨T,hT,he⟩ := mem_biUnion.mp he
        exact SparseEdge.triEdges_subset_edges (member_data hT).1 he
      · intro he
        have hAdj : (Rainbow.host 5 (Fin 3 × A)).G.Adj u v :=
          (SimpleGraph.mem_edgeSet _).mp (mem_filter.mp he).2
        have huv : u.1≠v.1 := hAdj
        obtain ⟨T,hT,heT⟩ := edge_has_block u v huv
        exact mem_biUnion.mpr ⟨T,hT,heT⟩

theorem physical :
    IsPhysical (Rainbow.host 5 (Fin 3 × A)) (Rainbow.types 5)
      (edges (Rainbow.host 5 (Fin 3 × A))) :=
  isPhysical_of_isDecomposition decomposition

theorem cyclic_part_card (m : ℕ) [NeZero m] :
    Fintype.card (Fin 3 × ZMod m)=3*m := by
  simp only [Fintype.card_prod,Fintype.card_fin,ZMod.card]

theorem physical_cyclic (m : ℕ) [NeZero m] :
    IsPhysical (Rainbow.host 5 (Fin 3 × ZMod m)) (Rainbow.types 5)
      (edges (Rainbow.host 5 (Fin 3 × ZMod m))) := physical

#print axioms decomposition
#print axioms physical
end TypedTriangle.Applications.FivePartite
