module
public import RequestProject.TypedTriangle.ApplicationsRainbowDefs
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Examples.RainbowRetention
open TypedTriangle.Applications

abbrev Vertex (A : Type) := Fin 5 × A

local instance {A : Type} : DecidableEq (Vertex A) := Classical.decEq _

/-- The edges among the original four parts, inside the five-part host. -/
def oldEdges (A : Type) [Fintype A] : Finset (Sym2 (Vertex A)) :=
  (edges (Rainbow.host 5 A)).filter (fun e => ∀ v∈e,v.1≠(4 : Fin 5))

/-- Adding a fifth nonempty part cannot preserve every triangle of an
exact decomposition on the first four parts. The new edges must be
covered using some of the already covered old edges. -/
theorem cannot_retain_old_decomposition {A : Type} [Fintype A] [Nonempty A]
    (Dold Dfull : Finset (Finset (Vertex A)))
    (hOld : IsDecomposition (Rainbow.host 5 A) (Rainbow.types 5) (oldEdges A) Dold)
    (hFull : IsDecomposition (Rainbow.host 5 A) (Rainbow.types 5)
      (edges (Rainbow.host 5 A)) Dfull) : ¬Dold⊆Dfull := by
  intro hRetain
  let a : A := Classical.choice inferInstance
  let p : Vertex A := (0,a)
  let q : Vertex A := (4,a)
  have hpq : p≠q := by simp [p,q]
  have hNew : s(p,q)∈edges (Rainbow.host 5 A) := by
    simp [edges,Rainbow.host,p,q]
  obtain ⟨T,hT,v,hp,hq,hv,hvp,hvq,hpv,_⟩ := hFull.third hNew
  have hvOld : v.1≠(4 : Fin 5) := by
    have ha := (hFull.1 T hT).2.1 v hv q hq hvq
    change v.1≠(4 : Fin 5) at ha
    exact ha
  have hpOld : p.1≠(4 : Fin 5) := by simp [p]
  have hOldEdge : s(p,v)∈oldEdges A := by
    apply mem_filter.mpr
    refine ⟨hpv,?_⟩
    intro z hz
    rcases Sym2.mem_iff.mp hz with rfl|rfl
    · exact hpOld
    · exact hvOld
  obtain ⟨Q,hQ,hOldQ⟩ := hOld.exists_mem hOldEdge
  have hOldT : s(p,v)∈triEdges T :=
    mem_triEdges.mpr ⟨hp,hv,Ne.symm hvp⟩
  have hTQ : T=Q := hFull.unique hT (hRetain hQ) hOldT hOldQ
  have hNewT : s(p,q)∈triEdges T := mem_triEdges.mpr ⟨hp,hq,hpq⟩
  have hNewOld : s(p,q)∈oldEdges A :=
    hOld.subset hQ (by simpa only [hTQ] using hNewT)
  have hForbidden := (mem_filter.mp hNewOld).2 q (Sym2.mem_mk_right p q)
  exact hForbidden rfl

#print axioms cannot_retain_old_decomposition
end TypedTriangle.Examples.RainbowRetention
