module
public import RequestProject.TypedTriangle.Absorb
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Octahedron

def core : Finset (Sym2 (Fin 6)) :=
  {s(0,5),s(4,1),s(4,5),s(4,2),s(4,3),s(5,2),s(5,3)}

def mode (a b : Fin 6) : Finset (Finset (Fin 6)) :=
  {{0,5,a},{4,1,a},{4,5,b}}

theorem mode_cover (a b : Fin 6) (hab : (a=2 ∧ b=3) ∨ (a=3 ∧ b=2)) :
    (mode a b).biUnion triEdges = core ∪ wedge 0 1 a := by
  rcases hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      fin_cases x <;> fin_cases y <;>
        simp [mode,mem_biUnion,core,wedge,mem_triEdges,Sym2.eq_iff]

theorem mode_pairwise (a b : Fin 6) (hab : (a=2 ∧ b=3) ∨ (a=3 ∧ b=2)) :
    (mode a b : Set (Finset (Fin 6))).PairwiseDisjoint triEdges := by
  intro T hT U hU hTU
  simp only [mode,mem_coe,mem_insert,mem_singleton] at hT hU
  rcases hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    rcases hT with rfl | rfl | rfl <;>
    rcases hU with rfl | rfl | rfl
  all_goals first | exact (hTU rfl).elim | skip
  all_goals
    apply disjoint_left.mpr
    intro e he he'
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨hx,hy,hxy⟩ := mem_triEdges.mp he
      obtain ⟨hx',hy',_⟩ := mem_triEdges.mp he'
      simp only [mem_insert,mem_singleton] at hx hy hx' hy'
      rcases hx with rfl | rfl | rfl <;>
        rcases hy with rfl | rfl | rfl <;> simp_all

theorem core_avoids : Disjoint core (triEdges {0,1,2} ∪ triEdges {0,1,3}) := by
  apply disjoint_left.mpr
  intro e he he'
  induction e using Sym2.ind with
  | _ x y =>
    fin_cases x <;> fin_cases y <;>
      simp [core,mem_triEdges,Sym2.eq_iff] at he he'

theorem core_support : support core = univ := by
  ext x
  fin_cases x <;> simp [support,core]

theorem mode_card_three (a b : Fin 6) (hab : (a=2 ∧ b=3) ∨ (a=3 ∧ b=2))
    (T : Finset (Fin 6)) (hT : T∈mode a b) : T.card=3 := by
  simp only [mode,mem_insert,mem_singleton] at hT
  rcases hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    rcases hT with rfl | rfl | rfl <;> decide

#print axioms mode_cover
#print axioms mode_pairwise
#print axioms core_avoids
#print axioms core_support
end TypedTriangle.Applications.Octahedron
