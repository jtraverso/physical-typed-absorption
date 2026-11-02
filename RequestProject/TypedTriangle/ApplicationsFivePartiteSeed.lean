module
public import RequestProject.TypedTriangle.ApplicationsRainbowNeighbors
public import RequestProject.TypedTriangle.SparseEdgeDefs
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Applications.FivePartite

variable {A : Type} [Fintype A]

local instance : DecidableEq (Fin 5 × A) := Classical.decEq _

private theorem remaining_colors (i j : Fin 5) (h : i≠j) :
    ((univ : Finset (Fin 5)).filter (fun c => c≠i ∧ c≠j)).card=3 := by
  revert i j h
  decide

def edgeThirds (u v : Fin 5 × A) : Finset (Fin 5 × A) :=
  univ.filter (fun w => w.1≠u.1 ∧ w.1≠v.1)

theorem edgeThirds_card (u v : Fin 5 × A) (h : u.1≠v.1) :
    (edgeThirds u v).card=3*Fintype.card A := by
  let C : Finset (Fin 5) := univ.filter (fun c => c≠u.1 ∧ c≠v.1)
  let e : (edgeThirds u v) ≃ (C × A) := {
    toFun := fun w => (⟨w.val.1,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp w.property).2⟩⟩,w.val.2)
    invFun := fun t => ⟨(t.1.val,t.2),mem_filter.mpr ⟨mem_univ _,(mem_filter.mp t.1.property).2⟩⟩
    left_inv := fun w => by apply Subtype.ext; rfl
    right_inv := fun t => by
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · rfl }
  calc
    (edgeThirds u v).card=Fintype.card (edgeThirds u v) := (Fintype.card_coe _).symm
    _ = Fintype.card (C × A) := Fintype.card_congr e
    _ = Fintype.card C*Fintype.card A := Fintype.card_prod C A
    _ = 3*Fintype.card A := by
      rw [Fintype.card_coe]
      exact congrArg (fun n => n*Fintype.card A) (remaining_colors u.1 v.1 h)

private theorem triple_change_decEq {V : Type} (u v w : V) (P : Finset V → Prop)
    (d₁ d₂ : DecidableEq V)
    (h : P (letI : DecidableEq V := d₁; ({u,v,w} : Finset V))) :
    P (letI : DecidableEq V := d₂; ({u,v,w} : Finset V)) := by
  cases Subsingleton.elim d₁ d₂
  exact h

/-- Every edge in the balanced five-partite graph has exactly three
whole parts of possible third vertices. -/
theorem edge_triangle_count (u v : Fin 5 × A) (h : u.1≠v.1) :
    ((allowed (Rainbow.host 5 A) (Rainbow.types 5)).filter
      (fun T => s(u,v)∈triEdges T)).card=3*Fintype.card A := by
  have huv : u≠v := fun e => h (congrArg Prod.fst e)
  have hBijection : (edgeThirds u v).card=
      ((allowed (Rainbow.host 5 A) (Rainbow.types 5)).filter
        (fun T => s(u,v)∈triEdges T)).card := by
    apply card_bij (fun w _ => ({u,v,w} : Finset (Fin 5 × A)))
    · intro w hw
      obtain ⟨hwu,hwv⟩ := (mem_filter.mp hw).2
      have hAllowed : IsAllowed (Rainbow.host 5 A) (Rainbow.types 5) {u,v,w} :=
        triple_change_decEq u v w (IsAllowed (Rainbow.host 5 A) (Rainbow.types 5))
          _ (inferInstance) (Rainbow.allowed_triangle u v w h hwu.symm hwv.symm)
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hAllowed⟩,?_⟩
      exact mem_triEdges.mpr ⟨by simp,by simp,huv⟩
    · intro w hw z hz hEq
      obtain ⟨hwu,hwv⟩ := (mem_filter.mp hw).2
      have hm : w∈({u,v,z} : Finset (Fin 5 × A)) := by rw [←hEq]; simp
      simp only [mem_insert,mem_singleton] at hm
      rcases hm with hm|hm|hm
      · exact False.elim (hwu (congrArg Prod.fst hm))
      · exact False.elim (hwv (congrArg Prod.fst hm))
      · exact hm
    · intro T hT
      obtain ⟨hTa,he⟩ := mem_filter.mp hT
      have hAllowed := (mem_filter.mp hTa).2
      obtain ⟨hu,hv,_⟩ := mem_triEdges.mp he
      obtain ⟨w,hwu,hwv,hEq⟩ := SparseEdge.eq_triple_of_mem hAllowed.1 hu hv huv
      have hwT : w∈T := by rw [hEq]; simp
      have hcwu : w.1≠u.1 := hAllowed.2.1 w hwT u hu hwu
      have hcwv : w.1≠v.1 := hAllowed.2.1 w hwT v hv hwv
      exact ⟨w,mem_filter.mpr ⟨mem_univ _,hcwu,hcwv⟩,hEq.symm⟩
  exact hBijection.symm.trans (edgeThirds_card u v h)

/-- The canonical fractional decomposition gives weight 1/(3n) to every
rainbow triangle, where n is the size of each part. -/
def uniformSeed (A : Type) [Fintype A] (_T : Finset (Fin 5 × A)) : ℝ :=
  1/(3*(Fintype.card A : ℝ))

theorem diffuse_uniformSeed (hA : 0<Fintype.card A) :
    IsDiffuseSeed (Rainbow.host 5 A) (Rainbow.types 5) (5/3) (uniformSeed A) := by
  have hn : (0 : ℝ)<Fintype.card A := Nat.cast_pos.mpr hA
  refine ⟨?_,?_⟩
  · intro T hT
    dsimp only [uniformSeed]
    rw [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    constructor
    · apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith
    · apply le_of_eq
      field_simp [ne_of_gt hn] <;> ring
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have h : u.1≠v.1 := (SimpleGraph.mem_edgeSet _).mp he
      change (∑ T∈((allowed (Rainbow.host 5 A) (Rainbow.types 5)).filter
        (fun T => s(u,v)∈triEdges T)),1/(3*(Fintype.card A : ℝ)))=1
      rw [sum_const,nsmul_eq_mul,edge_triangle_count u v h]
      push_cast
      field_simp [ne_of_gt hn]

#print axioms edge_triangle_count
#print axioms diffuse_uniformSeed
end TypedTriangle.Applications.FivePartite
