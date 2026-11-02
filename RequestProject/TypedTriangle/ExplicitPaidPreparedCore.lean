/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExplicitSparseEdgePayment
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace TypedTriangle.Vortex.ExplicitPaid

def paidBudget (α : ℝ) (h : ℕ) : ℝ := min (geometryBudget α h / 2) (latticeBudget α h / 2)
def paidOrder (α : ℝ) (h : ℕ) : ℕ := max (geometryOrder α h) (latticeOrder α)

theorem paidBudget_pos {α : ℝ} (h : ℕ) (hα : 0 < α) : 0 < paidBudget α h := by
  have hG := geometryBudget_pos h hα
  have hL := latticeBudget_pos h hα
  unfold paidBudget
  positivity

theorem paid_lattice_persist_explicit (α : ℝ) (h : ℕ)
    (hα : 0 < α) :
      ∀ (V I : Type) [Fintype V] (H : Host V I) (F : Set (Multiset I))
        (β : ℝ),
        β ≤ 1 / 2 →
        latticeOrder α ≤ Fintype.card V →
        CommonNbrCond H F α → HingeCond H F α h →
        Dispersal.PreparedCore H.G H.lab F α h (latticeOrder α) β →
        ∀ B : Finset (Sym2 V),
          (∀ x, (((B.filter (fun e => x ∈ e)).card : ℕ) : ℝ) ≤
            latticeBudget α h / 2 * Fintype.card V) →
          ∀ Z : Finset V, (Z.card : ℝ) ≤ β * Fintype.card V →
            ∀ y ∈ lattice (subHost H (edges H \ B)) F,
              (∀ e : Sym2 V, (∃ z ∈ Z, z ∈ e) → y e = 0) →
                Dispersal.restr Z y ∈ lattice
                  (restrictedHost (subHost H (edges H \ B)) Z) F := by
  let η := latticeBudget α h
  have hη := latticeBudget_pos h hα
  have hSparse := sparse_edge_deletion_host_explicit α h hα
  intro V I _ H F β hβ hn h3 h4 P B hB Z hZ y hy hvan
  have hRawDeg : ∀ x,
      (((B.filter (fun e => x ∈ e)).card : ℕ) : ℝ) ≤ η * Fintype.card V := by
    intro x
    have hx := hB x
    have hn0 : (0 : ℝ) ≤ Fintype.card V := by positivity
    nlinarith
  have hFull := hSparse V I H F hn h3 h4 B hRawDeg
  have hRestricted : ∀ Z' : Finset V,
      (Z'.card : ℝ) ≤ β * Fintype.card V →
      ∀ z : Sym2 (Survivors Z') → ℤ,
        z ∈ lattice (subHost (restrictedHost H Z')
            (edges (restrictedHost H Z') \ restrictEdgeSet Z' B)) F ↔
          z ∈ lattice (restrictedHost H Z') F ∧
            ∀ e ∈ restrictEdgeSet Z' B, z e = 0 := by
    intro Z' hZ' z
    letI : DecidableEq (Survivors Z') := Classical.decEq _
    have hCard : (Fintype.card (Survivors Z') : ℝ) + Z'.card = Fintype.card V := by
      exact_mod_cast card_survivors_add_card Z'
    have hn0 : (0 : ℝ) ≤ Fintype.card V := by positivity
    have hZN : (Z'.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 := by
      have hmul := mul_le_mul_of_nonneg_right hβ hn0
      nlinarith
    have hHalf : (Fintype.card V : ℝ) / 2 ≤ Fintype.card (Survivors Z') := by
      linarith
    convert hSparse (Survivors Z') I (restrictedHost H Z') F
      (P.order Z' hZ') (P.h3 Z' hZ') (P.h4 Z' hZ') (restrictEdgeSet Z' B)
      (by
        intro x
        have hprod : 0 ≤ η * ((Fintype.card (Survivors Z') : ℝ) - Fintype.card V / 2) :=
          mul_nonneg hη.le (sub_nonneg.mpr hHalf)
        calc
          _ ≤ ((B.filter (fun e => x.1 ∈ e)).card : ℝ) := by
            norm_cast
            apply Finset.card_le_card_of_injOn (Sym2.map Subtype.val)
            · intro e he
              obtain ⟨heB, hxe⟩ := Finset.mem_filter.mp he
              exact Finset.mem_filter.mpr ⟨(mem_restrictEdgeSet Z' B e).mp heB,
                Sym2.mem_map.mpr ⟨x, hxe, rfl⟩⟩
            · exact (Sym2.map.injective Subtype.val_injective).injOn
          _ ≤ latticeBudget α h / 2 * Fintype.card V := hB x.1
          _ ≤ η * Fintype.card (Survivors Z') := by nlinarith) z using 1
    constructor <;> intro hz <;> convert hz using 1 <;>
      (congr 2 <;> apply Finset.ext <;> intro e <;> simp only [Finset.mem_sdiff])
  exact paid_lattice_persist_of_sparse_contracts H F B α h (latticeOrder α) β P hFull
    hRestricted Z hZ y hy hvan


theorem paid_prepared_core_explicit (α : ℝ) (h : ℕ)
    (hα : 0 < α) (hh : 6 ≤ h) :
      ∀ {V I : Type} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)) (β : ℝ),
        0 < β → β ≤ 1/2 →
        Dispersal.PreparedCore H.G H.lab F α h (paidOrder α h) β →
        CommonNbrCond H F α → HingeCond H F α h →
        ∀ (B : Finset (Sym2 V)) (d : ℕ), B ⊆ edges H →
          (∀ v, SparseEdge.degIn B v ≤ d) →
          (d : ℝ) ≤ paidBudget α h * Fintype.card V →
          Dispersal.PreparedCore
            (subHost H (edges H \ B)).G (subHost H (edges H \ B)).lab F
            (min (α/2) (S07V49.hingeConstB α 1 h)) (2*h-3) (paidOrder α h) β := by
  let ηG := geometryBudget α h
  let ηL := latticeBudget α h
  let nG := geometryOrder α h
  let nL := latticeOrder α
  have hηG := geometryBudget_pos h hα
  have hLat := paid_lattice_persist_explicit α h hα
  intro V I _ H F β hβ hβhalf P hRaw3 hRaw4 B d hBE hDeg hSmall
  have hN : nG ≤ max nG nL := le_max_left _ _
  have hnL : nL ≤ Fintype.card V := by
    have hzero : (0 : ℝ) ≤ β * Fintype.card V := by positivity
    have ho := P.order ∅ (by simpa using hzero)
    have hcard : Fintype.card (Survivors (∅ : Finset V)) = Fintype.card V := by
      have hc := card_survivors_add_card (∅ : Finset V)
      simpa using hc
    exact (le_max_right _ _).trans (hcard ▸ ho)
  let Psmall : Dispersal.PreparedCore H.G H.lab F α h nL β :=
    { h3 := P.h3, h4 := P.h4,
      order := fun Z hZ => (le_max_right _ _).trans (P.order Z hZ),
      lattice_persist := P.lattice_persist }
  have hn0 : (0 : ℝ) ≤ Fintype.card V := by positivity
  have hGsmall : (d : ℝ) ≤ ηG / 2 * Fintype.card V :=
    hSmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0)
  have hLsmall : (d : ℝ) ≤ ηL / 2 * Fintype.card V :=
    hSmall.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hn0)
  have hB : ∀ x, (((B.filter (fun e => x ∈ e)).card : ℕ) : ℝ) ≤
      ηL / 2 * Fintype.card V := by
    intro x
    have hDx := hDeg x
    have hC : ((B.filter (fun e => x ∈ e)).card : ℝ) ≤ d := by
      unfold SparseEdge.degIn at hDx
      exact_mod_cast hDx
    exact hC.trans hLsmall
  have hPersist := hLat V I H F β hβhalf hnL hRaw3 hRaw4 Psmall B hB
  refine paid_prepared_core_of_lattice H F α β ηG h (max nG nL) nG d
    P hβhalf hηG hN ?_ B hBE hDeg hGsmall hPersist
  intro U J _ R F' B' d' hn' h3' h4' hBE' hDeg' hSmall'
  exact geometry_after_edge_payment_explicit α h hα hh R F' B' d'
    hn' h3' h4' hBE' hDeg' hSmall' 


theorem paid_prepared_core_with_required_order_explicit (α : ℝ) (h : ℕ)
    (hα : 0 < α) (hh : 6 ≤ h) :
      ∀ {V I : Type} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)) (Nreq : ℕ) (β : ℝ),
        0 < β → β ≤ 1 / 2 →
        Dispersal.PreparedCore H.G H.lab F α h (max (paidOrder α h) Nreq) β →
        CommonNbrCond H F α → HingeCond H F α h →
        ∀ (B : Finset (Sym2 V)) (d : ℕ), B ⊆ edges H →
          (∀ v, SparseEdge.degIn B v ≤ d) →
          (d : ℝ) ≤ paidBudget α h * Fintype.card V →
          Dispersal.PreparedCore
            (subHost H (edges H \ B)).G (subHost H (edges H \ B)).lab F
            (min (α / 2) (S07V49.hingeConstB α 1 h)) (2 * h - 3)
            (max (paidOrder α h) Nreq) β := by
  intro V I _ H F Nreq β hβ hβhalf P h3 h4 B d hBE hDeg hSmall
  have Pbase : Dispersal.PreparedCore H.G H.lab F α h (paidOrder α h) β :=
    { h3 := P.h3
      h4 := P.h4
      order := fun Z hZ => (le_max_left (paidOrder α h) Nreq).trans (P.order Z hZ)
      lattice_persist := P.lattice_persist }
  have Qbase := paid_prepared_core_explicit α h hα hh H F β hβ hβhalf Pbase h3 h4 B d hBE hDeg hSmall
  exact
    { h3 := Qbase.h3
      h4 := Qbase.h4
      order := P.order
      lattice_persist := Qbase.lattice_persist }


#print axioms paid_lattice_persist_explicit
#print axioms paid_prepared_core_explicit
#print axioms paid_prepared_core_with_required_order_explicit
end TypedTriangle.Vortex.ExplicitPaid
