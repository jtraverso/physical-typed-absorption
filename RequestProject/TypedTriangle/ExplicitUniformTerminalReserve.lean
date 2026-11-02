module
public import RequestProject.TypedTriangle.ExplicitPreparedTerminalReserve
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.PreparedSupply.Explicit

def uniformOuterRate (α : ℝ) (h t L : ℕ) (β : Fin (L+1) → ℝ) : ℝ :=
  (univ : Finset (Fin (L+1))).inf' ⟨0, mem_univ _⟩ (fun r => outerRate α (β r) h t)

def uniformReserveOrder (α : ℝ) (h t L : ℕ) (β : Fin (L+1) → ℝ) : ℕ :=
  (univ : Finset (Fin (L+1))).sup (fun r => reserveOrder α (β r) h t)

theorem uniformOuterRate_pos (α : ℝ) (h t L : ℕ) (β : Fin (L+1) → ℝ)
    (hα : 0 < α) (hβ : ∀ r, 0 < β r) : 0 < uniformOuterRate α h t L β := by
  apply (lt_inf'_iff _).mpr
  intro r _
  exact lt_min (by norm_num) (by exact div_pos (reserveBudget_pos h t hα (hβ r)) (by norm_num))

theorem uniformOuterRate_le (α : ℝ) (h t L : ℕ) (β : Fin (L+1) → ℝ)
    (r : Fin (L+1)) : uniformOuterRate α h t L β ≤ outerRate α (β r) h t :=
  inf'_le _ (mem_univ r)

theorem uniformOuterRate_small (α : ℝ) (h t L : ℕ) (β : Fin (L+1) → ℝ) :
    uniformOuterRate α h t L β ≤ 1/32 :=
  (uniformOuterRate_le α h t L β 0).trans ((min_le_left _ _).trans (by norm_num))

/-- A fixed finite minimum of rates and maximum of thresholds handles every
    intrinsic index, with no numerical witness selected from an existence theorem. -/
theorem uniform_terminal_absorber_explicit (α : ℝ) (h t L : ℕ) (β : Fin (L+1) → ℝ)
    (hα : 0 < α) (hβ : ∀ r, 0 < β r)
    {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (hn : uniformReserveOrder α h t L β ≤ Fintype.card V) (r : Fin (L+1))
    (Pc : Dispersal.PreparedCore H.G H.lab F α h (absorberOrder α h) (β r))
    (W U : Finset V)
    (hW : (W.card : ℝ) ≤ 2 * uniformOuterRate α h t L β * Fintype.card V)
    (hU : U.card ≤ t) :
    ∃ R : Finset (Sym2 V), Disjoint R (triEdges W) ∧
      R.card ≤ reserveSize α h t ∧ (∀ v, degIn R v ≤ reserveSize α h t) ∧ Basal H F R ∧
      ∀ M : Finset (Sym2 V), IsPhysical H F M → support M ⊆ U → Basal H F (R ∪ M) := by
  have hnr : reserveOrder α (β r) h t ≤ Fintype.card V :=
    (le_sup (f := fun r => reserveOrder α (β r) h t) (mem_univ r)).trans hn
  apply terminal_absorber_avoiding_outer_core_explicit α (β r) h t hα (hβ r) H F hnr Pc W U
  · exact hW.trans (by gcongr; exact uniformOuterRate_le α h t L β r)
  · exact hU

#print axioms uniformOuterRate_pos
#print axioms uniform_terminal_absorber_explicit
end TypedTriangle.PreparedSupply.Explicit
