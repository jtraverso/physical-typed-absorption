module
public import RequestProject.TypedTriangle.ExplicitPreparedAbsorberSupply
public import RequestProject.TypedTriangle.ExplicitTerminalPlacement
public import RequestProject.TypedTriangle.VortexUniformTerminalReserve
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.PreparedSupply.Explicit

def reserveSize (α : ℝ) (h t : ℕ) : ℕ := supplySize α h (t*t) * 2^(t*t)
def reserveBudget (α β : ℝ) (h t : ℕ) : ℝ :=
  S07V31.terminalBudget t (supplySize α h (t*t)) (supplyBudget α β h)
def reserveOrder (α β : ℝ) (h t : ℕ) : ℕ :=
  max (supplyOrder α h (t*t))
    (S07V31.terminalOrder t (supplySize α h (t*t)) (supplyBudget α β h))
def outerRate (α β : ℝ) (h t : ℕ) : ℝ := min (1/64) (reserveBudget α β h t / 4)
theorem reserveBudget_pos (h t : ℕ) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    0 < reserveBudget α β h t :=
  S07V31.terminalBudget_pos t _ (supplyBudget_pos h hα hβ)

theorem terminal_absorber_on_prepared_host_explicit (α β : ℝ) (h t : ℕ)
    (hα : 0 < α) (hβ : 0 < β) :
    let ε := reserveBudget α β h t
    let K := reserveSize α h t
    let N := absorberOrder α h
    let n₀ := reserveOrder α β h t
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V →
        Dispersal.PreparedCore H.G H.lab F α h N β →
        ∀ (U : Finset V) (B : Finset (Sym2 V)) (b : ℕ),
          U.card ≤ t → (∀ v, degIn B v ≤ b) →
          (b : ℝ) ≤ ε * Fintype.card V →
          ∃ R : Finset (Sym2 V),
            Disjoint R B ∧ Disjoint R (triEdges U) ∧ R.card ≤ K ∧
            (∀ v, degIn R v ≤ K) ∧ Basal H F R ∧
            ∀ L : Finset (Sym2 V), IsPhysical H F L → support L ⊆ U →
              Basal H F (R ∪ L) := by
  dsimp only
  let s := supplySize α h (t*t)
  let δ := supplyBudget α β h
  have hδ : 0 < δ := supplyBudget_pos h hα hβ
  intro V I _ H F hn Pc U B b hU hB hb
  have hsup : S07V31.TerminalSupply H.G H.lab F U s
      ⌊δ * Fintype.card V⌋₊ ⌊δ * Fintype.card V⌋₊ := by
    intro P hP _
    obtain ⟨hPE,hPhys⟩ := S07V31.mem_physSubsets.mp hP
    have hCard : P.card ≤ t*t :=
      (card_le_card hPE).trans ((S07V31.card_triEdges_le U).trans
        (Nat.mul_le_mul hU hU))
    exact prepared_uniform_supply_explicit α h (t*t) hα β hβ H F
      ((le_max_left _ _).trans hn) Pc P hCard hPhys
  exact S07V31.universal_terminal_absorber_explicit t s hδ H.G H.lab F U B b ((le_max_right _ _).trans hn) hU hB hb hsup

theorem terminal_absorber_avoiding_outer_core_explicit (α β : ℝ) (h t : ℕ)
    (hα : 0 < α) (hβ : 0 < β) :
    let q := outerRate α β h t
    let K := reserveSize α h t
    let N := absorberOrder α h
    let n₀ := reserveOrder α β h t
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V →
        Dispersal.PreparedCore H.G H.lab F α h N β →
        ∀ W U : Finset V, (W.card : ℝ) ≤ 2*q*Fintype.card V →
          U.card ≤ t →
          ∃ R : Finset (Sym2 V), Disjoint R (triEdges W) ∧
            R.card ≤ K ∧ (∀ v, degIn R v ≤ K) ∧ Basal H F R ∧
            ∀ L : Finset (Sym2 V), IsPhysical H F L → support L ⊆ U →
              Basal H F (R ∪ L) := by
  dsimp only
  let ε := reserveBudget α β h t
  have hε : 0 < ε := reserveBudget_pos h t hα hβ
  let q := min (1/64) (ε/4)
  have hq : 0 < q := lt_min (by norm_num) (by positivity)
  have hqSmall : q ≤ 1/32 := (min_le_left _ _).trans (by norm_num)
  have hBudget : 2*q ≤ ε := by
    have h := min_le_right (1/64 : ℝ) (ε/4)
    dsimp only [q]
    linarith
  intro V I _ H F hn Pc W U hW hU
  change (W.card : ℝ) ≤ 2*q*Fintype.card V at hW
  have hBcap : (W.card : ℝ) ≤ ε*Fintype.card V :=
    hW.trans (by
      have h := mul_le_mul_of_nonneg_right hBudget
        (show (0 : ℝ) ≤ Fintype.card V by positivity)
      nlinarith)
  obtain ⟨R,hAvoid,-,hCard,hDeg,hBasal,hAbsorb⟩ :=
    terminal_absorber_on_prepared_host_explicit α β h t hα hβ H F hn Pc U (triEdges W) W.card hU
      (fun v => S07V31.degIn_triEdges_le W v) hBcap
  exact ⟨R,hAvoid,hCard,hDeg,hBasal,hAbsorb⟩
#print axioms terminal_absorber_on_prepared_host_explicit
#print axioms terminal_absorber_avoiding_outer_core_explicit
end TypedTriangle.PreparedSupply.Explicit
