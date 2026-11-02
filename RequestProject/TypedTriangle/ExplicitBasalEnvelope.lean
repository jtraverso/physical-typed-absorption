module
public import RequestProject.TypedTriangle.BasalEnvelopeQuantitative
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false

namespace TypedTriangle.Envelope.Explicit
open SelSimul

def envelopeLoad (α : ℝ) : ℕ := ⌈4 / α⌉₊ + 1
def envelopeDegree (α : ℝ) : ℕ := 2 + 2 * envelopeLoad α
def envelopeBudget (α : ℝ) : ℝ := α / (64 * ((envelopeLoad α : ℝ) + 4))
def envelopeOrder (α : ℝ) : ℕ := ⌈32 * (envelopeLoad α : ℝ) / α⌉₊ + 1

theorem envelopeDegree_pos (α : ℝ) : 0 < envelopeDegree α := by unfold envelopeDegree; omega
theorem envelopeBudget_pos {α : ℝ} (hα : 0 < α) : 0 < envelopeBudget α := by
  unfold envelopeBudget
  positivity

theorem uniform_envelope_of_H3_explicit (α : ℝ) (hα : 0 < α)
    {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (hn : envelopeOrder α ≤ Fintype.card V) (hH3 : CommonNbrCond H F α)
    (E B : Finset (Sym2 V)) (Z : Finset V) (r b : ℕ)
    (hE : ∀ v, edeg E v ≤ r) (hB : ∀ v, edeg B v ≤ b)
    (hr : (r : ℝ) ≤ envelopeBudget α * Fintype.card V)
    (hb : (b : ℝ) ≤ envelopeBudget α * Fintype.card V)
    (hz : (Z.card : ℝ) ≤ envelopeBudget α * Fintype.card V)
    (htri : ∀ e ∈ E, HasTri H F e) :
    ∃ W : Finset (Sym2 V), Disjoint W (E ∪ B) ∧ Basal H F (E ∪ W) ∧
      ∀ v, edeg W v ≤ envelopeDegree α * (r + 1) := by
  let L := envelopeLoad α
  have hL : 0 < L := by dsimp [L, envelopeLoad]; omega
  have hαL : 4 ≤ α * L := by
    have hc : 4 / α ≤ (L : ℝ) := (Nat.le_ceil _).trans
      (by dsimp [L, envelopeLoad]; push_cast; linarith)
    have hd := (div_le_iff₀ hα).mp hc
    nlinarith
  have hceil : ⌈32 * (L : ℝ) / α⌉₊ ≤ Fintype.card V := by
    change ⌈32 * (L : ℝ) / α⌉₊ + 1 ≤ Fintype.card V at hn
    omega
  have hnR : 32 * (L : ℝ) / α ≤ Fintype.card V :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hn' : 32 * (L : ℝ) ≤ α * Fintype.card V := by
    have hh := (div_le_iff₀ hα).mp hnR
    nlinarith
  have hdiag : ∀ e ∈ E, ¬ e.IsDiag := by
    intro e he
    obtain ⟨T, hT, heT⟩ := htri e he
    exact (mem_filter.mp heT).2
  have hm := two_card_le_card_mul_degree E hdiag hE
  have hwin := sparse_window hα hL hαL hm hn' hr hb hz
  obtain ⟨W, hW, hbas, hWd⟩ := envelope_of_H3 hH3 E B Z
    (Nat.mul_pos hL (Nat.succ_pos r)) hE hB htri hwin
  refine ⟨W, hW, hbas, fun v => (hWd v).trans ?_⟩
  calc
    2 * (r + L * (r + 1)) ≤ 2 * ((r + 1) + L * (r + 1)) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.le_succ r) _)
    _ = envelopeDegree α * (r + 1) := by dsimp [envelopeDegree, L]; ring

#print axioms uniform_envelope_of_H3_explicit
end TypedTriangle.Envelope.Explicit
