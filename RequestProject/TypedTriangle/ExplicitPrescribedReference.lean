/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExplicitDenseReference
public import RequestProject.TypedTriangle.ExplicitBasalEnvelope
public import RequestProject.TypedTriangle.VortexPrescribedEdgeReference
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.RawReference.Explicit

def prescribedBudget (a b α : ℝ) (h : ℕ) : ℝ :=
  min (Envelope.Explicit.envelopeBudget α)
    (stockBudget a b α h / (2*((Envelope.Explicit.envelopeDegree α : ℝ)+1)))
def prescribedLoadTolerance (η : ℝ) : ℝ := min (referenceLoadTolerance η) (1/2)
def prescribedAvoidBudget (a b α η : ℝ) : ℝ :=
  min (referenceAvoidBudget a b η) (Envelope.Explicit.envelopeBudget α)
def prescribedOrder (a b α : ℝ) (h : ℕ) (η : ℝ) : ℕ :=
  max (Envelope.Explicit.envelopeOrder α) (max (referenceOrder a b η)
    ⌈2*(Envelope.Explicit.envelopeDegree α : ℝ)/stockBudget a b α h⌉₊)

theorem prescribedBudget_pos {a b α : ℝ} (h : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α) : 0 < prescribedBudget a b α h :=
  lt_min (Envelope.Explicit.envelopeBudget_pos hα)
    (div_pos (stockBudget_pos h ha hab hα) (by positivity))

theorem prescribedLoadTolerance_pos {η : ℝ} (hη : 0 < η) :
    0 < prescribedLoadTolerance η := lt_min (referenceLoadTolerance_pos hη) (by norm_num)

theorem prescribedAvoidBudget_pos {a b α η : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α) (hη : 0 < η) :
    0 < prescribedAvoidBudget a b α η :=
  lt_min (referenceAvoidBudget_pos ha hab hη) (Envelope.Explicit.envelopeBudget_pos hα)

private theorem hasTri_of_approximate_load {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (μ : Finset V → ℝ)
    (ε : ℝ) (hε : ε < 1)
    (hLoad : ∀ e ∈ edges H, |bdry H F μ e - 1| ≤ ε) :
    ∀ e ∈ edges H, HasTri H F e := by
  intro e he
  by_contra hNo
  have hZero : bdry H F μ e = 0 := by
    unfold bdry
    apply Finset.sum_eq_zero
    intro T hT
    have hAllowed : IsAllowed H F T := by simpa [allowed] using hT
    have hMissing : e ∉ triEdges T := fun heT => hNo ⟨T,hAllowed,heT⟩
    simp only [indR, if_neg hMissing, mul_zero]
  have hBound := hLoad e he
  rw [hZero] at hBound
  norm_num at hBound
  linarith

theorem dense_reference_containing_sparse_edges_with_stock_explicit {I : Type}
    (F : Set (Multiset I)) (a b α : ℝ) (h : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α) :
    ∀ η : ℝ, 0 < η →
        ∀ {V : Type} [Fintype V] (H : Host V I) (μ : Finset V → ℝ)
          (E B : Finset (Sym2 V)) (dE dB : ℕ),
          prescribedOrder a b α h η ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
          (∀ T, IsAllowed H F T →
            a / Fintype.card V ≤ μ T ∧ μ T ≤ b / Fintype.card V) →
          (∀ e ∈ edges H, |bdry H F μ e - 1| ≤ prescribedLoadTolerance η) →
          E ⊆ edges H → Disjoint E B →
          (∀ v, degIn E v ≤ dE) → (dE : ℝ) ≤ prescribedBudget a b α h * Fintype.card V →
          (∀ v, degIn B v ≤ dB) → (dB : ℝ) ≤ prescribedAvoidBudget a b α η * Fintype.card V →
          ∃ (W : Finset (Sym2 V)) (DS : Finset (Finset V))
            (E₀ : Finset (Sym2 V)) (D₀ : Finset (Finset V)),
            Disjoint W (E ∪ B) ∧ IsDecomposition H F (E ∪ W) DS ∧
            (E ∪ W) ⊆ E₀ ∧ DS ⊆ D₀ ∧ E₀ ⊆ edges H ∧ IsDecomposition H F E₀ D₀ ∧
            Disjoint E₀ B ∧
            (∀ v,(degIn (edges H \ E₀) v : ℝ) ≤ η * Fintype.card V) ∧
            ∀ v,degIn W v ≤ Envelope.Explicit.envelopeDegree α * (dE+1) := by
  let c := Envelope.Explicit.envelopeDegree α
  let nEnv := Envelope.Explicit.envelopeOrder α
  let θ := stockBudget a b α h
  have hθ := stockBudget_pos h ha hab hα
  let ρ := prescribedBudget a b α h
  intro η hη
  let nRef := referenceOrder a b η
  let ε := prescribedLoadTolerance η
  intro V _ H μ E B dE dB hn h3 h4 hWeights hLoad hE hEB hEdeg hEcap hBdeg hBcap
  have hnEnv : nEnv ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnRef : nRef ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnRound : ⌈2 * (c : ℝ) / θ⌉₊ ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hTri := hasTri_of_approximate_load H F μ ε
    ((min_le_right _ _).trans_lt (by norm_num)) hLoad
  obtain ⟨W,hW,hBasal,hWdeg⟩ := Envelope.Explicit.uniform_envelope_of_H3_explicit α hα H F hnEnv h3 E B ∅ dE dB
    (by intro v; simpa only [SelSimul.edeg,degIn] using hEdeg v)
    (by intro v; simpa only [SelSimul.edeg,degIn] using hBdeg v)
    (hEcap.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)))
    (hBcap.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)))
    (by
      simp only [card_empty,Nat.cast_zero]
      exact mul_nonneg (Envelope.Explicit.envelopeBudget_pos hα).le (Nat.cast_nonneg _))
    (fun e he => hTri e (hE he))
  obtain ⟨DS,hDS⟩ := hBasal
  let S := E ∪ W
  let dS := dE + c * (dE + 1)
  have hS : S ⊆ edges H := by
    intro e he
    obtain ⟨T,hT,heT⟩ := hDS.exists_mem he
    exact triEdges_subset_edges (hDS.1 T hT) heT
  have hSB : Disjoint S B :=
    disjoint_union_left.mpr ⟨hEB,hW.mono_right subset_union_right⟩
  have hSdeg : ∀ v, degIn S v ≤ dS := by
    intro v
    have hUnion := SelSimul.edeg_union_le E W v
    have hWing := hWdeg v
    simpa only [S,dS,SelSimul.edeg,degIn] using
      hUnion.trans (Nat.add_le_add (hEdeg v) hWing)
  have hRound : (c : ℝ) ≤ θ / 2 * Fintype.card V := by
    have hnReal : (⌈2 * (c : ℝ) / θ⌉₊ : ℝ) ≤ Fintype.card V := by
      exact_mod_cast hnRound
    have hCeil := (Nat.le_ceil (2 * (c : ℝ) / θ)).trans hnReal
    have hMul := (div_le_iff₀ hθ).mp hCeil
    nlinarith
  have hCoef : ((c : ℝ) + 1) * ρ ≤ θ / 2 := by
    have hUpper : ρ ≤ θ / (2 * ((c : ℝ) + 1)) := min_le_right _ _
    have hMul := (le_div_iff₀ (by positivity : 0 < 2 * ((c : ℝ) + 1))).mp hUpper
    nlinarith
  have hScap : (dS : ℝ) ≤ θ * Fintype.card V := by
    have hScale := mul_le_mul_of_nonneg_right hCoef
      (show (0 : ℝ) ≤ Fintype.card V by positivity)
    have hDE := mul_le_mul_of_nonneg_left hEcap
      (show (0 : ℝ) ≤ (c : ℝ) + 1 by positivity)
    dsimp only [dS]
    push_cast
    nlinarith
  obtain ⟨E₀,D₀,hSE,hE₀,hDec,hDSsub,hAvoid,hHole⟩ :=
    dense_reference_containing_stock_explicit F a b α h ha hab hα η hη H μ S B DS dS dB hnRef h4 hWeights
      (fun e he => (hLoad e he).trans (min_le_left _ _)) hS hDS hSB hSdeg hScap hBdeg
      (hBcap.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)))
  refine ⟨W,DS,E₀,D₀,hW,hDS,hSE,hDSsub,hE₀,hDec,hAvoid,hHole,?_⟩
  intro v
  simpa only [c,SelSimul.edeg,degIn] using hWdeg v


theorem dense_reference_containing_sparse_edges_explicit {I : Type}
    (F : Set (Multiset I)) (a b α : ℝ) (h : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α) :
    ∀ η : ℝ, 0 < η →
        ∀ {V : Type} [Fintype V] (H : Host V I) (μ : Finset V → ℝ)
          (E B : Finset (Sym2 V)) (dE dB : ℕ),
          prescribedOrder a b α h η ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
          (∀ T, IsAllowed H F T →
            a / Fintype.card V ≤ μ T ∧ μ T ≤ b / Fintype.card V) →
          (∀ e ∈ edges H, |bdry H F μ e - 1| ≤ prescribedLoadTolerance η) →
          E ⊆ edges H → Disjoint E B →
          (∀ v, degIn E v ≤ dE) → (dE : ℝ) ≤ prescribedBudget a b α h * Fintype.card V →
          (∀ v, degIn B v ≤ dB) → (dB : ℝ) ≤ prescribedAvoidBudget a b α η * Fintype.card V →
          ∃ (E₀ : Finset (Sym2 V)) (D₀ : Finset (Finset V)),
            E ⊆ E₀ ∧ E₀ ⊆ edges H ∧ IsDecomposition H F E₀ D₀ ∧
            Disjoint E₀ B ∧
            ∀ v, (degIn (edges H \ E₀) v : ℝ) ≤ η * Fintype.card V := by
  intro η hη V _ H μ E B dE dB hn h3 h4 hWeights hLoad hE hEB hEdeg hEcap hBdeg hBcap
  obtain ⟨W,DS,E₀,D₀,hW,hDS,hSE,hDSsub,hE₀,hDec,hAvoid,hHole,hDegree⟩ :=
    dense_reference_containing_sparse_edges_with_stock_explicit F a b α h ha hab hα η hη
      H μ E B dE dB hn h3 h4 hWeights hLoad hE hEB hEdeg hEcap hBdeg hBcap
  exact ⟨E₀,D₀,subset_union_left.trans hSE,hE₀,hDec,hAvoid,hHole⟩

#print axioms dense_reference_containing_sparse_edges_with_stock_explicit
#print axioms dense_reference_containing_sparse_edges_explicit
end TypedTriangle.RawReference.Explicit
