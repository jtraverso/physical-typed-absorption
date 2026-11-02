/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexGlobalRadiusSchedule
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.Vortex.Explicit

def radiusState (εprep : ℝ → ℝ) (b : ℝ) (L : ℕ) (βTop : ℝ) :
    ℕ → ℝ × ℝ
  | 0 => (βTop, εprep βTop)
  | r + 1 =>
      let s := radiusState εprep b L βTop r
      let next := min (s.1 / 2) (s.2 / (16 * b * (L + 1))) / 2
      (next, min s.2 (εprep next))

theorem radiusState_pos (εprep : ℝ → ℝ) (b : ℝ) (L r : ℕ)
    (βTop : ℝ) (hb : 0 < b) (hTop : 0 < βTop)
    (hε : ∀ x, 0 < x → 0 < εprep x) :
    0 < (radiusState εprep b L βTop r).1 ∧
    0 < (radiusState εprep b L βTop r).2 := by
  induction r with
  | zero => exact ⟨by simpa [radiusState] using hTop,
      by simpa [radiusState] using hε βTop hTop⟩
  | succ r ih =>
      have hden : 0 < 16 * b * (L + 1 : ℝ) := by positivity
      have hnext : 0 < min ((radiusState εprep b L βTop r).1 / 2)
          ((radiusState εprep b L βTop r).2 / (16 * b * (L + 1))) / 2 := by
        exact half_pos (lt_min (half_pos ih.1) (div_pos ih.2 hden))
      exact ⟨by simpa only [radiusState] using hnext,
        by simpa only [radiusState] using lt_min ih.2 (hε _ hnext)⟩

theorem radiusState_min_le (εprep : ℝ → ℝ) (b : ℝ) (L r t : ℕ)
    (βTop : ℝ)
    (ht : t ≤ r) :
    (radiusState εprep b L βTop r).2 ≤
      εprep (radiusState εprep b L βTop t).1 := by
  induction r with
  | zero =>
      have : t = 0 := by omega
      subst t
      simp [radiusState]
  | succ r ih =>
      by_cases h : t ≤ r
      · have hleft : (radiusState εprep b L βTop (r + 1)).2 ≤
            (radiusState εprep b L βTop r).2 := by
          change min (radiusState εprep b L βTop r).2
            (εprep (min ((radiusState εprep b L βTop r).1 / 2)
              ((radiusState εprep b L βTop r).2 / (16 * b * (L + 1))) / 2)) ≤ _
          exact min_le_left _ _
        exact hleft.trans (ih h)
      · have : t = r + 1 := by omega
        subst t
        simp only [radiusState]
        exact min_le_right _ _

theorem radiusState_first_le_top (εprep : ℝ → ℝ) (b : ℝ)
    (L r : ℕ) (βTop : ℝ) (hb : 0 < b) (hTop : 0 < βTop)
    (hε : ∀ x, 0 < x → 0 < εprep x) :
    (radiusState εprep b L βTop r).1 ≤ βTop := by
  induction r with
  | zero => simp [radiusState]
  | succ r ih =>
      have hprev : 0 ≤ (radiusState εprep b L βTop r).1 :=
        (radiusState_pos εprep b L r βTop hb hTop hε).1.le
      have hmin : min ((radiusState εprep b L βTop r).1 / 2)
          ((radiusState εprep b L βTop r).2 / (16*b*(L+1))) ≤
          (radiusState εprep b L βTop r).1 / 2 := min_le_left _ _
      change min ((radiusState εprep b L βTop r).1 / 2)
          ((radiusState εprep b L βTop r).2 / (16*b*(L+1))) / 2 ≤ βTop
      linarith

/-- A transparent finite backward recursion. No robustness parameter is
selected through a choice function or a fixed-point theorem. -/
def radiusSequence (εprep : ℝ → ℝ) (b : ℝ) (L : ℕ) (βTop : ℝ) (j : ℕ) : ℝ :=
  (radiusState εprep b L βTop (L-j)).1

/-- Backward choice for the genuine dependency `εprep (β k)`. There are at
most `L` strict quotient changes, so this schedule is fixed before any
sampled chain, regardless of its depth. -/
theorem radiusSequence_spec (εprep : ℝ → ℝ)
    (b : ℝ) (L : ℕ) (βTop : ℝ) (hb : 0 < b) (hTop : 0 < βTop)
    (hε : ∀ x, 0 < x → 0 < εprep x) :
    let β := radiusSequence εprep b L βTop;
      (∀ j ≤ L, 0 < β j) ∧
      (∀ j < L, β j ≤ β (j + 1) / 2) ∧
      (∀ j k, j < k → k ≤ L →
        β j ≤ εprep (β k) / (16 * b * (L + 1))) ∧
      (∀ r ≤ L, 2 * b * (∑ j ∈ range r, β j) ≤ εprep (β r) / 8) ∧
      (∀ j ≤ L, β j ≤ βTop) ∧
      (∑ j ∈ range (L + 1), β j) ≤ (L + 1 : ℝ) * βTop := by
  dsimp only
  let β := radiusSequence εprep b L βTop
  have hβpos : ∀ j ≤ L, 0 < β j := by
    intro j _
    exact (radiusState_pos εprep b L (L-j) βTop hb hTop hε).1
  have hβstep : ∀ j < L, β j ≤ β (j + 1) / 2 := by
    intro j hj
    have hs : L - j = (L - (j + 1)) + 1 := by omega
    have hleft : β j =
        min ((radiusState εprep b L βTop (L - (j + 1))).1 / 2)
          ((radiusState εprep b L βTop (L - (j + 1))).2 / (16*b*(L+1))) / 2 := by
      dsimp only [β,radiusSequence]
      rw [hs]
      rfl
    rw [hleft]
    change _ ≤ (radiusState εprep b L βTop (L - (j + 1))).1 / 2
    have hm : min ((radiusState εprep b L βTop (L - (j + 1))).1 / 2)
        ((radiusState εprep b L βTop (L - (j + 1))).2 / (16*b*(L+1))) ≤
        (radiusState εprep b L βTop (L - (j + 1))).1 / 2 := min_le_left _ _
    have hprev : 0 ≤ (radiusState εprep b L βTop (L - (j + 1))).1 :=
      (radiusState_pos εprep b L _ βTop hb hTop hε).1.le
    linarith
  have hcross : ∀ j k, j < k → k ≤ L →
      β j ≤ εprep (β k) / (16 * b * (L + 1)) := by
    intro j k hjk hk
    have hr : L - j = (L - j - 1) + 1 := by omega
    have ht : L - k ≤ L - j - 1 := by omega
    have hmin := radiusState_min_le εprep b L (L-j-1) (L-k) βTop ht
    have hden : 0 < 16 * b * (L + 1 : ℝ) := by positivity
    have hcomp :
        (radiusState εprep b L βTop (L-j-1)).2 / (16*b*(L+1)) ≤
        εprep (radiusState εprep b L βTop (L-k)).1 / (16*b*(L+1)) :=
      div_le_div_of_nonneg_right hmin hden.le
    have hleft : β j =
        min ((radiusState εprep b L βTop (L-j-1)).1 / 2)
          ((radiusState εprep b L βTop (L-j-1)).2 / (16*b*(L+1))) / 2 := by
      dsimp only [β,radiusSequence]
      rw [hr]
      rfl
    rw [hleft]
    change _ ≤ εprep (radiusState εprep b L βTop (L-k)).1 / (16*b*(L+1))
    have hm : min ((radiusState εprep b L βTop (L-j-1)).1 / 2)
        ((radiusState εprep b L βTop (L-j-1)).2 / (16*b*(L+1))) ≤
        (radiusState εprep b L βTop (L-j-1)).2 / (16*b*(L+1)) := min_le_right _ _
    have hnum : 0 ≤ (radiusState εprep b L βTop (L-j-1)).2 :=
      (radiusState_pos εprep b L _ βTop hb hTop hε).2.le
    have hfrac : 0 ≤ (radiusState εprep b L βTop (L-j-1)).2 /
        (16*b*(L+1)) := div_nonneg hnum hden.le
    linarith
  have hβtop : ∀ j ≤ L, β j ≤ βTop := by
    intro j _
    exact radiusState_first_le_top εprep b L (L-j) βTop hb hTop hε
  refine ⟨hβpos,hβstep,hcross,?_,hβtop,?_⟩
  · intro r hr
    exact earlier_radii_within_window β (fun j => εprep (β j)) b hb L r hr
      (hε _ (hβpos r hr)).le
      (by intro j hj; exact hcross j r hj hr)
  · calc
      (∑ j ∈ range (L + 1), β j) ≤ ∑ _j ∈ range (L + 1), βTop := by
        apply Finset.sum_le_sum
        intro j hj
        exact hβtop j (by simpa using hj)
      _ = (L + 1 : ℝ) * βTop := by simp [nsmul_eq_mul]

/-- Fixed cap and total debt, with a constant extension past the last index. -/
def radiusTop (cap η : ℝ) (L : ℕ) : ℝ := min cap (η/(2*(L+1:ℝ)))

def cappedRadius (εprep : ℝ → ℝ) (b : ℝ) (L : ℕ) (cap η : ℝ) : ℕ → ℝ :=
  radiusSequence εprep b L (radiusTop cap η L)

/-- Every exported radius is the stated finite formula. The index bound L,
tolerance function and total debt all precede the host order. -/
theorem cappedRadius_spec (εprep : ℝ → ℝ) (b : ℝ) (L : ℕ) (cap η : ℝ)
    (hb : 0 < b) (hcap : 0 < cap) (hη : 0 < η)
    (hε : ∀ x, 0 < x → 0 < εprep x) :
    let β := cappedRadius εprep b L cap η;
    (∀ j, 0 < β j ∧ β j ≤ cap) ∧
    (∀ j < L, β j ≤ β (j+1)/2) ∧
    (∀ j k, j < k → k ≤ L → β j ≤ εprep (β k)/(16*b*(L+1))) ∧
    (∀ r ≤ L, 2*b*(∑ j ∈ range r, β j) ≤ εprep (β r)/8) ∧
    (∑ j ∈ range (L+1), β j) ≤ η/2 := by
  dsimp only
  let βTop := radiusTop cap η L
  have hTop : 0 < βTop := lt_min hcap (by positivity)
  have hSpec := radiusSequence_spec εprep b L βTop hb hTop hε
  dsimp only at hSpec
  obtain ⟨hpos,hstep,hcross,hbudget,htop,hsum⟩ := hSpec
  refine ⟨?_,hstep,hcross,hbudget,?_⟩
  · intro j
    have hjPos := (radiusState_pos εprep b L (L-j) βTop hb hTop hε).1
    have hjTop := radiusState_first_le_top εprep b L (L-j) βTop hb hTop hε
    exact ⟨hjPos,hjTop.trans (min_le_left _ _)⟩
  · have hTopη : βTop ≤ η/(2*(L+1:ℝ)) := min_le_right _ _
    have hfactor : 0 ≤ (L+1:ℝ) := by positivity
    have hm := mul_le_mul_of_nonneg_left hTopη hfactor
    have heq : (L+1:ℝ)*(η/(2*(L+1:ℝ))) = η/2 := by field_simp
    change (∑ j ∈ range (L+1), radiusSequence εprep b L βTop j) ≤ η/2
    rw [heq] at hm
    exact hsum.trans hm

/-- The numerical inverse/profile tolerance passed into the radius recursion. -/
def paidProfileTolerance (C : ℝ) (K δ : ℝ → ℝ) (x : ℝ) : ℝ :=
  min (1/(2*C*K x)) (δ x)

theorem paidProfileTolerance_pos (C : ℝ) (K δ : ℝ → ℝ)
    (hC : 0 < C) (hK : ∀ x, 0 < x → 0 < K x) (hδ : ∀ x, 0 < x → 0 < δ x)
    (x : ℝ) (hx : 0 < x) : 0 < paidProfileTolerance C K δ x := by
  exact lt_min (by have hp := hK x hx; positivity) (hδ x hx)

/-- The explicit radius function simultaneously pays the smooth inverse and
reference-load profile. This theorem contains no existential numerical data. -/
theorem capped_paid_profile_spec (C b cap η : ℝ) (K δ : ℝ → ℝ) (L : ℕ)
    (hC : 0 < C) (hb : 0 < b) (hcap : 0 < cap) (hη : 0 < η)
    (hK : ∀ x, 0 < x → 0 < K x) (hδ : ∀ x, 0 < x → 0 < δ x) :
    let β := cappedRadius (paidProfileTolerance C K δ) b L cap η;
    (∀ j, 0 < β j ∧ β j ≤ cap) ∧
    (∀ j < L, β j ≤ β (j+1)/2) ∧
    (∀ r ≤ L,
      K (β r)*(2*b*(∑ j ∈ range r, β j)) ≤ 1/(16*C) ∧
      2*b*(∑ j ∈ range r, β j) ≤ δ (β r)/8) ∧
    (∑ j ∈ range (L+1), β j) ≤ η/2 := by
  dsimp only
  let β := cappedRadius (paidProfileTolerance C K δ) b L cap η
  obtain ⟨hpos,hstep,hcross,hprior,hsum⟩ := cappedRadius_spec
    (paidProfileTolerance C K δ) b L cap η hb hcap hη
    (paidProfileTolerance_pos C K δ hC hK hδ)
  refine ⟨hpos,hstep,?_,hsum⟩
  intro r hr
  have hp := hprior r hr
  have hKr : 0 < K (β r) := hK _ (hpos r).1
  constructor
  · calc
      K (β r)*(2*b*(∑ j ∈ range r, β j)) ≤
          K (β r)*((1/(2*C*K (β r)))/8) :=
        mul_le_mul_of_nonneg_left
          (hp.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))) hKr.le
      _ = 1/(16*C) := by field_simp; ring
  · exact hp.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))

/-- A named finite maximum, used to aggregate all radius-dependent orders. -/
def scheduleOrder (nGeometry : ℕ) (nAt : ℝ → ℕ) (β : ℕ → ℝ) (L : ℕ) : ℕ :=
  max nGeometry ((univ : Finset (Fin (L+1))).sup (fun j => nAt (β j)))

theorem scheduleOrder_geometry (nGeometry : ℕ) (nAt : ℝ → ℕ) (β : ℕ → ℝ) (L : ℕ) :
    nGeometry ≤ scheduleOrder nGeometry nAt β L := le_max_left _ _

theorem scheduleOrder_at (nGeometry : ℕ) (nAt : ℝ → ℕ) (β : ℕ → ℝ) (L : ℕ)
    (j : Fin (L+1)) : nAt (β j) ≤ scheduleOrder nGeometry nAt β L :=
  (Finset.le_sup (f := fun i : Fin (L+1) => nAt (β i)) (mem_univ j)).trans (le_max_right _ _)

#print axioms radiusSequence_spec
#print axioms cappedRadius_spec
#print axioms capped_paid_profile_spec
#print axioms scheduleOrder_at

end TypedTriangle.Vortex.Explicit
