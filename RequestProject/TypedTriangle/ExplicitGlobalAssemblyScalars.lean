/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexUniformInnerRate
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Vortex.Explicit

def uniformInnerRate (α a εOuter γStock ηBank ρFuture : ℝ) (h m : ℕ) : ℝ :=
  min (1/32) (min (εOuter/4) (min (ρFuture/2)
    (min (ηBank/16) (min (γStock/8)
      (min (α/(64*(2:ℝ)^h.choose 2)) (a/(64*(m:ℝ)*(2:ℝ)^m)))))))

def stateHoleCap (α a q : ℝ) (m : ℕ) : ℝ :=
  min (windowRouteRate a q m/4) (α*q/128)

theorem uniformInnerRate_spec (α a εOuter γStock ηBank ρFuture : ℝ) (h m : ℕ)
    (hα : 0 < α) (ha : 0 < a) (hε : 0 < εOuter)
    (hγ : 0 < γStock) (hη : 0 < ηBank) (hρ : 0 < ρFuture) (hm : 0 < m) :
    let q := uniformInnerRate α a εOuter γStock ηBank ρFuture h m;
    let ζState := stateHoleCap α a q m;
    0 < q ∧ q ≤ 1 / 32 ∧ 4*q ≤ εOuter ∧
      2*q ≤ ρFuture ∧ q ≤ ηBank/16 ∧ q ≤ γStock/8 ∧
      q ≤ α/(64*(2:ℝ)^h.choose 2) ∧
      q*m*(2:ℝ)^m ≤ a/64 ∧ 0 < ζState ∧
      ζState ≤ windowRouteRate a q m/4 ∧ ζState ≤ α*q/128 := by
  dsimp only
  let q := uniformInnerRate α a εOuter γStock ηBank ρFuture h m
  have hmReal : (0:ℝ) < m := by exact_mod_cast hm
  have hq : 0 < q := by dsimp [q,uniformInnerRate]; positivity
  have hCaps : q ≤ 1/32 ∧ q ≤ εOuter/4 ∧ q ≤ ρFuture/2 ∧
      q ≤ ηBank/16 ∧ q ≤ γStock/8 ∧
      q ≤ α/(64*(2:ℝ)^h.choose 2) ∧ q ≤ a/(64*(m:ℝ)*(2:ℝ)^m) := by
    have hqAll : q ≤ min (1/32) (min (εOuter/4) (min (ρFuture/2)
        (min (ηBank/16) (min (γStock/8)
          (min (α/(64*(2:ℝ)^h.choose 2)) (a/(64*(m:ℝ)*(2:ℝ)^m))))))) := le_rfl
    simpa only [le_min_iff] using hqAll
  have hPath : q*m*(2:ℝ)^m ≤ a/64 := by
    have hs := (le_div_iff₀ (by positivity : 0 < 64*(m:ℝ)*(2:ℝ)^m)).mp
      hCaps.2.2.2.2.2.2
    nlinarith
  let ζ := stateHoleCap α a q m
  have hRate := windowRouteRate_pos m ha hq
  have hζ : 0 < ζ := lt_min (by positivity) (by positivity)
  refine ⟨hq,hCaps.1,?_,?_,hCaps.2.2.2.1,hCaps.2.2.2.2.1,
    hCaps.2.2.2.2.2.1,hPath,hζ,min_le_left _ _,min_le_right _ _⟩ <;> linarith [hCaps.2.1,hCaps.2.2.1]


def preparationDebtCap (α C ε δOuter : ℝ) (h : ℕ) : ℝ :=
  min δOuter (min ε (min (α/(4*(2:ℝ)^h.choose 2)) (1/(8*max 1 (2*C)))))

def globalDebtCap (α C ε δOuter aInner aOuter : ℝ) (h mInner mOuter : ℕ) : ℝ :=
  min (1/8) (min (α/128)
    (min (aInner/(64*(mInner:ℝ)*(2:ℝ)^mInner))
      (min (aOuter/(128*(mOuter:ℝ)*(2:ℝ)^mOuter)) (preparationDebtCap α C ε δOuter h))))

theorem globalDebtCap_spec (α C ε δOuter aInner aOuter : ℝ) (h mInner mOuter : ℕ)
    (hα : 0 < α) (hε : 0 < ε) (hδ : 0 < δOuter)
    (haInner : 0 < aInner) (haOuter : 0 < aOuter)
    (hmInner : 0 < mInner) (hmOuter : 0 < mOuter) :
    let B := globalDebtCap α C ε δOuter aInner aOuter h mInner mOuter;
    0 < B ∧ B ≤ 1/8 ∧ B ≤ α/128 ∧
    B*mInner*(2:ℝ)^mInner ≤ aInner/64 ∧
    B*mOuter*(2:ℝ)^mOuter ≤ aOuter/128 ∧
    B ≤ preparationDebtCap α C ε δOuter h := by
  dsimp only
  have hmI : (0:ℝ) < mInner := by exact_mod_cast hmInner
  have hmO : (0:ℝ) < mOuter := by exact_mod_cast hmOuter
  have hPrep : 0 < preparationDebtCap α C ε δOuter h := by
    dsimp only [preparationDebtCap]
    positivity
  let B := globalDebtCap α C ε δOuter aInner aOuter h mInner mOuter
  have hB : 0 < B := by dsimp [B,globalDebtCap]; positivity
  have hCaps : B ≤ 1/8 ∧ B ≤ α/128 ∧
      B ≤ aInner/(64*(mInner:ℝ)*(2:ℝ)^mInner) ∧
      B ≤ aOuter/(128*(mOuter:ℝ)*(2:ℝ)^mOuter) ∧
      B ≤ preparationDebtCap α C ε δOuter h := by
    have hh : B ≤ min (1/8) (min (α/128)
        (min (aInner/(64*(mInner:ℝ)*(2:ℝ)^mInner))
          (min (aOuter/(128*(mOuter:ℝ)*(2:ℝ)^mOuter)) (preparationDebtCap α C ε δOuter h)))) := le_rfl
    simpa only [le_min_iff] using hh
  refine ⟨hB,hCaps.1,hCaps.2.1,?_,?_,hCaps.2.2.2.2⟩
  · have hp := (le_div_iff₀ (by positivity : 0 < 64*(mInner:ℝ)*(2:ℝ)^mInner)).mp hCaps.2.2.1
    nlinarith only [hp]
  · have hp := (le_div_iff₀ (by positivity : 0 < 128*(mOuter:ℝ)*(2:ℝ)^mOuter)).mp hCaps.2.2.2.1
    nlinarith only [hp]

def adjustedBankWindow (εOuter aOuter : ℝ) (mOuter : ℕ) : ℝ :=
  min εOuter (aOuter/(32*(mOuter:ℝ)*(2:ℝ)^mOuter))

def globalInnerRate (α aInner aOuter εOuter γStock ηBank ρFuture : ℝ)
    (h mInner mOuter : ℕ) : ℝ :=
  uniformInnerRate α aInner (adjustedBankWindow εOuter aOuter mOuter)
    γStock ηBank ρFuture h mInner

theorem globalInnerRate_spec (α aInner aOuter εOuter γStock ηBank ρFuture : ℝ)
    (h mInner mOuter : ℕ) (hα : 0 < α) (haInner : 0 < aInner) (haOuter : 0 < aOuter)
    (hε : 0 < εOuter) (hγ : 0 < γStock) (hη : 0 < ηBank) (hρ : 0 < ρFuture)
    (hmInner : 0 < mInner) (hmOuter : 0 < mOuter) :
    let q := globalInnerRate α aInner aOuter εOuter γStock ηBank ρFuture h mInner mOuter;
    let ζ := stateHoleCap α aInner q mInner;
    0 < q ∧ q ≤ 1/32 ∧ 4*q ≤ εOuter ∧ 2*q ≤ ρFuture ∧
      q ≤ ηBank/16 ∧ q ≤ γStock/8 ∧ q ≤ α/(64*(2:ℝ)^h.choose 2) ∧
      q*mInner*(2:ℝ)^mInner ≤ aInner/64 ∧ q*mOuter*(2:ℝ)^mOuter ≤ aOuter/128 ∧
      0 < ζ ∧ ζ ≤ windowRouteRate aInner q mInner/4 ∧ ζ ≤ α*q/128 := by
  dsimp only
  have hmO : (0:ℝ) < mOuter := by exact_mod_cast hmOuter
  have hAdjusted : 0 < adjustedBankWindow εOuter aOuter mOuter := lt_min hε (by positivity)
  obtain ⟨hq,hq32,hqCap,hqρ,hqη,hqγ,hqα,hqInner,hζ,hζRoute,hζPool⟩ :=
    uniformInnerRate_spec α aInner (adjustedBankWindow εOuter aOuter mOuter)
      γStock ηBank ρFuture h mInner hα haInner hAdjusted hγ hη hρ hmInner
  have hqOuter : globalInnerRate α aInner aOuter εOuter γStock ηBank ρFuture h mInner mOuter*
      mOuter*(2:ℝ)^mOuter ≤ aOuter/128 := by
    change uniformInnerRate α aInner (adjustedBankWindow εOuter aOuter mOuter)
      γStock ηBank ρFuture h mInner*mOuter*(2:ℝ)^mOuter ≤ aOuter/128
    have hp := hqCap.trans (min_le_right εOuter (aOuter/(32*(mOuter:ℝ)*(2:ℝ)^mOuter)))
    have hs := (le_div_iff₀ (by positivity : 0 < 32*(mOuter:ℝ)*(2:ℝ)^mOuter)).mp hp
    nlinarith only [hs]
  exact ⟨hq,hq32,hqCap.trans (min_le_left _ _),hqρ,hqη,hqγ,hqα,hqInner,hqOuter,hζ,hζRoute,hζPool⟩

#print axioms uniformInnerRate_spec
#print axioms globalDebtCap_spec
#print axioms globalInnerRate_spec
end TypedTriangle.Vortex.Explicit
