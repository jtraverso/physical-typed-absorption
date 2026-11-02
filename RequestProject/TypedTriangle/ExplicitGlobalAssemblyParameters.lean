/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExplicitConcreteInnerSchedule
public import RequestProject.TypedTriangle.ExplicitGlobalAssemblyScalars
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
namespace TypedTriangle.Vortex.Explicit

def assemblyStateCap (α C εBank γStock ηBank aInner aOuter : ℝ) (h mInner mOuter : ℕ) : ℝ :=
  let q := globalInnerRate α aInner aOuter εBank γStock ηBank (futureDensity (α/8) C h) h mInner mOuter
  stateHoleCap α aInner q mInner

def assemblyRadius (α C ε δOuter εBank γStock ηBank aInner aOuter : ℝ)
    (h L mInner mOuter : ℕ) : ℕ → ℝ :=
  innerRadius (α/8) C ε (assemblyStateCap α C εBank γStock ηBank aInner aOuter h mInner mOuter)
    (2*globalDebtCap α C ε δOuter aInner aOuter h mInner mOuter) h L

def assemblyScheduleOrder (α C ε δOuter εBank γStock ηBank aInner aOuter : ℝ)
    (h L mInner mOuter : ℕ) : ℕ :=
  innerScheduleOrder (α/8) C ε (assemblyStateCap α C εBank γStock ηBank aInner aOuter h mInner mOuter)
    (2*globalDebtCap α C ε δOuter aInner aOuter h mInner mOuter) h L

/-- Choose the actual global agenda after both path lengths are known.
The inner rate pays the outer path loss too; the outer sampling rate and
the terminal reserve order have not yet been chosen. -/
theorem global_assembly_parameters_explicit {I : Type} (F : Set (Multiset I))
    (α C ε δOuter εBank γStock ηBank aInner aOuter : ℝ) (h L mInner mOuter : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hh : 6 ≤ h) (hε : 0 < ε)
    (hδ : 0 < δOuter) (hBank : 0 < εBank) (hStock : 0 < γStock)
    (hηBank : 0 < ηBank) (haInner : 0 < aInner) (haOuter : 0 < aOuter)
    (hmInner : 0 < mInner) (hmOuter : 0 < mOuter) :
    let ρ := futureDensity (α/8) C h;
    let q := globalInnerRate α aInner aOuter εBank γStock ηBank ρ h mInner mOuter;
    let ζ := assemblyStateCap α C εBank γStock ηBank aInner aOuter h mInner mOuter;
    let B := globalDebtCap α C ε δOuter aInner aOuter h mInner mOuter;
    let β := assemblyRadius α C ε δOuter εBank γStock ηBank aInner aOuter h L mInner mOuter;
    let N := assemblyScheduleOrder α C ε δOuter εBank γStock ηBank aInner aOuter h L mInner mOuter;
      0 < ρ ∧ 0 < q ∧ q ≤ 1/32 ∧ 4*q ≤ εBank ∧
      2*q ≤ ρ ∧ q ≤ ηBank/16 ∧ q ≤ γStock/8 ∧
      q ≤ α/(64*(2:ℝ)^h.choose 2) ∧
      q*mInner*(2:ℝ)^mInner ≤ aInner/64 ∧
      q*mOuter*(2:ℝ)^mOuter ≤ aOuter/128 ∧
      0 < ζ ∧ ζ ≤ windowRouteRate aInner q mInner/4 ∧ ζ ≤ α*q/128 ∧
      0 < B ∧ B ≤ 1/8 ∧ B ≤ α/128 ∧
      B*mInner*(2:ℝ)^mInner ≤ aInner/64 ∧
      B*mOuter*(2:ℝ)^mOuter ≤ aOuter/128 ∧
      B ≤ min δOuter (min ε (min (α/(4*(2:ℝ)^h.choose 2)) (1/(8*max 1 (2*C))))) ∧
      (∀ j, 0 ≤ β j) ∧ (∀ j ≤ L, 0 < β j ∧ β j ≤ ε) ∧
      (∑ j ∈ range (L+1), β j) ≤ B ∧
      Nonempty (ConcreteInnerLayerSchedule F (α/8) C ρ ζ β h N L) := by
  dsimp only
  let ρ := futureDensity (α/8) C h
  have hρ : 0 < ρ := futureDensity_pos (α/8) C h (by positivity) hC
  obtain ⟨hq,hq32,hqBank,hqρ,hqη,hqStock,hqα,hqInner,hqOuter,hζ,hζRoute,hζPool⟩ :=
    globalInnerRate_spec α aInner aOuter εBank γStock ηBank ρ h mInner mOuter
      hα haInner haOuter hBank hStock hηBank hρ hmInner hmOuter
  let q := globalInnerRate α aInner aOuter εBank γStock ηBank ρ h mInner mOuter
  let ζ := assemblyStateCap α C εBank γStock ηBank aInner aOuter h mInner mOuter
  let B := globalDebtCap α C ε δOuter aInner aOuter h mInner mOuter
  obtain ⟨hB,hB8,hBα,hBInner,hBOuter,hBPrep⟩ :=
    globalDebtCap_spec α C ε δOuter aInner aOuter h mInner mOuter hα hε hδ
      haInner haOuter hmInner hmOuter
  obtain ⟨hβ,hStep,hPrior,hSum⟩ := innerRadius_spec (α/8) C ε ζ (2*B) h L
    (by positivity) hC hε hζ (by positivity)
  have hSchedule := concreteInnerSchedule F (α/8) C ε ζ (2*B) h L
    (by positivity) hC hh hε hζ (by positivity)
  have hTotal : (∑ j ∈ range (L+1),innerRadius (α/8) C ε ζ (2*B) h L j) ≤ B := by linarith only [hSum]
  exact ⟨hρ,hq,hq32,hqBank,hqρ,hqη,hqStock,hqα,hqInner,hqOuter,hζ,hζRoute,hζPool,
    hB,hB8,hBα,hBInner,hBOuter,hBPrep,fun j => (hβ j).1.le,fun j _ => hβ j,hTotal,⟨hSchedule⟩⟩

#print axioms global_assembly_parameters_explicit
end TypedTriangle.Vortex.Explicit
