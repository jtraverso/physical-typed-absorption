/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExplicitGlobalRadiusSchedule
public import RequestProject.TypedTriangle.ExplicitPaidSmooth
public import RequestProject.TypedTriangle.ExplicitPrescribedReference
public import RequestProject.TypedTriangle.VortexConcreteInnerLayerParameters
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TypedTriangle.Vortex.Explicit
open ExplicitPaid

/-- The future density precedes every state-hole and route precision. -/
def futureDensity (α C : ℝ) (h : ℕ) : ℝ :=
  RawReference.Explicit.prescribedBudget (3/(4*C)) (2*C) α h

theorem futureDensity_pos (α C : ℝ) (h : ℕ) (hα : 0 < α) (hC : 1 ≤ C) :
    0 < futureDensity α C h := by
  have hCp : 0 < C := by linarith
  have ha : 0 < 3/(4*C) := by positivity
  have hab : 3/(4*C) ≤ 2*C := by
    apply (div_le_iff₀ (by positivity : 0 < 4*C)).mpr
    nlinarith only [hC]
  exact RawReference.Explicit.prescribedBudget_pos h ha hab hα

def referencePrecision (α C ζState : ℝ) (h : ℕ) (x : ℝ) : ℝ :=
  min ζState (min (α/(10*(2:ℝ)^h.choose 2))
    (min (paidBudget α h/4) (1/(512*C*C*paidInverseCost α x h))))

def referenceLoad (α C ζState : ℝ) (h : ℕ) (x : ℝ) : ℝ :=
  RawReference.Explicit.prescribedLoadTolerance (referencePrecision α C ζState h x)

def referenceAvoid (α C ζState : ℝ) (h : ℕ) (x : ℝ) : ℝ :=
  RawReference.Explicit.prescribedAvoidBudget (3/(4*C)) (2*C) α
    (referencePrecision α C ζState h x)

def referenceThreshold (α C ζState : ℝ) (h : ℕ) (x : ℝ) : ℕ :=
  RawReference.Explicit.prescribedOrder (3/(4*C)) (2*C) α h
    (referencePrecision α C ζState h x)

def innerRadius (α C cap ζState ηGlobal : ℝ) (h L : ℕ) : ℕ → ℝ :=
  cappedRadius (paidProfileTolerance C (fun x => paidInverseCost α x h)
    (referenceLoad α C ζState h)) (2*C) L cap ηGlobal

def innerNodeOrder (α C ζState : ℝ) (h : ℕ) (x : ℝ) : ℕ :=
  max (max (max (paidOrder α h) (paidPreparedOrder α h)) (paidInverseOrder α h))
    (referenceThreshold α C ζState h x)

def innerScheduleOrder (α C cap ζState ηGlobal : ℝ) (h L : ℕ) : ℕ :=
  scheduleOrder (paidOrder α h) (innerNodeOrder α C ζState h)
    (innerRadius α C cap ζState ηGlobal h L) L

theorem referencePrecision_pos (α C ζState : ℝ) (h : ℕ) (x : ℝ)
    (hα : 0 < α) (hC : 0 < C) (hζ : 0 < ζState) :
    0 < referencePrecision α C ζState h x := by
  have hp := paidBudget_pos h hα
  have hK := paidInverseCost_pos x h hα
  unfold referencePrecision
  positivity

theorem referencePrecision_caps (α C ζState : ℝ) (h : ℕ) (x : ℝ) :
    referencePrecision α C ζState h x ≤ ζState ∧
    referencePrecision α C ζState h x ≤ α/(10*(2:ℝ)^h.choose 2) ∧
    referencePrecision α C ζState h x ≤ paidBudget α h/4 ∧
    referencePrecision α C ζState h x ≤ 1/(512*C*C*paidInverseCost α x h) := by
  have hh : referencePrecision α C ζState h x ≤
      min ζState (min (α/(10*(2:ℝ)^h.choose 2))
        (min (paidBudget α h/4) (1/(512*C*C*paidInverseCost α x h)))) := le_rfl
  simpa only [le_min_iff] using hh

theorem referenceLoad_pos (α C ζState : ℝ) (h : ℕ) (x : ℝ)
    (hα : 0 < α) (hC : 0 < C) (hζ : 0 < ζState) :
    0 < referenceLoad α C ζState h x :=
  RawReference.Explicit.prescribedLoadTolerance_pos (referencePrecision_pos α C ζState h x hα hC hζ)

/-- The explicit radius function has all prefix and total-debt certificates. -/
theorem innerRadius_spec (α C cap ζState ηGlobal : ℝ) (h L : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hcap : 0 < cap)
    (hζ : 0 < ζState) (hGlobal : 0 < ηGlobal) :
    let β := innerRadius α C cap ζState ηGlobal h L;
    (∀ j, 0 < β j ∧ β j ≤ cap) ∧
    (∀ j < L, β j ≤ β (j+1)/2) ∧
    (∀ r ≤ L, paidInverseCost α (β r) h*(4*C*(∑ j ∈ range r,β j)) ≤ 1/(16*C) ∧
      4*C*(∑ j ∈ range r,β j) ≤ referenceLoad α C ζState h (β r)/8) ∧
    (∑ j ∈ range (L+1),β j) ≤ ηGlobal/2 := by
  have hCp : 0 < C := by linarith
  have hp := capped_paid_profile_spec C (2*C) cap ηGlobal
    (fun x => paidInverseCost α x h) (referenceLoad α C ζState h) L hCp (by positivity)
    hcap hGlobal (fun x _ => paidInverseCost_pos x h hα)
    (fun x _ => referenceLoad_pos α C ζState h x hα hCp hζ)
  dsimp only at hp ⊢
  simpa only [innerRadius,show (2:ℝ)*(2*C)=4*C by ring] using hp

/-- This is the actual legacy-consumable schedule, with every scalar and order
specified above. No numerical existential or choice operation is an input. -/
def concreteInnerSchedule {I : Type} (F : Set (Multiset I))
    (α C cap ζState ηGlobal : ℝ) (h L : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hh : 6 ≤ h) (hcap : 0 < cap)
    (hζ : 0 < ζState) (hGlobal : 0 < ηGlobal) :
    ConcreteInnerLayerSchedule F α C (futureDensity α C h) ζState
      (innerRadius α C cap ζState ηGlobal h L) h
      (innerScheduleOrder α C cap ζState ηGlobal h L) L := by
  have hCp : 0 < C := by linarith
  have ha : 0 < 3/(4*C) := by positivity
  have hab : 3/(4*C) ≤ 2*C := by
    apply (div_le_iff₀ (by positivity : 0 < 4*C)).mpr
    nlinarith only [hC]
  let β := innerRadius α C cap ζState ηGlobal h L
  obtain ⟨hβ,hStep,hPrior,hSum⟩ := innerRadius_spec α C cap ζState ηGlobal h L hα hC hcap hζ hGlobal
  refine {
    K := fun r => paidInverseCost α (β r) h
    ηSpec := fun _ => paidBudget α h
    ζRef := fun r => referencePrecision α C ζState h (β r)
    εRef := fun r => referenceLoad α C ζState h (β r)
    γRef := fun r => referenceAvoid α C ζState h (β r)
    Nbase := fun _ => paidOrder α h
    Ns := fun _ => paidPreparedOrder α h
    nPaid := fun _ => paidInverseOrder α h
    nRef := fun r => referenceThreshold α C ζState h (β r)
    nGeometry := paidOrder α h
    K_pos := fun r _ => paidInverseCost_pos (β r) h hα
    ηSpec_pos := fun _ _ => paidBudget_pos h hα
    ζRef_pos := fun r _ => referencePrecision_pos α C ζState h (β r) hα hCp hζ
    εRef_pos := fun r _ => referenceLoad_pos α C ζState h (β r) hα hCp hζ
    γRef_pos := ?_
    ref_state := fun r _ => (referencePrecision_caps α C ζState h (β r)).1
    ref_spec := ?_
    ref_clean := fun r _ => (referencePrecision_caps α C ζState h (β r)).2.1
    paid_cap := fun _ _ => paid_reference_cap_explicit α h hα hh
    paid_smooth := fun r _ => paid_smooth_at_explicit α (β r) h hα (hβ r).1 hh
    reference := ?_
    orders := ?_
    geometry_order := scheduleOrder_geometry _ _ _ _
    hole_inverse := ?_
    prefix_inverse := fun r hr => (hPrior r hr).1
    prefix_reference := fun r hr => (hPrior r hr).2 }
  · intro r _
    exact RawReference.Explicit.prescribedAvoidBudget_pos ha hab hα
      (referencePrecision_pos α C ζState h (β r) hα hCp hζ)
  · intro r _
    have hc := (referencePrecision_caps α C ζState h (β r)).2.2.1
    have hb := paidBudget_pos h hα
    linarith only [hc,hb]
  · intro r _
    exact RawReference.Explicit.dense_reference_containing_sparse_edges_explicit F
      (3/(4*C)) (2*C) α h ha hab hα (referencePrecision α C ζState h (β r))
      (referencePrecision_pos α C ζState h (β r) hα hCp hζ)
  · intro r hr
    exact scheduleOrder_at (paidOrder α h) (innerNodeOrder α C ζState h)
      (innerRadius α C cap ζState ηGlobal h L) L ⟨r,by omega⟩
  · intro r _
    have hc := (referencePrecision_caps α C ζState h (β r)).2.2.2
    have hK := paidInverseCost_pos (β r) h hα
    have hDen : 0 < 512*C*C*paidInverseCost α (β r) h := by positivity
    have hm := (le_div_iff₀ hDen).mp hc
    apply (le_div_iff₀ (by positivity : 0 < 16*C)).mpr
    nlinarith only [hm]

#print axioms innerRadius_spec
#print axioms concreteInnerSchedule
end TypedTriangle.Vortex.Explicit
