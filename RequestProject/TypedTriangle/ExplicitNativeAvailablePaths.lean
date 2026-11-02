/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExplicitOddPaths
public import RequestProject.TypedTriangle.VortexAutomaticCleanRawPathsBeforeRate
public import RequestProject.TypedTriangle.VortexWindowPathTrim
@[expose] public section
open Finset Classical S07V24 S07V25
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex.ExplicitRaw
open CorePaid ComponentRows

def nativeInteriorCount (α : ℝ) (h : ℕ) : ℕ := S07V24.Explicit.pathInteriorCount α (kappaOf α h)
def nativeDensity (α : ℝ) (h : ℕ) : ℝ := S07V24.Explicit.pathDensity α (kappaOf α h)
def nativeAvoidBudget (α : ℝ) (h : ℕ) : ℝ := nativeDensity α h/(4*(nativeInteriorCount α h:ℝ))
def nativeRouteOrder (α : ℝ) (h : ℕ) : ℕ :=
  max (S07V24.Explicit.oddPathOrder α (kappaOf α h)) (n1Of α)

/-- Native original-root paths remain plentiful after an arbitrary small
fixed deletion of their auxiliaries. All constants precede every sampling
rate, and the two fixed roots may themselves belong to the deletion set. -/
theorem nativePathScalars_spec (α : ℝ) (h : ℕ) (hα : 0 < α) :
    let m := nativeInteriorCount α h;
    let a := nativeDensity α h;
    let δ := nativeAvoidBudget α h;
    0 < m ∧ 0 < a ∧ 0 < δ ∧ Odd (m+1) ∧ 3 ≤ m+1 := by
  let κ := kappaOf α h
  have hκ : 0 < κ := kappaOf_pos hα h
  dsimp only
  let m := nativeInteriorCount α h
  let a := nativeDensity α h
  have hm : 0 < m := by dsimp [m,nativeInteriorCount,S07V24.Explicit.pathInteriorCount]; positivity
  have ha : 0 < a := by
    have hp : 0 < min α 1 := lt_min hα one_pos
    dsimp [a,nativeDensity,S07V24.Explicit.pathDensity]
    positivity
  have hodd : Odd (m+1) := by
    obtain ⟨hk,_⟩ := S07V24.Explicit.oddPathK_spec hα hκ
    have heq : m+1 = S07V24.Explicit.oddPathK α κ + 2 := by dsimp [m,nativeInteriorCount,S07V24.Explicit.pathInteriorCount]
    rw [heq]
    exact hk.add_even even_two
  have ht3 : 3 ≤ m+1 := by
    change 3 ≤ S07V24.Explicit.oddPathK α (kappaOf α h)+2
    unfold S07V24.Explicit.oddPathK
    omega
  let δ := a/(4*(m:ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  exact ⟨hm,ha,hδ,hodd,ht3⟩

/-- The original-root path supply at the specified scalar constants and order. -/
theorem native_available_path_supply_explicit (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
      nativeRouteOrder α h ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
      ∀ A : Finset V, (A.card:ℝ) ≤ nativeAvoidBudget α h*Fintype.card V →
      ∀ v x y, AdmPair (activeComps H.G H.lab F)
        (fun v C => IsBip H.G H.lab F (v,C)) (colG H.G H.lab F) v x y →
        (nativeDensity α h/2)*(Fintype.card V:ℝ)^(nativeInteriorCount α h) ≤
          (pathsIn (link H.G H.lab F v) (nativeInteriorCount α h) x y (univ \ A)).card := by
  let κ := kappaOf α h
  have hκ : 0 < κ := kappaOf_pos hα h
  let m := nativeInteriorCount α h
  let a := nativeDensity α h
  let δ := nativeAvoidBudget α h
  obtain ⟨hm,ha,hδ,hodd,ht3⟩ := nativePathScalars_spec α h hα
  intro V I _ H F hn h3 h4 A hA v x y hadm
  letI : DecidableEq V := Classical.decEq _
  letI : ∀ v, DecidableRel (link H.G H.lab F v).Adj := fun _ => Classical.decRel _
  have hI := activeComps_interface hα h3 h4 ((le_max_right _ _).trans hn)
  have hpaths : a*(Fintype.card V:ℝ)^m ≤
      (pathsLen (link H.G H.lab F v) (m+1) x y).card := by
    obtain ⟨C,hC,hx,hy,hxy,hcol⟩ := hadm
    exact S07V24.Explicit.link_paths_of_interface_formula α κ hα hκ (link H.G H.lab F v)
      (Fintype.card V) ((le_max_left _ _).trans hn) rfl C
      (IsBip H.G H.lab F (v,C)) (colG H.G H.lab F v)
      (hI v C hC) x y hx hy hxy hcol
  have hFull : pathsIn (link H.G H.lab F v) m x y univ =
      pathsLen (link H.G H.lab F v) (m+1) x y := by
    simp [pathsIn]
  have hTrim := paths_in_trim_count (link H.G H.lab F v) m x y univ A
  rw [hFull,Finset.card_univ] at hTrim
  have hTrimR : ((pathsLen (link H.G H.lab F v) (m+1) x y).card:ℝ) ≤
      (pathsIn (link H.G H.lab F v) m x y (univ \ A)).card +
        (A.card:ℝ)*(m:ℝ)*(Fintype.card V:ℝ)^(m-1) := by exact_mod_cast hTrim
  have hδm : δ*(m:ℝ) = a/4 := by
    dsimp only [δ,nativeAvoidBudget]
    field_simp <;> dsimp only [m,a] <;> ring
  have hPower : (Fintype.card V:ℝ)^(m-1)*(Fintype.card V:ℝ) =
      (Fintype.card V:ℝ)^m := by rw [← pow_succ,Nat.sub_add_cancel hm]
  have hLoss : (A.card:ℝ)*(m:ℝ)*(Fintype.card V:ℝ)^(m-1) ≤
      (a/4)*(Fintype.card V:ℝ)^m := by
    calc
      (A.card:ℝ)*(m:ℝ)*(Fintype.card V:ℝ)^(m-1) =
          (A.card:ℝ)*((m:ℝ)*(Fintype.card V:ℝ)^(m-1)) := by ring
      _ ≤ (δ*Fintype.card V)*((m:ℝ)*(Fintype.card V:ℝ)^(m-1)) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
      _ = (a/4)*(Fintype.card V:ℝ)^m := by rw [← hδm,← hPower]; ring
  have hPos : 0 ≤ a*(Fintype.card V:ℝ)^m := by positivity
  nlinarith only [hpaths,hTrimR,hLoss,hPos]

#print axioms nativePathScalars_spec
#print axioms native_available_path_supply_explicit
end TypedTriangle.Vortex.ExplicitRaw
