/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExplicitAutomaticCleanRawSample
public import RequestProject.TypedTriangle.ExplicitNativeAvailablePaths
public import RequestProject.TypedTriangle.VortexFixedSamplingRate
@[expose] public section

open Finset Classical S07V24 S07V25
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex.ExplicitRaw
open RawReference CorePaid ComponentRows

def nativePathTailRate (α q : ℝ) (h : ℕ) : ℝ :=
  nativeDensity α h*q^(2*nativeInteriorCount α h)/(16*(nativeInteriorCount α h:ℝ)^2)

def nativeRoutePrecision (α q : ℝ) (h : ℕ) : ℝ :=
  epsOf (nativeDensity α h) q (nativeInteriorCount α h)

def nativeSampleOrder (α q b : ℝ) (h : ℕ) : ℝ :=
  max (automaticRawOrder α q b (nativePathTailRate α q h) h) (max (nativeRouteOrder α h:ℝ) 1)

/-- Automatic precision, native routes, external-root pools, clean hinges
and the approximate fractional profile are realized on one and the same W. -/
theorem automatic_native_clean_raw_paths_explicit
    (αmin b : ℝ) (h : ℕ)
    (hαmin : 0 < αmin) (hb : 0 < b) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
      let m := nativeInteriorCount αmin h;
      let a := nativeDensity αmin h;
      let εRoute := nativeRoutePrecision αmin q h;
      ∀ {V I : Type} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)) (α ε : ℝ),
        αmin ≤ α → ε ≤ 1/2 → nativeSampleOrder αmin q b h ≤ (Fintype.card V : ℝ) →
        CommonNbrCond H F α → HingeCond H F α h →
        ∀ hClean : CleanHingeCond H F α h,
        ∀ μ : Finset V → ℝ,
          (∀ T, IsAllowed H F T → 0 ≤ μ T ∧ μ T ≤ b/Fintype.card V) →
          (∀ e ∈ edges H, |bdry H F μ e-1| ≤ ε) →
      let η : ℝ := (Real.sqrt (Real.sqrt (Fintype.card V : ℝ)))⁻¹
      0 < η ∧ η < 1 ∧ ∃ W : Finset V,
        (1-η)*q*Fintype.card V ≤ W.card ∧
        (W.card : ℝ) < (1+η)*q*Fintype.card V ∧
        (∀ u v, u ≠ v → ∀ k, ({H.lab u,H.lab v,k} : Multiset I) ∈ F →
          (1-η)*α*q*Fintype.card V ≤ ((commonNbrs H k u v) ∩ W).card) ∧
        (∀ u v a c, HingeTest H.G H.lab F u v a c →
          (1-η)*α*q^(cleanHingeOrder hClean u v a c-4)*
            (Fintype.card V : ℝ)^(cleanHingeOrder hClean u v a c-4) ≤
              (((SparseEdge.hinges H.G H.lab F u v a c
                (cleanHingeOrder hClean u v a c)).filter (fun K => s(a,c) ∉ K)).filter
                  (fun K => freeV u v a c K ⊆ W)).card) ∧
        (∀ u v, H.G.Adj u v →
          |S07V48.sampW H.G H.lab F μ W u v/q-1| ≤ ε+2*η) ∧
        S07V27.RouteProp H.G H.lab F (m+1) εRoute W ∧
        (∀ v x y, AdmPair (activeComps H.G H.lab F)
          (fun v C => IsBip H.G H.lab F (v,C)) (colG H.G H.lab F) v x y →
          a*(Fintype.card V:ℝ)^m*q^m/2 ≤
            (pathsIn (link H.G H.lab F v) m x y W).card) := by
  dsimp only
  let κ := kappaOf αmin h
  have hκ : 0 < κ := kappaOf_pos hαmin h
  let m := nativeInteriorCount αmin h
  let a := nativeDensity αmin h
  obtain ⟨hm,ha,_,hodd,ht3⟩ := nativePathScalars_spec αmin h hαmin
  let θPath := nativePathTailRate αmin q h
  let εRoute := nativeRoutePrecision αmin q h
  let nRoute := nativeRouteOrder αmin h
  have hθPath : 0 < θPath := by dsimp [θPath,nativePathTailRate]; positivity
  have hAuto {V I : Type} [Fintype V] := automatic_clean_raw_profile_quartic_at_explicit_order
    αmin q b θPath h hαmin hq hq1 hb hθPath (V := V) (I := I)
  let Nauto := automaticRawOrder αmin q b θPath h
  let N := nativeSampleOrder αmin q b h
  intro V I _ H F α ε hαge hε hn h3 h4 hClean μ hμ hLoad
  have hnAuto : Nauto ≤ (Fintype.card V:ℝ) := (le_max_left _ _).trans hn
  have hnRoute : nRoute ≤ Fintype.card V := by
    exact_mod_cast (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn0 : 0 < Fintype.card V := by
    have hn1 : (1:ℝ) ≤ Fintype.card V :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hn)
    exact_mod_cast (by linarith : (0:ℝ) < Fintype.card V)
  have h3min : CommonNbrCond H F αmin := commonNbrCond_mono h3 hαge
  have h4min : HingeCond H F αmin h := hingeCond_mono h4 hαge
  letI : DecidableEq V := Classical.decEq _
  letI : ∀ v, DecidableRel (link H.G H.lab F v).Adj := fun _ => Classical.decRel _
  have hnI : n1Of αmin ≤ Fintype.card V := (le_max_right _ _).trans hnRoute
  have hnPaths : S07V24.Explicit.oddPathOrder αmin κ ≤ Fintype.card V := (le_max_left _ _).trans hnRoute
  have hI := activeComps_interface hαmin h3min h4min hnI
  have hpaths : ∀ v x y,
      AdmPair (activeComps H.G H.lab F) (fun v C => IsBip H.G H.lab F (v,C))
        (colG H.G H.lab F) v x y →
      a * (Fintype.card V:ℝ)^m ≤ (pathsLen (link H.G H.lab F v) (m+1) x y).card := by
    rintro v x y ⟨C,hC,hx,hy,hxy,hcol⟩
    exact S07V24.Explicit.link_paths_of_interface_formula αmin κ hαmin hκ (link H.G H.lab F v)
      (Fintype.card V) hnPaths rfl C (IsBip H.G H.lab F (v,C)) (colG H.G H.lab F v)
      (hI v C hC) x y hx hy hxy hcol
  let Eextra : (V × V × V) → Finset V → Prop := fun j W =>
    AdmPair (activeComps H.G H.lab F) (fun v C => IsBip H.G H.lab F (v,C))
      (colG H.G H.lab F) j.1 j.2.1 j.2.2 ∧
      ((pathsIn (link H.G H.lab F j.1) m j.2.1 j.2.2 W).card:ℝ) <
        a * (Fintype.card V:ℝ)^m * q^m / 2
  have hExtra : ∀ j, @bprob V q univ (Eextra j)
      (fun W => Classical.propDecidable _) ≤ Real.exp (-(θPath * Fintype.card V)) := by
    rintro ⟨v,x,y⟩
    by_cases hadm : AdmPair (activeComps H.G H.lab F)
        (fun v C => IsBip H.G H.lab F (v,C)) (colG H.G H.lab F) v x y
    · refine (bprob_mono hq.le hq1 (E := Eextra (v,x,y))
        (E' := fun W => ((pathsIn (link H.G H.lab F v) m x y W).card:ℝ) <
          a * (Fintype.card V:ℝ)^m * q^m / 2)
        (iE' := fun W => inferInstance) (fun W hw => hw.2)).trans ?_
      refine (fam_paths ha hq hq1 hm hn0 (link H.G H.lab F v) x y (hpaths v x y hadm)).trans ?_
      exact le_rfl
    · rw [bprob_false (E := Eextra (v,x,y)) (fun W hw => hadm hw.1)]
      exact (Real.exp_pos _).le
  have hCountIdx : Fintype.card (V × V × V) ≤ Fintype.card V ^ 4 := by
    have hn1 : 1 ≤ Fintype.card V := hn0
    simp only [Fintype.card_prod]
    nlinarith [Nat.pow_le_pow_right hn1 (show 3 ≤ 4 by omega)]
  obtain ⟨hη,hη1,W,hWlo,hWhi,hPool,hHinges,hRaw,hGood⟩ :=
    hAuto H F α ε hαge hε hnAuto h3 hClean μ hμ hLoad hCountIdx Eextra hExtra
  refine ⟨hη,hη1,W,hWlo,hWhi,hPool,hHinges,hRaw,?_,?_⟩
  · intro Z B _ d hZ hB hd v x y hadm
    have hCount : a * (Fintype.card V:ℝ)^m * q^m / 2 ≤
        ((pathsIn (link H.G H.lab F v) m x y W).card:ℝ) :=
      le_of_not_gt (fun hc => hGood (v,x,y) ⟨hadm,hc⟩)
    have hwin := window_ok ha hq hm hn0 Z d hZ hd
    obtain ⟨p,hp,hW,hZ',hB'⟩ := pay_deterministic
      (link H.G H.lab F v) m x y W hCount Z B d hB (by convert hwin using 1 <;> ring)
    exact ⟨p,hp,by simpa using hW,by simpa using hZ',hB'⟩
  · intro v x y hadm
    exact le_of_not_gt (fun hc => hGood (v,x,y) ⟨hadm,hc⟩)

#print axioms automatic_native_clean_raw_paths_explicit

end TypedTriangle.Vortex.ExplicitRaw
