/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExplicitNativeOuterStart
public import RequestProject.TypedTriangle.ExplicitRawPathsPreparedVortex
@[expose] public section
open Finset Classical S07V24 S07V25 S07V45
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex.ExplicitRaw
open RawReference CorePaid ComponentRows

def outerInnerRootOrder (α C qInner qOuter : ℝ) (h Ninner Mrequired Nouter : ℕ) : ℕ :=
  nativeOuterRootOrder α C qOuter h Nouter (max 16 (rawRootOrder α qInner h Ninner Mrequired))

/-- A concrete outer sample followed by the constructed inner vortex. The
terminal bound is fixed before the outer rate and the outer prepared order.
The same preparation kernel, quotient counter and literal raw weights are
used on both sides of the outer sample. -/
theorem outer_inner_raw_prepared_vortex_explicit {I : Type} (F : Set (Multiset I))
    (α C : ℝ) (h : ℕ) (hα : 0 < α) (hh : 1 ≤ h) (hC : 0 < C) :
    ∀ qInner : ℝ, 0 < qInner → qInner ≤ 1/32 →
      let d := rawPreparationRank α h;
      let T := rawPreparationTorsion α h;
      let mInner := nativeInteriorCount (α/2) h;
      let aInner := nativeDensity (α/2) h;
      let mOuter := nativeInteriorCount (8*α) h;
      let aOuter := nativeDensity (8*α) h;
      let δOuter := nativeOuterAvoidBudget (8*α) h;
      let εRouteInner := nativeRoutePrecision (α/2) qInner h;
      ∀ β : ℕ → ℝ, (∀ j, 0 ≤ β j) →
        (∑ j ∈ range (d+(d+1)*Nat.log 2 T+1), β j) ≤
          min δOuter (rawPreparationTolerance α C h) →
      ∀ Ninner Mrequired : ℕ,
      let M := rawMinimumOrder α qInner h Ninner Mrequired;
      let nInner := rawRootOrder α qInner h Ninner Mrequired;
      let t := rawTerminalOrder α C qInner h Ninner Mrequired;
      ∀ qOuter : ℝ, 0 < qOuter → qOuter ≤ 1/32 →
      let εRouteOuter := windowRouteRate aOuter qOuter mOuter;
      ∀ Nouter : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I), outerInnerRootOrder α C qInner qOuter h Ninner Mrequired Nouter ≤ Fintype.card V →
        CommonNbrCond H F (8*α) → CleanHingeCond H F (8*α) h →
      ∀ μ : Finset V → ℝ, IsDiffuseSeed H F C μ →
      ∃ node : IntrinsicRawPreparedLayer H F α C β h Nouter (max 16 nInner) d T μ,
        letI : DecidableEq (Survivors node.trim) := Classical.decEq _
        ∃ W : Finset (Survivors node.trim), max 16 nInner ≤ W.card ∧
          16*W.card ≤ Fintype.card (Survivors node.trim) ∧
          qOuter*Fintype.card (Survivors node.trim)/2 ≤ W.card ∧
          (W.card:ℝ) < 2*qOuter*Fintype.card (Survivors node.trim) ∧
          (1-automaticRelativeError (Fintype.card (Survivors node.trim)))*qOuter*
            Fintype.card (Survivors node.trim) ≤ (W.card:ℝ) ∧
          (W.card:ℝ) < (1+automaticRelativeError (Fintype.card (Survivors node.trim)))*qOuter*
            Fintype.card (Survivors node.trim) ∧
          node.index ≤ physicalPotential (restrictedHost (restrictedHost H node.trim) (univ \ W)) F T ∧
          (∀ u v, u ≠ v → ∀ k, ({H.lab u,H.lab v,k} : Multiset I) ∈ F →
            (4*α)*Fintype.card V*qOuter/2 ≤ ((commonNbrs H k u v) ∩ liftVertexSet node.trim W).card) ∧
          (∀ v x y, OrigAdm H.G H.lab F v x y →
            aOuter*(Fintype.card V:ℝ)^mOuter*qOuter^mOuter/4 ≤
              (pathsIn (link H.G H.lab F v) mOuter x y (liftVertexSet node.trim W)).card) ∧
          S07V27.RouteProp H.G H.lab F (mOuter+1) εRouteOuter (liftVertexSet node.trim W) ∧
          ∃ chain : IntrinsicRawPathsPreparedVortex F α qInner C β h Ninner M d T mInner aInner
              εRouteInner t (restrictedHost (restrictedHost H node.trim) (univ \ W))
              (survivorSampledWeights (restrictedWeights μ node.trim) W qOuter),
            chain.HasRelativeWindows := by
  intro qInner hqInner hqInner32
  dsimp only
  let d := rawPreparationRank α h
  let T := rawPreparationTorsion α h
  let mInner := nativeInteriorCount (α/2) h
  let aInner := nativeDensity (α/2) h
  let mOuter := nativeInteriorCount (8*α) h
  let aOuter := nativeDensity (8*α) h
  let δOuter := nativeOuterAvoidBudget (8*α) h
  let εRouteInner := nativeRoutePrecision (α/2) qInner h
  intro β hβ hBudget Ninner Mrequired
  let M := rawMinimumOrder α qInner h Ninner Mrequired
  let nInner := rawRootOrder α qInner h Ninner Mrequired
  let t := rawTerminalOrder α C qInner h Ninner Mrequired
  have hBudgetInner := hBudget.trans (min_le_right _ _)
  have hInnerBuild {V : Type} [Fintype V] := intrinsic_raw_paths_prepared_vortex_explicit F α C h hα hh hC
    qInner hqInner hqInner32 β hβ hBudgetInner Ninner Mrequired (V := V)
  intro qOuter hqOuter hqOuter32
  intro Nouter
  have hOuterBuild {V : Type} [Fintype V] := native_outer_raw_start_explicit F α C h hα hC hh
    qOuter hqOuter hqOuter32 β hβ hBudget Nouter (max 16 nInner) (le_max_left _ _) (V := V)
  intro V _ H hn h3 hClean μ hSeed
  obtain ⟨node,W,hWmin,hShrink,hLow,hUp,hRelLow,hRelUp,h3Child,hCleanChild,hChildIndex,
    hNext,hRawChild,hPools,hPaths,hRoute⟩ := hOuterBuild H hn h3 hClean μ hSeed
  letI : DecidableEq (Survivors node.trim) := Classical.decEq _
  have hnChild : nInner ≤ Fintype.card (Survivors (univ \ W)) := by
    rw [CorePaid.card_survivors_compl W]
    exact (le_max_right _ _).trans hWmin
  obtain ⟨chain,hMetadata⟩ := hInnerBuild
    (restrictedHost (restrictedHost H node.trim) (univ \ W)) hnChild h3Child hCleanChild
    (survivorSampledWeights (restrictedWeights μ node.trim) W qOuter) hRawChild
  exact ⟨node,W,hWmin,hShrink,hLow,hUp,hRelLow,hRelUp,hNext,hPools,hPaths,hRoute,chain,hMetadata⟩

#print axioms outer_inner_raw_prepared_vortex_explicit
end TypedTriangle.Vortex.ExplicitRaw
