/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexRelativeRawPathsPreparedVortex
public import RequestProject.TypedTriangle.ExplicitGlobalRawPathsRichStep
public import RequestProject.TypedTriangle.ExplicitIntrinsicPreparation
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex
open S07V24 S07V25 ComponentRows RawReference

namespace ExplicitRaw

def rawPreparationTolerance (α C : ℝ) (h : ℕ) : ℝ :=
  min (Explicit.preparationTolerance (α/4) h)
    (min (α/(4*2^Nat.choose h 2)) (1/(8*max 1 (2*C))))

def rawPreparationRank (α : ℝ) (h : ℕ) : ℕ := Explicit.preparationRank (α/4) h

def rawPreparationTorsion (α : ℝ) (h : ℕ) : ℕ := Explicit.preparationTorsion (α/4) h

def rawRequiredGeometry (α q : ℝ) (h : ℕ) : ℝ :=
  let κ := α*q^h/4
  max ((8*((h:ℝ)+1))^4)
    (max ((32:ℝ)^4) (max (4/κ) (2*(1+(h:ℝ))*2^Nat.choose h 2/κ)))

def rawMinimumOrder (α q : ℝ) (h N Mrequired : ℕ) : ℕ :=
  max (max (Explicit.preparationOrder (α/4) h N) Mrequired)
    (max 1 (⌈rawRequiredGeometry α q h⌉₊+1))

def rawRootOrder (α q : ℝ) (h N Mrequired : ℕ) : ℕ :=
  2*rawMinimumOrder α q h N Mrequired

def rawTerminalOrder (α C q : ℝ) (h N Mrequired : ℕ) : ℝ :=
  let M := rawMinimumOrder α q h N Mrequired
  max (globalRawStepOrder α C q h (2*M)) M

theorem rawPreparationKernel_spec (α C : ℝ) (h : ℕ) (hα : 0 < α) (hC : 0 < C) :
    0 < rawPreparationTolerance α C h ∧ 1 ≤ rawPreparationTorsion α h ∧
    IntrinsicPreparationKernel (α/4) h (rawPreparationTolerance α C h)
      (rawPreparationRank α h) (rawPreparationTorsion α h) := by
  have hPrep := Explicit.preparationTolerance_pos (by positivity : 0 < α/4) h
  refine ⟨lt_min hPrep (lt_min (by positivity) (by positivity)),
    Explicit.preparationTorsion_pos (α/4) h, ?_⟩
  exact (Explicit.intrinsic_preparation_kernel_explicit (α/4) h (by positivity)).mono
    (min_le_left _ _)

theorem intrinsic_raw_paths_prepared_vortex_explicit {I : Type} (F : Set (Multiset I))
    (α₀ C : ℝ) (h : ℕ) (hα : 0 < α₀) (hh : 1 ≤ h) (hC : 0 < C) :
    ∀ q : ℝ, 0 < q → q ≤ 1/32 →
      let d := rawPreparationRank α₀ h;
      let T := rawPreparationTorsion α₀ h;
      let m := nativeInteriorCount (α₀/2) h;
      let a := nativeDensity (α₀/2) h;
      let εRoute := nativeRoutePrecision (α₀/2) q h;
      let L := d+(d+1)*Nat.log 2 T;
      ∀ β : ℕ → ℝ, (∀ j, 0 ≤ β j) →
      (∑ j ∈ range (L+1), β j) ≤ rawPreparationTolerance α₀ C h →
      ∀ N Mrequired : ℕ,
      let M := rawMinimumOrder α₀ q h N Mrequired;
      let t := rawTerminalOrder α₀ C q h N Mrequired;
      ∀ {V : Type} [Fintype V] (H : Host V I), rawRootOrder α₀ q h N Mrequired ≤ Fintype.card V →
        CommonNbrCond H F α₀ → CleanHingeCond H F α₀ h →
        ∀ μ : Finset V → ℝ,
          RawProfileAt H F C (globalRawProfileError 4 (max 1 (2*C)) β (Fintype.card V)
            (physicalPotential H F T)) μ →
          ∃ chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ,
            chain.HasRelativeWindows := by
  let D : ℝ := 2 ^ Nat.choose h 2
  have hD : 0 < D := by positivity
  let d := rawPreparationRank α₀ h
  let T := rawPreparationTorsion α₀ h
  let E : ℝ := max 1 (2 * C)
  have hE1 : 1 ≤ E := le_max_left _ _
  have hEC : 2 * C ≤ E := le_max_right _ _
  have hE : 0 < E := by linarith only [hE1]
  let m := nativeInteriorCount (α₀/2) h
  let a := nativeDensity (α₀/2) h
  let ε := rawPreparationTolerance α₀ C h
  intro q hq hq32
  dsimp only
  let εRoute := nativeRoutePrecision (α₀/2) q h
  let L := d+(d+1)*Nat.log 2 T
  intro β hβ hBudget N Mrequired
  change (∑ j ∈ range (L+1), β j) ≤ ε at hBudget
  let nPrep := Explicit.preparationOrder (α₀/4) h N
  have hPrepare := Explicit.preparation_at_explicit_order (α₀/4) h N (by positivity)
  have hQuot : ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
      nPrep ≤ Fintype.card V → CommonNbrCond H F (α₀/4) → HingeCond H F (α₀/4) h →
      Module.finrank ℤ (physQuot H F) ≤ d ∧ Nat.card (Submodule.torsion ℤ (physQuot H F)) ≤ T := by
    intro V I _ H F hn h3 h4
    have hEntry : Explicit.entryOrder (α₀/4) h ≤ Fintype.card V := (le_max_left _ _).trans hn
    have hnCmp : ExplicitSample.compressionOrder ((α₀/4)/2) h ≤ Fintype.card V := by
      have hd : 2*ExplicitSample.compressionOrder ((α₀/4)/2) h ≤ Fintype.card V :=
        (le_max_right _ _).trans hEntry
      omega
    exact ExplicitSample.physQuot_bounds_of_H3H4_explicit ((α₀/4)/2) h (by positivity) H F hnCmp
      (commonNbrCond_mono h3 (by linarith)) (hingeCond_mono h4 (by linarith))
  let κ : ℝ := α₀ * q ^ h / 4
  have hκ : 0 < κ := by dsimp [κ]; positivity
  let R : ℝ := max ((8 * ((h : ℝ) + 1)) ^ 4)
    (max ((32 : ℝ)^4) (max (4 / κ) (2 * (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 / κ)))
  let M := rawMinimumOrder α₀ q h N Mrequired
  have hMprep : nPrep ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hM1 : 1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hCeil : (⌈R⌉₊ : ℝ) ≤ M := by
    exact_mod_cast (show ⌈R⌉₊ ≤ M from (Nat.le_succ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hRM : R ≤ M := (Nat.le_ceil _).trans hCeil
  have hPower : (8 * ((h : ℝ) + 1)) ^ 4 ≤ M := (le_max_left _ _).trans hRM
  have hW1 : 3 < κ * M := by
    have hs : 4 / κ ≤ (M : ℝ) := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hRM
    have hs' := (div_le_iff₀ hκ).mp hs
    linarith only [hs']
  have hW2 : (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 ≤ κ / 2 * M := by
    have hs : 2 * (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 / κ ≤ (M : ℝ) :=
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hRM
    have hs' := (div_le_iff₀ hκ).mp hs
    nlinarith only [hs']
  have hBudgetPrep := hBudget.trans (min_le_left _ _)
  have hDebt : D * (∑ j ∈ range (L + 1), β j) ≤ α₀ / 4 := by
    have hs := (le_div_iff₀ (by positivity : 0 < 4 * D)).mp (hBudget.trans ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith only [hs]
  have hFloor (n : ℝ) (r : ℕ) (hn : (M : ℝ) ≤ n) (hr : r ≤ L) :
      α₀ / 2 ≤ globalGeometryFloor α₀ h D β n r := by
    have hp : (∑ j ∈ range r, β j) ≤ ∑ j ∈ range (L + 1), β j :=
      sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (by intro j _ _; exact hβ j)
    exact globalGeometryFloor_half_le α₀ D h β n r hα.le (hPower.trans hn)
      ((mul_le_mul_of_nonneg_left hp hD.le).trans hDebt)
  have hRawDebt : E * (∑ j ∈ range (L + 1), β j) ≤ 1 / 8 := by
    have hs := (le_div_iff₀ (by positivity : 0 < 8 * E)).mp
      (hBudget.trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [hs]
  have hRawPower : (32 : ℝ)^4 ≤ M :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hRM
  have hRawCap (n : ℝ) (r : ℕ) (hn : (M : ℝ) ≤ n) (hr : r ≤ L) :
      globalRawProfileError 4 E β n r ≤ 1 / 4 := by
    have he := automaticRelativeError_le_of_power_bound 32 n (by norm_num) (hRawPower.trans hn)
    norm_num at he
    have hp : (∑ j ∈ range r, β j) ≤ ∑ j ∈ range (L + 1), β j :=
      sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (by intro j _ _; exact hβ j)
    apply globalRawProfileError_le_cap 4 E (1 / 4) β n r
    · linarith only [he]
    · norm_num
      exact (mul_le_mul_of_nonneg_left hp hE.le).trans hRawDebt
  let Ns := globalRawStepOrder α₀ C q h (2*M)
  have hStep {V J : Type} [Fintype V] := global_clean_raw_paths_rich_step_explicit α₀ C D h hα hh hC hD.le
    q hq hq32 (2*M) L β (by omega) hβ hDebt (V := V) (I := J)
  let t : ℝ := max Ns M
  have hAll : ∀ n : ℕ, ∀ {V : Type} [Fintype V] (H : Host V I), Fintype.card V = n →
      2 * M ≤ n → physicalPotential H F T ≤ L →
      CommonNbrCond H F (globalGeometryFloor α₀ h D β n (physicalPotential H F T)) →
      CleanHingeCond H F (globalGeometryFloor α₀ h D β n (physicalPotential H F T)) h →
      ∀ μ : Finset V → ℝ, RawProfileAt H F C (globalRawProfileError 4 E β n (physicalPotential H F T)) μ →
      ∃ chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ, chain.HasRelativeWindows := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ H hcard hMin hp h3 hClean μ hRaw
      have hMcur : M ≤ Fintype.card V := by omega
      have hMcurR : (M : ℝ) ≤ Fintype.card V := by exact_mod_cast hMcur
      have hFloorCur := hFloor (Fintype.card V) (physicalPotential H F T) hMcurR hp
      rw [← hcard] at h3 hClean hRaw
      obtain ⟨r, hr, A, hpEnter, hpA, hCost, hHalf, h3A, hCleanA, hPc⟩ :=
        hPrepare β hβ hBudgetPrep H F _ (hMprep.trans hMcur) (by linarith only [hFloorCur]) h3 hClean
      change r ≤ L at hr
      change physicalPotential H F T ≤ r at hpEnter
      change physicalPotential (restrictedHost H A) F T = r at hpA
      change (A.card:ℝ) ≤ Fintype.card V*((∑ j ∈ range r, β j)-
        ∑ j ∈ range (physicalPotential H F T), β j) at hCost
      letI : DecidableEq (Survivors A) := Classical.decEq _
      have hMA : M ≤ Fintype.card (Survivors A) := by
        have hnR : (2 : ℝ) * M ≤ Fintype.card V := by exact_mod_cast (show 2 * M ≤ Fintype.card V by omega)
        have hOut : (M : ℝ) ≤ Fintype.card (Survivors A) := by linarith
        exact_mod_cast hOut
      have hMAR : (M : ℝ) ≤ Fintype.card (Survivors A) := by exact_mod_cast hMA
      have hSize : Fintype.card (Survivors A) ≤ Fintype.card V := by
        have hc := card_survivors_add_card A
        omega
      have hSizeR : (Fintype.card (Survivors A) : ℝ) ≤ Fintype.card V := by exact_mod_cast hSize
      have hAPos : (0 : ℝ) < Fintype.card (Survivors A) := by
        exact_mod_cast (show 0 < Fintype.card (Survivors A) by omega)
      have hTrim := globalGeometryFloor_trim α₀ D h β hα.le (Fintype.card V)
        (Fintype.card (Survivors A)) (physicalPotential H F T) r hAPos hSizeR
      have h3Prepared := commonNbrCond_mono h3A hTrim
      have hCleanPrepared := hCleanA.mono hTrim
      have hPreparedFloor := hFloor (Fintype.card (Survivors A)) r hMAR hr
      have h3base := commonNbrCond_mono h3Prepared (show α₀ / 4 ≤ _ by linarith only [hPreparedFloor,hα])
      have hCleanbase := hCleanPrepared.mono (show α₀ / 4 ≤ _ by linarith only [hPreparedFloor,hα])
      have hRawCapCur := hRawCap (Fintype.card V) (physicalPotential H F T) hMcurR hp
      have hnPos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
      let debt := (∑ j ∈ range r, β j) - ∑ j ∈ range (physicalPotential H F T), β j
      have hDebt0 : 0 ≤ debt := by
        have hs := sum_le_sum_of_subset_of_nonneg (range_mono hpEnter) (by intro j _ _; exact hβ j)
        dsimp [debt]
        linarith only [hs]
      have hDebtCap : debt ≤ ε := by
        have hs : (∑ j ∈ range r, β j) ≤ ∑ j ∈ range (L + 1), β j :=
          sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (by intro j _ _; exact hβ j)
        have hp0 : 0 ≤ ∑ j ∈ range (physicalPotential H F T), β j := sum_nonneg (by intro j _; exact hβ j)
        dsimp [debt]
        linarith only [hs,hp0,hBudget]
      have hDebt1 : debt < 1 := by
        have hεcap : ε ≤ 1 / (8 * E) := (min_le_right _ _).trans (min_le_right _ _)
        have hs := (le_div_iff₀ (by positivity : 0 < 8 * E)).mp (hDebtCap.trans hεcap)
        have hPay := mul_le_mul_of_nonneg_right hE1 hDebt0
        nlinarith only [hs,hPay]
      have hRawPrepared := raw_profile_restrict_global H F C E β μ (physicalPotential H F T) r A debt
        hC hE1 hEC hβ hnPos hRaw (by linarith only [hRawCapCur]) hDebt0 hDebt1
        (by dsimp [debt]; nlinarith only [hCost]) le_rfl
      have hRawCapPrepared := hRawCap (Fintype.card (Survivors A)) r hMAR hr
      let baseNode : IntrinsicPreparedLayer H F α₀ β h N M d T :=
        ⟨A, r, hr, hpEnter, hpA, hCost, h3base, hCleanbase, hPc, hMA⟩
      let node : IntrinsicRawPreparedLayer H F α₀ C β h N M d T μ :=
        ⟨baseNode, hRawPrepared, hRawCapPrepared⟩
      by_cases hStop : (Fintype.card (Survivors A) : ℝ) ≤ t
      · exact ⟨.terminal node hStop, True.intro⟩
      · have hnStep : Ns ≤ (Fintype.card (Survivors A) : ℝ) :=
          (le_max_left _ _).trans (lt_of_not_ge hStop).le
        let μA := restrictedWeights μ A
        let ρA := globalRawProfileError 4 E β (Fintype.card (Survivors A)) r
        have hμA : ∀ S, IsAllowed (restrictedHost H A) F S →
            0 ≤ μA S ∧ μA S ≤ (2 * C) / Fintype.card (Survivors A) := by
          intro S hS
          have hs := hRawPrepared.1 S hS
          have hLow : 0 ≤ ((1 - ρA) / C) / Fintype.card (Survivors A) := by
            apply div_nonneg (div_nonneg (by dsimp [ρA]; linarith only [hRawCapPrepared]) hC.le) (by positivity)
          have hUpper : (1 + ρA) * C ≤ 2 * C :=
            mul_le_mul_of_nonneg_right (by dsimp [ρA]; linarith only [hRawCapPrepared]) hC.le
          exact ⟨hLow.trans hs.1, hs.2.trans (div_le_div_of_nonneg_right hUpper (by positivity))⟩
        obtain ⟨hηpos, hηlt, W, hWmin, hShrink, h3W, hCleanW, hSizes, hProfile, hRoute, hPaths, hPools, hInter⟩ :=
          hStep (restrictedHost H A) F r hr hnStep h3Prepared hCleanPrepared
            ρA (by dsimp [ρA]; linarith only [hRawCapPrepared]) μA hμA hRawPrepared.2
        have hWM : M ≤ W.card := by omega
        have hWMR : (M : ℝ) ≤ W.card := by exact_mod_cast hWM
        have hChildFloor := hFloor W.card r hWMR hr
        have hChild3 := commonNbrCond_mono h3W (show α₀ / 4 ≤ _ by linarith only [hChildFloor,hα])
        have hChild4 := hingeCond_mono hCleanW.hingeCond (show α₀ / 4 ≤ _ by linarith only [hChildFloor,hα])
        have hChildOrder : nPrep ≤ Fintype.card (Survivors (univ \ W)) := by
          rw [CorePaid.card_survivors_compl]
          exact hMprep.trans hWM
        have hChildQuot := hQuot (restrictedHost (restrictedHost H A) (univ \ W)) F
          hChildOrder hChild3 hChild4
        have hChildIndex := physicalPotential_le _ F d T hChildQuot.1 hChildQuot.2
        have hParentQuot := hQuot (restrictedHost H A) F (hMprep.trans hMA) h3base hCleanbase.hingeCond
        have hw1 : 3 < κ * W.card := hW1.trans_le (mul_le_mul_of_nonneg_left hWMR hκ.le)
        have hw2 : (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 ≤ κ / 2 * W.card :=
          hW2.trans (mul_le_mul_of_nonneg_left hWMR (by positivity))
        have hNext := physicalPotential_sample_mono (restrictedHost H A) F W κ h T hκ
          hInter hw1 hw2 hParentQuot.2
        rw [hpA] at hNext
        have hPrefix : (∑ j ∈ range r, β j) ≤
            ∑ j ∈ range (physicalPotential (restrictedHost (restrictedHost H A) (univ \ W)) F T), β j :=
          sum_le_sum_of_subset_of_nonneg (range_mono hNext) (by intro j _ _; exact hβ j)
        have hWeaken : globalGeometryFloor α₀ h D β W.card
            (physicalPotential (restrictedHost (restrictedHost H A) (univ \ W)) F T) ≤
            globalGeometryFloor α₀ h D β W.card r := by
          dsimp [globalGeometryFloor]
          nlinarith only [mul_le_mul_of_nonneg_left hPrefix hD.le]
        have hShrinkA : 16 * W.card ≤ Fintype.card (Survivors A) := by
          simpa only [← Nat.card_eq_fintype_card] using hShrink
        have hWlt : W.card < n := by omega
        have hRawChild := raw_profile_sample_global (restrictedHost H A) F C E q β μA r
          (physicalPotential (restrictedHost (restrictedHost H A) (univ \ W)) F T) W
          hC hE.le hq hβ hAPos hηlt hRawPrepared (by linarith only [hRawCapPrepared]) hSizes.1 hSizes.2.le
          hShrink hNext hProfile
        obtain ⟨tail, hTailRel⟩ := ih W.card hWlt (restrictedHost (restrictedHost H A) (univ \ W))
          (CorePaid.card_survivors_compl W) hWmin hChildIndex
          (by simpa only [CorePaid.card_survivors_compl] using commonNbrCond_mono h3W hWeaken)
          (by simpa only [CorePaid.card_survivors_compl] using hCleanW.mono hWeaken)
          (survivorSampledWeights μA W q)
          (by simpa only [CorePaid.card_survivors_compl] using hRawChild)
        have hRawDebtNonneg : 0 ≤ E * ∑ j ∈ range r, β j :=
          mul_nonneg hE.le (sum_nonneg (by intro j _; exact hβ j))
        have hEtaHalf : automaticRelativeError (Fintype.card (Survivors A)) ≤ 1 / 2 := by
          have hc := hRawCapPrepared
          dsimp only [globalRawProfileError] at hc
          linarith only [hc,hRawDebtNonneg]
        have hSizeLo := hSizes.1
        have hSizeHi := hSizes.2
        change (1 - automaticRelativeError (Fintype.card (Survivors A))) * q *
          Fintype.card (Survivors A) ≤ (W.card : ℝ) at hSizeLo
        change (W.card : ℝ) < (1 + automaticRelativeError (Fintype.card (Survivors A))) * q *
          Fintype.card (Survivors A) at hSizeHi
        have hLowerRel : q * Fintype.card (Survivors A) / 2 ≤ (W.card : ℝ) := by
          have hs := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤
            1 - automaticRelativeError (Fintype.card (Survivors A)) by linarith only [hEtaHalf])
            (mul_nonneg hq.le hAPos.le)
          nlinarith only [hs,hSizeLo]
        have hUpperRel : (W.card : ℝ) < 2 * q * Fintype.card (Survivors A) := by
          have hs := mul_lt_mul_of_pos_right (show
            1 + automaticRelativeError (Fintype.card (Survivors A)) < 2 by linarith only [hEtaHalf])
            (mul_pos hq hAPos)
          exact hSizeHi.trans (by convert hs using 1 <;> ring)
        let metadata : RawSampleMetadata (restrictedHost H A) F α₀ q W :=
          ⟨hLowerRel, hUpperRel, hSizeLo, hSizeHi, hPools⟩
        exact ⟨.descend node W hWmin hShrink hRoute hPaths hInter hNext tail, metadata, hTailRel⟩
  intro V _ H hn h3 hClean μ hRawInitial
  change 2*M ≤ Fintype.card V at hn
  have hOrder : nPrep ≤ Fintype.card V := hMprep.trans (by omega)
  have hBounds := hQuot H F hOrder
    (commonNbrCond_mono h3 (show α₀ / 4 ≤ α₀ by linarith only [hα]))
    (hingeCond_mono hClean.hingeCond (show α₀ / 4 ≤ α₀ by linarith only [hα]))
  have hp := physicalPotential_le H F d T hBounds.1 hBounds.2
  have hNonneg : 0 ≤ D * ∑ j ∈ range (physicalPotential H F T), β j :=
    mul_nonneg hD.le (sum_nonneg (by intro j _; exact hβ j))
  have hFloorLe : globalGeometryFloor α₀ h D β (Fintype.card V) (physicalPotential H F T) ≤ α₀ := by
    exact (sub_le_self _ hNonneg).trans (geometryFloor_le α₀ h _ hα.le)
  exact hAll (Fintype.card V) H rfl hn hp (commonNbrCond_mono h3 hFloorLe)
    (hClean.mono hFloorLe) μ hRawInitial

#print axioms rawPreparationKernel_spec
#print axioms intrinsic_raw_paths_prepared_vortex_explicit
end ExplicitRaw
end TypedTriangle.Vortex
