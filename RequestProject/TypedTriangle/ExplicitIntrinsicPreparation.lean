module
public import RequestProject.TypedTriangle.ExplicitVertexPreparation
public import RequestProject.TypedTriangle.VortexIntrinsicPreparationKernel
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex.Explicit
open ExplicitGeometry ExplicitSample

def coreTolerance (α : ℝ) (h : ℕ) : ℝ :=
  min (min (deletionBudget α h) (nestedBudget α h)) (1 / 2)
def coreOrder (α : ℝ) (h N : ℕ) : ℕ := max (nestedOrder α h) (2 * N)
def preparationTolerance (α : ℝ) (h : ℕ) : ℝ :=
  min (min (entryTolerance α h) (coreTolerance α h))
    (min (1 / 2) (α / (2 * 2 ^ Nat.choose h 2)))
def preparationOrder (α : ℝ) (h N : ℕ) : ℕ :=
  max (entryOrder α h) (2 * max (entryOrder α h) (coreOrder α h N))

theorem coreTolerance_pos {α : ℝ} (hα : 0 < α) (h : ℕ) :
    0 < coreTolerance α h :=
  lt_min (lt_min (deletionBudget_spec hα h).1 (nestedBudget_pos hα h)) (by norm_num)

theorem preparationTolerance_pos {α : ℝ} (hα : 0 < α) (h : ℕ) :
    0 < preparationTolerance α h :=
  lt_min (lt_min (nestedBudget_pos hα h) (coreTolerance_pos hα h))
    (lt_min (by norm_num) (by positivity))

theorem preparedCore_on_stable_host_explicit (α : ℝ) (h N : ℕ) (hα : 0 < α)
    (β : ℝ) (hβ : β ≤ coreTolerance α h)
    {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (hn : coreOrder α h N ≤ Fintype.card V)
    (h3 : CommonNbrCond H F α) (h4 : HingeCond H F α h)
    (hStable : ∀ Z : Finset V, (Z.card : ℝ) ≤ β * Fintype.card V →
      Function.Injective (quotMap (F := F) (vertexDeleted_le H Z) rfl)) :
    Dispersal.PreparedCore H.G H.lab F (α / 2) h N β := by
  obtain ⟨_, _, hGeom⟩ := deletionBudget_spec hα h
  have hβδ : β ≤ deletionBudget α h :=
    hβ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hβWin : β ≤ nestedBudget α h :=
    hβ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hβhalf : β ≤ 1 / 2 := hβ.trans (min_le_right _ _)
  have hSmall (Z : Finset V) (hZ : (Z.card : ℝ) ≤ β * Fintype.card V) :
      (Z.card : ℝ) ≤ deletionBudget α h * Fintype.card V :=
    hZ.trans (mul_le_mul_of_nonneg_right hβδ (by positivity))
  have hGeo (Z : Finset V) (hZ : (Z.card : ℝ) ≤ β * Fintype.card V) :=
    original_geometry_restrictedHost hα.le h3 h4 Z
      (hGeom (by positivity) (hSmall Z hZ)).1 (hGeom (by positivity) (hSmall Z hZ)).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Z hZ
    exact (prepared_commonNbrCond_iff _ _ _).mp (hGeo Z hZ).1
  · intro Z hZ
    exact (prepared_hingeCond_iff _ _ _ _).mp (hGeo Z hZ).2
  · intro Z hZ
    have hHalf : (Z.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 := by
      have hs := mul_le_mul_of_nonneg_right hβhalf (by positivity : (0 : ℝ) ≤ Fintype.card V)
      linarith
    have hc := card_survivors_add_card Z
    have hN : 2 * N ≤ Fintype.card V := (le_max_right _ _).trans hn
    have hHalfN : 2 * Z.card ≤ Fintype.card V := by
      exact_mod_cast (by linarith : (2 : ℝ) * Z.card ≤ Fintype.card V)
    have hOrder : N ≤ Fintype.card (Survivors Z) := by omega
    exact hOrder
  · intro Z hZ y hy hzero
    have hZWin : (Z.card : ℝ) ≤ nestedBudget α h * Fintype.card V :=
      hZ.trans (mul_le_mul_of_nonneg_right hβWin (by positivity))
    obtain ⟨_, _, hw1, hw2⟩ := nested_windows_explicit α h hα (∅ : Finset V) Z
      ((le_max_left _ _).trans hn) (by
        simp only [card_empty, Nat.cast_zero]
        exact mul_nonneg (nestedBudget_pos hα h).le (Nat.cast_nonneg _)) hZWin
    have hSurvEmpty : Fintype.card (Survivors (∅ : Finset V)) = Fintype.card V := by
      simpa only [card_empty, Nat.add_zero] using card_survivors_add_card (∅ : Finset V)
    rw [hSurvEmpty] at hw1 hw2
    have hw1' : (Z.card : ℝ) + 2 < α * Fintype.card V := by
      have hNonneg : (0 : ℝ) ≤ α * Fintype.card V := mul_nonneg hα.le (by positivity)
      linarith
    have hw2' : ((Z.card : ℝ) + h) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V := by
      have hNonneg : (0 : ℝ) ≤ α * Fintype.card V := mul_nonneg hα.le (by positivity)
      nlinarith
    have hp := (quotMap_vertexDeleted_injective_iff hα h3 h4 Z hw1' hw2').mp (hStable Z hZ)
    exact edgeRestrict_mem_lattice H F Z (hp y hy hzero)

/-- The actual preparation statement at a specified host-independent order. -/
theorem preparation_at_explicit_order (α : ℝ) (h N : ℕ) (hα : 0 < α) :
    let d := preparationRank α h
    let T := preparationTorsion α h
    let D : ℝ := 2 ^ Nat.choose h 2
    let L := d + (d + 1) * Nat.log 2 T
    ∀ β : ℕ → ℝ, (∀ j, 0 ≤ β j) →
      (∑ j ∈ range (L + 1), β j) ≤ preparationTolerance α h →
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (γ : ℝ),
        preparationOrder α h N ≤ Fintype.card V → 2 * α ≤ γ →
        CommonNbrCond H F γ → CleanHingeCond H F γ h →
        ∃ r ≤ L, ∃ A : Finset V,
          physicalPotential H F T ≤ r ∧ physicalPotential (restrictedHost H A) F T = r ∧
          let debt := (∑ j ∈ range r, β j) - ∑ j ∈ range (physicalPotential H F T), β j
          (A.card : ℝ) ≤ Fintype.card V * debt ∧
          (Fintype.card V : ℝ) / 2 ≤ Fintype.card (Survivors A) ∧
          CommonNbrCond (restrictedHost H A) F (γ - D * debt) ∧
          CleanHingeCond (restrictedHost H A) F (γ - D * debt) h ∧
          Dispersal.PreparedCore (restrictedHost H A).G (restrictedHost H A).lab F (α / 2) h N (β r) := by
  dsimp only
  let d := preparationRank α h
  let T := preparationTorsion α h
  let D : ℝ := 2 ^ Nat.choose h 2
  let ε := preparationTolerance α h
  let L := d + (d + 1) * Nat.log 2 T
  have hD : 0 < D := by positivity
  have hD1 : 1 ≤ D := one_le_pow₀ (by norm_num)
  intro β hβ hBudget V I _ H F γ hn hγ h3 hClean
  have h3base := commonNbrCond_mono h3 (show α ≤ γ by linarith)
  have h4base := hingeCond_mono hClean.hingeCond (show α ≤ γ by linarith)
  have hBudgetEntry : (∑ j ∈ range (L + 1), β j) ≤ entryTolerance α h :=
    hBudget.trans ((min_le_left _ _).trans (min_le_left _ _))
  obtain ⟨r, hr, A, hp₀r, hpA, hA, hStable⟩ := intrinsic_first_entry_explicit α h hα
    β hβ hBudgetEntry H F ((le_max_left _ _).trans hn) h3base h4base
  change r ≤ L at hr
  let debt := (∑ j ∈ range r, β j) - ∑ j ∈ range (physicalPotential H F T), β j
  have hDebt0 : 0 ≤ debt := by
    have hs := sum_le_sum_of_subset_of_nonneg (range_mono hp₀r) (by intro j _ _; exact hβ j)
    dsimp [debt]
    linarith
  have hDebtε : debt ≤ ε := by
    have hs : (∑ j ∈ range r, β j) ≤ ∑ j ∈ range (L + 1), β j :=
      sum_le_sum_of_subset_of_nonneg (range_mono (show r ≤ L + 1 by omega))
        (by intro j _ _; exact hβ j)
    have hPrior : 0 ≤ ∑ j ∈ range (physicalPotential H F T), β j :=
      sum_nonneg (by intro j _; exact hβ j)
    dsimp [debt]
    linarith
  have hLoss : D * debt ≤ α / 2 := by
    have hcap : ε ≤ α / (2 * D) := (min_le_right _ _).trans (min_le_right _ _)
    have hc := (le_div_iff₀ (by positivity : 0 < 2 * D)).mp (hDebtε.trans hcap)
    nlinarith
  have hResultNonneg : 0 ≤ γ - D * debt := by linarith
  have hCleanA := clean_hinge_after_vertex_deletion H F γ (D * debt) h A hClean hResultNonneg (by
    have hs := mul_le_mul_of_nonneg_right hA hD.le
    dsimp only [D] at hs ⊢
    nlinarith)
  have h3A := commonNbr_after_vertex_deletion_additive H F γ (D * debt) A h3 hResultNonneg (by
    have hd := mul_le_mul_of_nonneg_right hD1 hDebt0
    have hs := mul_le_mul_of_nonneg_right hd (by positivity : (0 : ℝ) ≤ Fintype.card V)
    nlinarith [hA])
  have hαA : α ≤ γ - D * debt := by linarith
  have h3Abase := commonNbrCond_mono h3A hαA
  have h4Abase := hingeCond_mono hCleanA.hingeCond hαA
  have hAhalf : (A.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 := by
    have hcap : ε ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hs := mul_le_mul_of_nonneg_left (hDebtε.trans hcap) (by positivity : (0 : ℝ) ≤ Fintype.card V)
    nlinarith [hA]
  have hcR : (Fintype.card (Survivors A) : ℝ) + A.card = Fintype.card V := by
    exact_mod_cast card_survivors_add_card A
  have hHalf : (Fintype.card V : ℝ) / 2 ≤ Fintype.card (Survivors A) := by linarith
  have hLarge : max (entryOrder α h) (coreOrder α h N) ≤ Fintype.card (Survivors A) := by
    have hIn : 2 * max (entryOrder α h) (coreOrder α h N) ≤ Fintype.card V :=
      (le_max_right _ _).trans hn
    have hInR : (2 : ℝ) * max (entryOrder α h) (coreOrder α h N) ≤ Fintype.card V := by
      exact_mod_cast hIn
    exact_mod_cast (show ((max (entryOrder α h) (coreOrder α h N) : ℕ) : ℝ) ≤
      Fintype.card (Survivors A) by linarith)
  have hβrε : β r ≤ ε :=
    (single_le_sum (by intro j _; exact hβ j) (mem_range.mpr (show r < L + 1 by omega))).trans hBudget
  have hβrPc : β r ≤ coreTolerance α h := hβrε.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hActualStable := intrinsic_stability_on_actual_host H F A (β r) hStable
  have hPrepared := preparedCore_on_stable_host_explicit α h N hα (β r) hβrPc
    (restrictedHost H A) F ((le_max_right _ _).trans hLarge) h3Abase h4Abase hActualStable
  exact ⟨r, hr, A, hp₀r, hpA, hA, hHalf, h3A, hCleanA, hPrepared⟩

theorem preparationTorsion_pos (α : ℝ) (h : ℕ) : 1 ≤ preparationTorsion α h :=
  physicalTorsionBound_pos (α / 2) h

/-- Compatibility with the existing preparation interface. The preceding
    theorem retains the specified threshold for quantitative consumers. -/
theorem intrinsic_preparation_kernel_explicit (α : ℝ) (h : ℕ) (hα : 0 < α) :
    IntrinsicPreparationKernel α h (preparationTolerance α h)
      (preparationRank α h) (preparationTorsion α h) := by
  dsimp only [IntrinsicPreparationKernel]
  intro N
  refine ⟨preparationOrder α h N, ?_, preparation_at_explicit_order α h N hα⟩
  intro V I _ H F hn h3 h4
  have hEntry : entryOrder α h ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hDouble : 2 * compressionOrder (α / 2) h ≤ Fintype.card V :=
    (le_max_right _ _).trans hEntry
  have hnCmp : compressionOrder (α / 2) h ≤ Fintype.card V := by omega
  exact physQuot_bounds_of_H3H4_explicit (α / 2) h (by positivity) H F hnCmp
    (commonNbrCond_mono h3 (by linarith)) (hingeCond_mono h4 (by linarith))

#print axioms preparedCore_on_stable_host_explicit
#print axioms preparation_at_explicit_order
#print axioms intrinsic_preparation_kernel_explicit
end TypedTriangle.Vortex.Explicit
