module
public import RequestProject.TypedTriangle.ExplicitPaidPreparedCore
public import RequestProject.TypedTriangle.ExplicitPreparedSmooth
public import RequestProject.TypedTriangle.VortexExactPaidSmoothParameters
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex.Explicit
open ExplicitPaid

def paidDensity (α : ℝ) (h : ℕ) : ℝ := min (α / 2) (S07V49.hingeConstB α 1 h)
def paidHingeOrder (h : ℕ) : ℕ := 2 * h - 3
def paidPreparedOrder (α : ℝ) (h : ℕ) : ℕ :=
  NativeSmooth.Explicit.preparedOrder (paidDensity α h) (paidHingeOrder h)
def paidInverseOrder (α : ℝ) (h : ℕ) : ℕ :=
  NativeSmooth.Explicit.inverseOrder (paidDensity α h) (paidHingeOrder h)
def paidInverseCost (α β : ℝ) (h : ℕ) : ℝ :=
  max (NativeSmooth.Explicit.inverseCost (paidDensity α h) (min β (1 / 2)) (paidHingeOrder h))
    (1 / paidBudget α h)

theorem paidDensity_pos {α : ℝ} (h : ℕ) (hα : 0 < α) (hh : 6 ≤ h) : 0 < paidDensity α h := by
  exact lt_min (by positivity) (S07V49.hingeConstB_pos hα (by norm_num) (by omega))

theorem paidInverseCost_pos {α : ℝ} (β : ℝ) (h : ℕ) (hα : 0 < α) : 0 < paidInverseCost α β h :=
  lt_of_lt_of_le (div_pos (by norm_num) (paidBudget_pos h hα)) (le_max_right _ _)

theorem paidInverseCost_budget {α : ℝ} (β : ℝ) (h : ℕ) (hα : 0 < α) :
    1 ≤ paidInverseCost α β h * paidBudget α h := by
  have hη := paidBudget_pos h hα
  have hb := mul_le_mul_of_nonneg_right
    (le_max_right (NativeSmooth.Explicit.inverseCost (paidDensity α h)
      (min β (1 / 2)) (paidHingeOrder h)) (1 / paidBudget α h)) hη.le
  simpa only [paidInverseCost, div_mul_cancel₀ 1 hη.ne'] using hb

/-- Dense ambient physicality transfers to the child's exact integer lattice
    at the specified sparse-deletion threshold. -/
theorem intrinsic_dense_child_explicit (α : ℝ) (h : ℕ) (hα : 0 < α)
    {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (hn : latticeOrder α ≤ Fintype.card V)
    (h3 : CommonNbrCond H F α) (h4 : HingeCond H F α h)
    (E : Finset (Sym2 V)) (hE : E ⊆ edges H) (hPhys : IsPhysical H F E)
    (hsmall : ∀ v, (degIn (edges H \ E) v : ℝ) ≤ latticeBudget α h * Fintype.card V) :
    IsPhysical (subHost H E) F (edges (subHost H E)) := by
  let B := edges H \ E
  have hzero : ∀ e ∈ B, ind E e = 0 := by
    intro e he
    simp only [B, mem_sdiff] at he
    simp [ind, he.2]
  have hx := (sparse_edge_deletion_host_explicit α h hα V I H F hn h3 h4 B hsmall (ind E)).mpr
    ⟨hPhys, hzero⟩
  have hDiff : edges H \ B = E := by
    dsimp [B]
    ext e
    have hh : e ∈ E → e ∈ edges H := fun he => hE he
    simp only [mem_sdiff]
    tauto
  change ind (edges (subHost H E)) ∈ lattice (subHost H E) F
  rw [Residual.edges_subHost_eq hE]
  rwa [hDiff] at hx

theorem paid_reference_cap_explicit (α : ℝ) (h : ℕ) (hα : 0 < α) (hh : 6 ≤ h) :
    PaidReferenceCap α h (paidBudget α h) (paidOrder α h) := by
  intro V I _ J F hn h3 h4 E Y D hD hY hYPhys hDis hHole
  dsimp only
  have hE : E ⊆ edges J := by
    intro e he
    obtain ⟨T, hT, heT⟩ := hD.exists_mem he
    exact triEdges_subset_edges (hD.1 T hT) heT
  have hη := paidBudget_pos h hα
  have hCapG : paidBudget α h ≤ geometryBudget α h := by
    have hg := geometryBudget_pos h hα
    have hc : paidBudget α h ≤ geometryBudget α h / 2 := min_le_left _ _
    linarith
  have hCapL : paidBudget α h ≤ latticeBudget α h := by
    have hl := latticeBudget_pos h hα
    have hc : paidBudget α h ≤ latticeBudget α h / 2 := min_le_right _ _
    linarith
  let Echild := E ∪ Y
  let B := edges J \ Echild
  let d := ⌊paidBudget α h * Fintype.card V⌋₊
  have hEchild : Echild ⊆ edges J := union_subset hE hY
  have hBsub : B ⊆ edges J := sdiff_subset
  have hBhole : B ⊆ edges J \ E := by
    intro e he
    exact mem_sdiff.mpr ⟨(mem_sdiff.mp he).1, fun hc => (mem_sdiff.mp he).2 (mem_union_left _ hc)⟩
  have hBReal : ∀ v, (SparseEdge.degIn B v : ℝ) ≤ paidBudget α h * Fintype.card V := by
    intro v
    have hc := card_le_card (filter_subset_filter (p := fun e => v ∈ e) hBhole)
    exact (show (SparseEdge.degIn B v : ℝ) ≤ SparseEdge.degIn (edges J \ E) v by
      exact_mod_cast hc).trans (hHole v)
  have hBDeg : ∀ v, SparseEdge.degIn B v ≤ d := fun v => Nat.le_floor (hBReal v)
  have hd : (d : ℝ) ≤ paidBudget α h * Fintype.card V := Nat.floor_le (by positivity)
  have hRecover : edges J \ B = Echild := by
    dsimp only [B]
    ext e
    simp only [mem_sdiff]
    have he : e ∈ Echild → e ∈ edges J := fun hp => hEchild hp
    tauto
  have hGeometry := geometry_after_edge_payment_explicit α h hα hh J F B d
    ((le_max_left _ _).trans hn) h3 h4 hBsub hBDeg
    (hd.trans (mul_le_mul_of_nonneg_right hCapG (Nat.cast_nonneg _)))
  rw [hRecover] at hGeometry
  have hPhys : IsPhysical (subHost J Echild) F (edges (subHost J Echild)) :=
    CatalogNative.intrinsic_H2_of_physical_reference_and_mode J F E Y (paidBudget α h)
      hE hY (isPhysical_of_isDecomposition hD) hYPhys hDis hHole (by
        intro A hA hAPhys hASmall
        exact intrinsic_dense_child_explicit α h hα J F ((le_max_right _ _).trans hn) h3 h4
          A hA hAPhys (fun v => (hASmall v).trans
            (mul_le_mul_of_nonneg_right hCapL (Nat.cast_nonneg _))))
  exact ⟨hPhys, commonNbrCond_mono hGeometry.1 (min_le_left _ _),
    hingeCond_mono hGeometry.2 (min_le_right _ _)⟩

/-- The paid-child inverse and all three orders are specified functions. -/
theorem paid_smooth_at_explicit (α β : ℝ) (h : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hh : 6 ≤ h) :
    PaidSmoothAt α β (paidInverseCost α β h) (paidBudget α h) h
      (paidOrder α h) (paidPreparedOrder α h) (paidInverseOrder α h) := by
  have hαp := paidDensity_pos h hα hh
  have hhp : 6 ≤ paidHingeOrder h := by dsimp [paidHingeOrder]; omega
  let β' := min β (1 / 2)
  have hβ' : 0 < β' := lt_min hβ (by norm_num)
  have hBase : PaidSmoothAt α β
      (NativeSmooth.Explicit.inverseCost (paidDensity α h) β' (paidHingeOrder h))
      (paidBudget α h) h (paidOrder α h) (paidPreparedOrder α h) (paidInverseOrder α h) := by
    intro V I _ H F hn P h3 h4 B d hBE hDeg hSmall
    dsimp only
    intro h3J h4J
    have hsub {Z : Finset V} (hz : (Z.card : ℝ) ≤ β' * Fintype.card V) :
        (Z.card : ℝ) ≤ β * Fintype.card V :=
      hz.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
    have P' : Dispersal.PreparedCore H.G H.lab F α h
        (max (paidOrder α h) (paidPreparedOrder α h)) β' :=
      { h3 := fun Z hz => P.h3 Z (hsub hz)
        h4 := fun Z hz => P.h4 Z (hsub hz)
        order := fun Z hz => P.order Z (hsub hz)
        lattice_persist := fun Z hz y hy hvan => P.lattice_persist Z (hsub hz) y hy hvan }
    have Q := paid_prepared_core_with_required_order_explicit α h hα hh H F
      (paidPreparedOrder α h) β' hβ' (min_le_right _ _) P' h3 h4 B d hBE hDeg hSmall
    have Qα := Dispersal.preparedCore_weaken_alpha
      (show paidDensity α h / 4 ≤ paidDensity α h by linarith) Q
    have Qweak : Dispersal.PreparedCore (subHost H (edges H \ B)).G
        (subHost H (edges H \ B)).lab F (paidDensity α h / 4) (paidHingeOrder h)
        (paidPreparedOrder α h) β' :=
      { h3 := Qα.h3, h4 := Qα.h4,
        order := fun Z hz => (le_max_right _ _).trans (Qα.order Z hz),
        lattice_persist := Qα.lattice_persist }
    exact NativeSmooth.Explicit.smooth_on_prepared_host_explicit (paidDensity α h) β'
      (paidHingeOrder h) hαp hβ' hhp (subHost H (edges H \ B)) F hn h3J h4J Qweak
  intro V I _ H F hn P h3 h4 B d hBE hDeg hSmall
  dsimp only
  intro h3J h4J
  have hSmooth := hBase H F hn P h3 h4 B d hBE hDeg hSmall h3J h4J
  intro x hx ε hε hxBound
  obtain ⟨w, hSupport, hBoundary, hBound⟩ := hSmooth x hx ε hε hxBound
  refine ⟨w, hSupport, hBoundary, ?_⟩
  intro T
  exact (hBound T).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hε) (Nat.cast_nonneg _))

#print axioms intrinsic_dense_child_explicit
#print axioms paid_reference_cap_explicit
#print axioms paid_smooth_at_explicit
end TypedTriangle.Vortex.Explicit
