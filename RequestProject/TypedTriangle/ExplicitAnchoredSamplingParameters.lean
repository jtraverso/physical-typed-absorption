/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexAnchoredParameters
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.RawReference.Explicit

/-- Extra orders are harmless: using j+6 for j≤h avoids a conditional rate
at the small orders where the denominator i-4 would vanish. -/
def hingeGeometryRate (α q : ℝ) (j : ℕ) : ℝ :=
  α^2*q^(2*(j+2))/(4*((2:ℝ)^((j+6).choose 2))^2*(j+2:ℝ))

def hingeGeometryMinimum (α q : ℝ) (h : ℕ) : ℝ :=
  (univ : Finset (Fin (h+1))).inf' ⟨0,mem_univ _⟩ (fun j => hingeGeometryRate α q j)

def geometryRate (α q : ℝ) (h : ℕ) : ℝ :=
  min (q^2/4) (min (α^2*q^2/4) (hingeGeometryMinimum α q h))

theorem hingeGeometryRate_pos (α q : ℝ) (j : ℕ) (hα : 0 < α) (hq : 0 < q) :
    0 < hingeGeometryRate α q j := by
  unfold hingeGeometryRate
  positivity

theorem geometryRate_spec (α q : ℝ) (h : ℕ) (hα : 0 < α) (hq : 0 < q) :
    0 < geometryRate α q h ∧ geometryRate α q h ≤ q^2/4 ∧
    geometryRate α q h ≤ α^2*q^2/4 ∧
    (∀ i, 6 ≤ i → i ≤ h → geometryRate α q h ≤
      α^2*q^(2*(i-4))/(4*((2:ℝ)^(i.choose 2))^2*((i-4:ℕ):ℝ))) := by
  have hMin : 0 < hingeGeometryMinimum α q h := by
    apply (lt_inf'_iff _).mpr
    intro j _
    exact hingeGeometryRate_pos α q j hα hq
  have hRate : 0 < geometryRate α q h := lt_min (by positivity) (lt_min (by positivity) hMin)
  refine ⟨hRate,min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),?_⟩
  intro i hi6 hih
  let j : Fin (h+1) := ⟨i-6,by omega⟩
  have hj6 : (j:ℕ)+6=i := by dsimp [j]; omega
  have hj2 : (j:ℕ)+2=i-4 := by dsimp [j]; omega
  have hj2R : ((j:ℕ):ℝ)+2=((i-4:ℕ):ℝ) := by exact_mod_cast hj2
  have hMinI : hingeGeometryMinimum α q h ≤ hingeGeometryRate α q j :=
    inf'_le (f := fun k : Fin (h+1) => hingeGeometryRate α q k) (mem_univ j)
  have hh := ((min_le_right (q^2/4) (min (α^2*q^2/4) (hingeGeometryMinimum α q h))).trans
    (min_le_right (α^2*q^2/4) (hingeGeometryMinimum α q h))).trans hMinI
  simpa only [geometryRate,hingeGeometryRate,hj6,hj2,hj2R] using hh

/-- Every numerical rate inequality is certified already at n≥1. The larger
probabilistic threshold will be a separate explicit polynomial-sqrt cut. -/
theorem geometry_at_order_one (α q : ℝ) (h : ℕ) (hα : 0 < α) (hq : 0 < q)
    (n : ℕ) (hn1 : (1:ℝ) ≤ n) :
    let η : ℝ := (Real.sqrt (Real.sqrt n))⁻¹;
    let θ : ℝ := geometryRate α q h*η^2;
    0 < η ∧ η ≤ 1 ∧ θ ≤ η^2*q^2/4 ∧ θ ≤ η^2*α^2*q^2/4 ∧
    (∀ i, 6 ≤ i → i ≤ h → θ ≤ η^2*α^2*q^(2*(i-4))/
      (4*((2:ℝ)^(i.choose 2))^2*((i-4:ℕ):ℝ))) := by
  obtain ⟨hc,hcsize,hcpool,hchinge⟩ := geometryRate_spec α q h hα hq
  let c := geometryRate α q h
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hs1 : (1 : ℝ) ≤ Real.sqrt n := by
    simpa using (Real.sqrt_le_sqrt hn1)
  have hss1 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt n) := by
    simpa using (Real.sqrt_le_sqrt hs1)
  dsimp
  have hηpos : 0 < (Real.sqrt (Real.sqrt n))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.2 (Real.sqrt_pos.2 hnpos))
  have hηle : (Real.sqrt (Real.sqrt n))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hss1
  have hηsq : 0 ≤ ((Real.sqrt (Real.sqrt n))⁻¹)^2 := sq_nonneg _
  refine ⟨hηpos,hηle,?_,?_,?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hcsize hηsq]
  · nlinarith [mul_le_mul_of_nonneg_right hcpool hηsq]
  · intro i hi6 hih
    calc
      c * (Real.sqrt (Real.sqrt n))⁻¹ ^ 2 ≤
          (α ^ 2 * q ^ (2 * (i - 4)) /
            (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ))) *
            (Real.sqrt (Real.sqrt n))⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_right (hchinge i hi6 hih) hηsq
      _ = (Real.sqrt (Real.sqrt n))⁻¹ ^ 2 * α ^ 2 * q ^ (2 * (i - 4)) /
            (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ)) := by ring

#print axioms geometryRate_spec
#print axioms geometry_at_order_one
end TypedTriangle.RawReference.Explicit
