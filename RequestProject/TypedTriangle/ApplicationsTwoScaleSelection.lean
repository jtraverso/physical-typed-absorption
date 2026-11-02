module
public import Mathlib
public import PartitionedTriangleAbsorption.BernoulliBlocks
@[expose] public section
open Finset MeasureTheory ProbabilityTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TypedTriangle.Applications.Latin.TwoScale

/-- A finite simultaneous choice from one probability space. No independence
between the bad events is needed. -/
theorem exists_avoiding_finite_events {Ω J : Type} [MeasurableSpace Ω] [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (bad : J → Set Ω) (p : ℝ)
    (hbad : ∀ j, μ.real (bad j) ≤ p) (hsmall : (Fintype.card J : ℝ)*p < 1) :
    ∃ ω, ∀ j, ω ∉ bad j := by
  classical
  by_contra h
  push Not at h
  have huniv : (⋃ j, bad j) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact h ω
  have hb := measureReal_iUnion_fintype_le (μ := μ) bad
  have hs : (∑ j, μ.real (bad j)) ≤ (Fintype.card J : ℝ)*p := by
    calc
      _ ≤ ∑ _j : J, p := sum_le_sum (fun j _ => hbad j)
      _ = _ := by simp
  rw [huniv] at hb
  have hu : μ.real Set.univ = 1 := by simp
  linarith

/-- Two-sided Hoeffding estimate with a common interval bound. -/
theorem bounded_independent_tail {Ω I : Type} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → ℝ)
    (hind : iIndepFun X μ) (D ε : ℝ) (hD : 0≤D) (hε : 0≤ε)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-D) D)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    μ.real {ω | ε ≤ |∑ i, X i ω|} ≤
      2*Real.exp (-ε^2/(2*(Fintype.card I : ℝ)*D^2)) := by
  classical
  let c : NNReal := ⟨D^2, sq_nonneg D⟩
  have hc : (‖D-(-D)‖₊/2)^2=c := by
    apply Subtype.ext
    change (‖D-(-D)‖/2)^2 = D^2
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    ring
  have hsg (i : I) : HasSubgaussianMGF (X i) c μ := by
    rw [← hc]
    exact hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hmeas i) (hbound i) (hmean i)
  have hu := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := univ) (fun i _ => hsg i) hε
  have hnind : iIndepFun (fun i ω => -X i ω) μ :=
    hind.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hl := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hnind
    (s := univ) (fun i _ => (hsg i).neg) hε
  have hevent : {ω | ε ≤ |∑ i, X i ω|} =
      {ω | ε ≤ ∑ i, X i ω} ∪ {ω | ε ≤ ∑ i, -X i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, sum_neg_distrib, le_abs]
  have hden : (2*(∑ _i : I, c) : ℝ) = 2*(Fintype.card I : ℝ)*D^2 := by
    rw [NNReal.coe_sum]
    change 2*(∑ _i : I, D^2)=2*(Fintype.card I : ℝ)*D^2
    simp [mul_assoc]
  simp only [hden] at hu hl
  rw [hevent]
  exact (measureReal_union_le _ _).trans (by linarith)

/-- Construct independent fair signs and select one outcome retaining all
prescribed linear forms. The probability space is constructed internally. -/
theorem exists_signs_for_linear_forms {I J : Type} [Fintype I] [Fintype J]
    (d : J → I → ℝ) (D ε : ℝ) (hD : 0≤D) (hε : 0≤ε)
    (hd : ∀ j i, |d j i|≤D)
    (hsmall : (Fintype.card J : ℝ) *
      (2*Real.exp (-ε^2/(2*(Fintype.card I : ℝ)*D^2))) < 1) :
    ∃ e : I → ℝ, (∀ i, e i=1 ∨ e i= -1) ∧
      ∀ j, |∑ i, e i*d j i| < ε := by
  classical
  obtain ⟨μ,hμ,hind,hmarg⟩ :=
    PartitionedTriangleAbsorption.BernoulliBlocks.exists_edge_trials (E := I)
      (1/2) (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure μ := hμ
  let A : I → Set (I → Bool) := fun i => {ω | ω i=true}
  let Z : I → (I → Bool) → ℝ := fun i => (A i).indicator (fun _ => 1)
  have hA (i : I) : MeasurableSet (A i) := MeasurableSet.of_discrete
  have hZ (i : I) : Measurable (Z i) := measurable_const.indicator (hA i)
  have hZi (i : I) : Integrable (Z i) μ := (integrable_const (1:ℝ)).indicator (hA i)
  have hmean (i : I) : ∫ ω, Z i ω ∂μ = (1/2:ℝ) := by
    rw [show Z i=(A i).indicator (1 : (I → Bool) → ℝ) from rfl,
      integral_indicator_one (hA i)]
    change (μ {ω | ω i=true}).toReal = _
    rw [hmarg]
    norm_num
  let X : J → I → (I → Bool) → ℝ := fun j i ω => d j i*(2*Z i ω-1)
  have hTail (j : J) : μ.real {ω | ε ≤ |∑ i, X j i ω|} ≤
      2*Real.exp (-ε^2/(2*(Fintype.card I : ℝ)*D^2)) := by
    apply bounded_independent_tail μ (X j) ?_ D ε hD hε ?_ ?_ ?_
    · exact hind.iIndepFun_indicator.comp (fun i (x : ℝ) => d j i*(2*x-1))
        (fun i => measurable_const.mul ((measurable_const.mul measurable_id).sub measurable_const))
    · intro i
      exact (measurable_const.mul ((measurable_const.mul (hZ i)).sub measurable_const)).aemeasurable
    · intro i
      apply ae_of_all
      intro ω
      have hh := abs_le.mp (hd j i)
      by_cases hω : ω i=true
      · norm_num [X,Z,A,hω]
        exact hh
      · norm_num [X,Z,A,hω]
        constructor <;> linarith
    · intro i
      change (∫ ω, d j i*(2*Z i ω-1) ∂μ)=0
      rw [integral_const_mul, integral_sub ((hZi i).const_mul 2) (integrable_const 1),
        integral_const_mul, hmean]
      simp
  obtain ⟨ω,hω⟩ := exists_avoiding_finite_events μ
    (fun j => {ω | ε≤|∑ i, X j i ω|}) _ hTail hsmall
  refine ⟨fun i => if ω i=true then 1 else -1, ?_, ?_⟩
  · intro i
    by_cases hi : ω i=true <;> simp [hi]
  · intro j
    have hpoint (i : I) : (if ω i=true then (1:ℝ) else -1)*d j i=X j i ω := by
      by_cases hi : ω i=true <;> norm_num [X,Z,A,hi]
    simp_rw [hpoint]
    exact lt_of_not_ge (hω j)

set_option pp.fullNames true
#print axioms exists_avoiding_finite_events
#print axioms bounded_independent_tail
#print axioms exists_signs_for_linear_forms
end TypedTriangle.Applications.Latin.TwoScale
