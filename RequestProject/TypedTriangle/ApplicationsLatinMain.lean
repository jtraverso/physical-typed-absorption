module
public import RequestProject.TypedTriangle.ApplicationsLatinProfile
public import RequestProject.TypedTriangle.ApplicationsLatinExtraction
public import RequestProject.TypedTriangle.ApplicationsLatinCyclic
public import RequestProject.TypedTriangle.ApplicationsRainbowGeometry
public import RequestProject.TypedTriangle.MainPaperIIIPasch
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin

private theorem pasch_error_change_decEq {V : Type} (D U : Finset (Finset V))
    (μ : Finset V → ℝ) (ε : ℝ) (d₁ d₂ : DecidableEq V)
    (h : |(@Pasch.count V d₁ D : ℝ)-@Pasch.target V d₁ μ U|≤ε) :
    |(@Pasch.count V d₂ D : ℝ)-@Pasch.target V d₂ μ U|≤ε := by
  cases Subsingleton.elim d₁ d₂
  exact h

/-- Latin squares realizing every bounded signed statistic and the Pasch
target of a positive three-dimensional stochastic array. -/
theorem latin_square_with_profile_statistics (a b η : ℝ) (q : ℕ)
    (ha : 0<a) (hη : 0<η) :
    ∃ N : ℕ, 2≤N ∧ ∀ (A : Type) [Fintype A],
      N≤Fintype.card A → ∀ p : A → A → A → ℝ,
      (∀ x y z,a/Fintype.card A ≤ p x y z ∧ p x y z ≤ b/Fintype.card A) →
      (∀ x y,∑ z,p x y z=1) → (∀ x z,∑ y,p x y z=1) → (∀ y z,∑ x,p x y z=1) →
      ∀ (ν : Type) [Fintype ν] (w : ν → A → A → A → ℝ),
      (Fintype.card ν : ℝ)≤(Fintype.card A : ℝ)^q →
      (∀ k x y z,|w k x y z|≤1) →
      ∃ L : LatinSquare A,
        (∀ k,|(∑ x,∑ y,w k x y (L x y))-(∑ x,∑ y,∑ z,p x y z*w k x y z)|≤
          η*(Fintype.card A : ℝ)^2) ∧
        |(Pasch.count (decomposition L) : ℝ)-Pasch.target (weight p) (allowed (host A) types)|≤
          η*(Fintype.card A : ℝ)^2 := by
  obtain ⟨n₀,hMain⟩ := Vortex.main_theorem_T_with_triangle_monitors_and_pasch
    types (1/36) (profileConstant a b) (η/9) 6 q (by norm_num)
      (profileConstant_ge_one a b) (by norm_num) (by positivity)
  refine ⟨max 2 n₀,le_max_left _ _,?_⟩
  intro A _ hN p hBounds h01 h02 h12 ν _ w hν hw
  have hn : 2≤Fintype.card A := (le_max_left _ _).trans hN
  letI : Nonempty A := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by norm_num : 0<2) hn)
  have hHost : n₀≤Fintype.card (Vertex A) := by
    rw [Fintype.card_prod,Fintype.card_fin]
    have := (le_max_right 2 n₀).trans hN
    omega
  have hH1 := diffuse_of_profile a b ha p hBounds h01 h02 h12
  have hH2 := cyclic_isPhysical A
  have hH3 : CommonNbrCond (host A) types (1/36) :=
    Rainbow.commonNbrCond 3 A (1/36) (by norm_num)
  have hH4 : HingeCond (host A) types (1/36) 6 := by
    convert Rainbow.hingeCond 3 A (by norm_num) hn using 1 <;> norm_num
  have hTests : (Fintype.card ν : ℝ)≤(Fintype.card (Vertex A) : ℝ)^q := by
    apply hν.trans
    rw [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    gcongr
    have h0 : (0:ℝ)≤Fintype.card A := Nat.cast_nonneg _
    linarith only [h0]
  obtain ⟨D,hD,hStat,hPasch⟩ := hMain (host A) (weight p) hHost hH1 hH2 hH3 hH4
    ν (fun k => weight (w k)) hTests (by
      intro k T hT
      obtain ⟨x,y,z,rfl⟩ := (allowed_iff T).mp hT
      simpa only [weight_triangle] using hw k x y z)
  let L := ofDecomposition hD
  have hLD : decomposition L=D := decomposition_ofDecomposition hD
  have hScale : η/9*(Fintype.card (Vertex A) : ℝ)^2=η*(Fintype.card A : ℝ)^2 := by
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    ring
  refine ⟨L,?_,?_⟩
  · intro k
    have hs := hStat k
    rw [←hLD,sum_decomposition_eq,sum_allowed_eq] at hs
    simpa only [weight_triangle,hScale] using hs
  · rw [hLD]
    exact pasch_error_change_decEq D (allowed (host A) types) (weight p)
      (η*(Fintype.card A : ℝ)^2) (Classical.decEq _) (inferInstance)
      (hPasch.trans_eq hScale)

theorem latin_square_with_uniform_statistics (η : ℝ) (q : ℕ) (hη : 0<η) :
    ∃ N : ℕ, 2≤N ∧ ∀ (A : Type) [Fintype A],
      N≤Fintype.card A → ∀ (ν : Type) [Fintype ν] (w : ν → A → A → A → ℝ),
      (Fintype.card ν : ℝ)≤(Fintype.card A : ℝ)^q →
      (∀ k x y z,|w k x y z|≤1) →
      ∃ L : LatinSquare A,
        (∀ k,|(∑ x,∑ y,w k x y (L x y))-
          (∑ x,∑ y,∑ z,(1/(Fintype.card A : ℝ))*w k x y z)|≤η*(Fintype.card A : ℝ)^2) ∧
        |(Pasch.count (decomposition L) : ℝ)-
          Pasch.target (weight (fun _ _ _ => 1/(Fintype.card A : ℝ))) (allowed (host A) types)|≤
            η*(Fintype.card A : ℝ)^2 := by
  obtain ⟨N,hN,hMain⟩ := latin_square_with_profile_statistics 1 1 η q (by norm_num) hη
  refine ⟨N,hN,?_⟩
  intro A _ hn ν _ w hν hw
  letI : Nonempty A := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by norm_num : 0<2) (hN.trans hn))
  have hcard : (Fintype.card A : ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  exact hMain A hn (fun _ _ _ => 1/(Fintype.card A : ℝ)) (by intros; exact ⟨le_rfl,le_rfl⟩)
    (by intros; simp [hcard]) (by intros; simp [hcard]) (by intros; simp [hcard]) ν w hν hw

#print axioms latin_square_with_profile_statistics
#print axioms latin_square_with_uniform_statistics
end TypedTriangle.Applications.Latin
