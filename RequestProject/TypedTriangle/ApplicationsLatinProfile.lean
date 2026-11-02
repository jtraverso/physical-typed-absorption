module
public import RequestProject.TypedTriangle.ApplicationsLatinCore
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin

/-- Extension of a three-dimensional stochastic array to triangle weights. -/
def weight {A : Type} [Fintype A] (p : A → A → A → ℝ) (T : Finset (Vertex A)) : ℝ :=
  ∑ x, ∑ y, ∑ z, if T=latinTriangle x y z then p x y z else 0

@[simp] theorem weight_triangle {A : Type} [Fintype A] (p : A → A → A → ℝ) (x y z : A) :
    weight p (latinTriangle x y z)=p x y z := by
  simp [weight,latinTriangle_eq_iff,ite_and]

theorem sum_allowed_eq {A : Type} [Fintype A] (f : Finset (Vertex A) → ℝ) :
    (∑ T ∈ allowed (host A) types, f T)=∑ x,∑ y,∑ z,f (latinTriangle x y z) := by
  symm
  rw [←Fintype.sum_prod_type',←Fintype.sum_prod_type']
  apply Finset.sum_bij (fun p _ => latinTriangle p.1.1 p.1.2 p.2)
  · intro p _
    exact mem_filter.mpr ⟨mem_univ _,latinTriangle_allowed _ _ _⟩
  · intro p _ q _ he
    obtain ⟨hx,hy,hz⟩ := (latinTriangle_eq_iff _ _ _ _ _ _).mp he
    exact Prod.ext (Prod.ext hx hy) hz
  · intro T hT
    obtain ⟨x,y,z,rfl⟩ := allowed_iff T |>.mp (mem_filter.mp hT).2
    exact ⟨((x,y),z),mem_univ _,rfl⟩
  · intro p _; rfl

theorem sum_decomposition_eq {A : Type} [Fintype A] (L : LatinSquare A)
    (f : Finset (Vertex A) → ℝ) :
    (∑ T ∈ decomposition L,f T)=∑ x,∑ y,f (latinTriangle x y (L x y)) := by
  rw [decomposition,Finset.sum_image]
  · rw [Fintype.sum_prod_type]
  · intro p _ q _ he
    have ht := (latinTriangle_eq_iff _ _ _ _ _ _).mp he
    exact Prod.ext ht.1 ht.2.1

theorem edge01_load {A : Type} [Fintype A] (p : A → A → A → ℝ) (x y : A) :
    (∑ T ∈ (allowed (host A) types).filter (fun T => s((0,x),(1,y)) ∈ triEdges T),weight p T)=
      ∑ z,p x y z := by
  rw [Finset.sum_filter,sum_allowed_eq]
  simp [ite_and]

theorem edge02_load {A : Type} [Fintype A] (p : A → A → A → ℝ) (x z : A) :
    (∑ T ∈ (allowed (host A) types).filter (fun T => s((0,x),(2,z)) ∈ triEdges T),weight p T)=
      ∑ y,p x y z := by
  rw [Finset.sum_filter,sum_allowed_eq]
  simp [ite_and]

theorem edge12_load {A : Type} [Fintype A] (p : A → A → A → ℝ) (y z : A) :
    (∑ T ∈ (allowed (host A) types).filter (fun T => s((1,y),(2,z)) ∈ triEdges T),weight p T)=
      ∑ x,p x y z := by
  rw [Finset.sum_filter,sum_allowed_eq]
  simp [ite_and]

/-- The three pair marginals are exactly the edge equations in H1. -/
theorem weight_exact_marginals {A : Type} [Fintype A] (p : A → A → A → ℝ)
    (h01 : ∀ x y,∑ z,p x y z=1) (h02 : ∀ x z,∑ y,p x y z=1)
    (h12 : ∀ y z,∑ x,p x y z=1) :
    ∀ e ∈ (host A).G.edgeSet,
      ∑ T ∈ (allowed (host A) types).filter (fun T => e ∈ triEdges T),weight p T=1 := by
  intro e
  refine Sym2.inductionOn e ?_
  rintro ⟨i,x⟩ ⟨j,y⟩ hij
  change i≠j at hij
  have h01' (x y : A) := (edge01_load p x y).trans (h01 x y)
  have h02' (x z : A) := (edge02_load p x z).trans (h02 x z)
  have h12' (y z : A) := (edge12_load p y z).trans (h12 y z)
  have h10' (y x : A) :
      (∑ T ∈ (allowed (host A) types).filter (fun T => s((1,y),(0,x)) ∈ triEdges T),weight p T)=1 := by
    rw [Sym2.eq_swap]
    exact h01' x y
  have h20' (z x : A) :
      (∑ T ∈ (allowed (host A) types).filter (fun T => s((2,z),(0,x)) ∈ triEdges T),weight p T)=1 := by
    rw [Sym2.eq_swap]
    exact h02' x z
  have h21' (z y : A) :
      (∑ T ∈ (allowed (host A) types).filter (fun T => s((2,z),(1,y)) ∈ triEdges T),weight p T)=1 := by
    rw [Sym2.eq_swap]
    exact h12' y z
  fin_cases i <;> fin_cases j <;> simp only [Fin.isValue,ne_eq,not_true_eq_false] at hij
  all_goals first | contradiction | exact h01' x y | exact h02' x y | exact h12' x y |
    exact h10' x y | exact h20' x y | exact h21' x y

theorem diffuse_of_marginals {A : Type} [Fintype A]
    (C : ℝ) (p : A → A → A → ℝ)
    (hBounds : ∀ x y z,1/(C*(3*(Fintype.card A : ℝ))) ≤ p x y z ∧
      p x y z ≤ C/(3*(Fintype.card A : ℝ)))
    (h01 : ∀ x y,∑ z,p x y z=1) (h02 : ∀ x z,∑ y,p x y z=1)
    (h12 : ∀ y z,∑ x,p x y z=1) :
    IsDiffuseSeed (host A) types C (weight p) := by
  constructor
  · intro T hT
    obtain ⟨x,y,z,rfl⟩ := (allowed_iff T).mp hT
    simpa only [weight_triangle,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
      using hBounds x y z
  · intro e he
    have hm := weight_exact_marginals p h01 h02 h12 e he
    convert hm using 1
    apply Finset.sum_congr
    · ext T
      simp
    · intro T hT
      rfl

/-- Constants for an array bounded between a/n and b/n. -/
def profileConstant (a b : ℝ) : ℝ := max 1 (max (3*b) (1/(3*a)))

theorem profileConstant_ge_one (a b : ℝ) : 1 ≤ profileConstant a b := le_max_left _ _

theorem diffuse_of_profile {A : Type} [Fintype A] [Nonempty A]
    (a b : ℝ) (ha : 0<a) (p : A → A → A → ℝ)
    (hBounds : ∀ x y z,a/Fintype.card A ≤ p x y z ∧ p x y z ≤ b/Fintype.card A)
    (h01 : ∀ x y,∑ z,p x y z=1) (h02 : ∀ x z,∑ y,p x y z=1)
    (h12 : ∀ y z,∑ x,p x y z=1) :
    IsDiffuseSeed (host A) types (profileConstant a b) (weight p) := by
  have hn : (0:ℝ)<Fintype.card A := Nat.cast_pos.mpr Fintype.card_pos
  have hC : 0<profileConstant a b := lt_of_lt_of_le zero_lt_one (profileConstant_ge_one a b)
  have hb : 3*b ≤ profileConstant a b := (le_max_left _ _).trans (le_max_right _ _)
  have haC : 1/(3*a) ≤ profileConstant a b := (le_max_right _ _).trans (le_max_right _ _)
  have hRecip : 1/(3*profileConstant a b) ≤ a := by
    have ht := (div_le_iff₀ (show (0:ℝ)<3*a by positivity)).mp haC
    apply (div_le_iff₀ (show (0:ℝ)<3*profileConstant a b by positivity)).mpr
    nlinarith only [ht]
  apply diffuse_of_marginals _ _ ?_ h01 h02 h12
  intro x y z
  constructor
  · have hh := div_le_div_of_nonneg_right hRecip hn.le
    have he : (1/(3*profileConstant a b))/Fintype.card A=
        1/(profileConstant a b*(3*(Fintype.card A : ℝ))) := by
      field_simp [ne_of_gt hC,ne_of_gt hn] <;> ring
    rw [he] at hh
    exact hh.trans (hBounds x y z).1
  · have hh := div_le_div_of_nonneg_right (show b ≤ profileConstant a b/3 by linarith only [hb]) hn.le
    have he : (profileConstant a b/3)/Fintype.card A=
        profileConstant a b/(3*(Fintype.card A : ℝ)) := by
      field_simp [ne_of_gt hn] <;> ring
    rw [he] at hh
    exact (hBounds x y z).2.trans hh

#print axioms diffuse_of_profile
end TypedTriangle.Applications.Latin
