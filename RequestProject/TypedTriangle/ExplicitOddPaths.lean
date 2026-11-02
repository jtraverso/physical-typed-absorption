/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Mathlib
public import RequestProject.S07.Compose
public import RequestProject.TypedTriangle.TupleCount
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace S07V24.Explicit
open TypedTriangle.SparseEdge
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A closed odd mixing time, replacing the existential kOf from the legacy
path theorem. All powers and ceilings depend only on c and κ. -/
def oddPathK (c κ : ℝ) : ℕ :=
  2*⌈4/((min κ 1)^2*(min c 1)^5)⌉₊+1

def pathInteriorCount (c κ : ℝ) : ℕ := oddPathK c κ+1

def pathDensity (c κ : ℝ) : ℝ := (min c 1)^(oddPathK c κ+3)/4

def oddPathOrder (c κ : ℝ) : ℕ :=
  ⌈4*((oddPathK c κ:ℝ)+2)^2/(min c 1)^(oddPathK c κ+3)⌉₊+1

theorem oddPathK_spec {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) :
    Odd (oddPathK c κ) ∧
      ((1-(min κ 1)^2/2)^2)^(oddPathK c κ) ≤ (min c 1)^5/4 := by
  let c₀ := min c 1
  let κ₀ := min κ 1
  have hc₀ : 0 < c₀ := lt_min hc one_pos
  have hκ₀ : 0 < κ₀ := lt_min hκ one_pos
  have hκ₁ : κ₀ ≤ 1 := min_le_right _ _
  have hDen : 0 < κ₀^2*c₀^5 := by positivity
  let j := ⌈4/(κ₀^2*c₀^5)⌉₊
  have hj : 4 ≤ (j:ℝ)*(κ₀^2*c₀^5) :=
    (div_le_iff₀ hDen).mp (Nat.le_ceil _)
  have hjk : (j:ℝ) ≤ oddPathK c κ := by
    have hn : j ≤ oddPathK c κ := by dsimp [j,c₀,κ₀,oddPathK]; omega
    exact_mod_cast hn
  have hPay : 4 ≤ (oddPathK c κ:ℝ)*κ₀^2*c₀^5 := by
    have hm := mul_le_mul_of_nonneg_right hjk hDen.le
    nlinarith only [hj,hm]
  refine ⟨odd_two_mul_add_one _,?_⟩
  have hu0 : 0 ≤ κ₀^2/2 := by positivity
  have hu1 : κ₀^2/2 ≤ 1 := by
    have hs : κ₀^2 ≤ 1 := pow_le_one₀ hκ₀.le hκ₁
    linarith only [hs]
  change ((1-κ₀^2/2)^2)^(oddPathK c κ) ≤ c₀^5/4
  rw [←pow_mul]
  apply (TypedTriangle.one_sub_pow_le_inv hu0 hu1 (2*oddPathK c κ)).trans
  have hpos : (0:ℝ) < 1+((2*oddPathK c κ:ℕ):ℝ)*(κ₀^2/2) := by positivity
  apply (div_le_div_iff₀ hpos (by norm_num : (0:ℝ)<4)).mpr
  push_cast
  nlinarith only [hPay,pow_pos hc₀ 5]

theorem odd_paths_bip_formula (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ)
    (K : SimpleGraph V) [DecidableRel K.Adj] (n : ℕ) (hn : oddPathOrder c κ ≤ n)
    (hmin : ∀ v, c * n ≤ K.degree v) (hmax : ∀ v, K.degree v ≤ n) (hcard : Fintype.card V ≤ n)
    (hexp : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V → κ * n * S.card ≤ cutCount K S)
    (col : V → Bool) (hcol : ∀ v w, K.Adj v w → col v ≠ col w) (x y : V) (hxy : col x ≠ col y) :
    (min c 1) ^ (oddPathK c κ + 3) / 4 * (n : ℝ) ^ (oddPathK c κ + 1) ≤
      (pathsLen K (oddPathK c κ + 2) x y).card := by
  obtain ⟨hkodd, hkb⟩ := oddPathK_spec hc hκ
  set k := oddPathK c κ
  set c' := min c 1
  set κ' := min κ 1
  have hc' : 0 < c' := lt_min hc one_pos
  have hκ' : 0 < κ' := lt_min hκ one_pos
  have hxy' : x ≠ y := fun h => hxy (h ▸ rfl)
  have hn0 : (4 * ((k : ℝ) + 2) ^ 2 / c' ^ (k + 3)) ≤ n := by
    have := Nat.le_ceil (4 * ((k : ℝ) + 2) ^ 2 / c' ^ (k + 3))
    have h2 : ((oddPathOrder c κ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    unfold oddPathOrder at h2; push_cast at h2; linarith
  have hnpos : 0 < n := by
    have : (0 : ℝ) < 4 * ((k : ℝ) + 2) ^ 2 / c' ^ (k + 3) := by positivity
    exact_mod_cast (lt_of_lt_of_le this hn0)
  have hmin' : ∀ v, c' * n ≤ K.degree v := fun v =>
    le_trans (mul_le_mul_of_nonneg_right (min_le_left c 1) (Nat.cast_nonneg _)) (hmin v)
  have hexp' : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V → κ' * n * S.card ≤ cutCount K S :=
    fun S hS => le_trans (by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left κ 1)
        (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (hexp S hS)
  have hw := walks_lower_core K hc' hκ' (min_le_right κ 1) hnpos hmin' hmax (by omega) hexp'
    col hcol k hkodd hkb x y hxy
  have := paths_from_walks K hc' k n hn0 hcard x y hxy' hw
  exact this


theorem odd_paths_nonbip_formula (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ)
    (K : SimpleGraph V) [DecidableRel K.Adj] (n : ℕ) (hn : oddPathOrder c κ ≤ n)
    (hmin : ∀ v, c * n ≤ K.degree v) (hmax : ∀ v, K.degree v ≤ n) (hcard : Fintype.card V ≤ n)
    (hexp : ∀ S : Finset (V × Bool), 2 * S.card ≤ Fintype.card (V × Bool) →
      κ * n * S.card ≤ cutCount (dcover K) S)
    (x y : V) (hxy : x ≠ y) :
    (min c 1) ^ (oddPathK c κ + 3) / 4 * (n : ℝ) ^ (oddPathK c κ + 1) ≤
      (pathsLen K (oddPathK c κ + 2) x y).card := by
  obtain ⟨hkodd, hkb⟩ := oddPathK_spec hc hκ
  set k := oddPathK c κ
  set c' := min c 1
  set κ' := min κ 1
  have hc' : 0 < c' := lt_min hc one_pos
  have hκ' : 0 < κ' := lt_min hκ one_pos
  have hn0 : (4 * ((k : ℝ) + 2) ^ 2 / c' ^ (k + 3)) ≤ n := by
    have := Nat.le_ceil (4 * ((k : ℝ) + 2) ^ 2 / c' ^ (k + 3))
    have h2 : ((oddPathOrder c κ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    unfold oddPathOrder at h2; push_cast at h2; linarith
  have hnpos : 0 < n := by
    have : (0 : ℝ) < 4 * ((k : ℝ) + 2) ^ 2 / c' ^ (k + 3) := by positivity
    exact_mod_cast (lt_of_lt_of_le this hn0)
  have hmin' : ∀ p : V × Bool, c' * n ≤ (dcover K).degree p := fun p => by
    rw [dcover_degree]
    exact le_trans (mul_le_mul_of_nonneg_right (min_le_left c 1) (Nat.cast_nonneg _)) (hmin p.1)
  have hmax' : ∀ p : V × Bool, (dcover K).degree p ≤ n := fun p => by
    rw [dcover_degree]; exact hmax p.1
  have hcard' : Fintype.card (V × Bool) ≤ 2 * n := by
    rw [Fintype.card_prod, Fintype.card_bool]; omega
  have hexp' : ∀ S : Finset (V × Bool), 2 * S.card ≤ Fintype.card (V × Bool) →
      κ' * n * S.card ≤ cutCount (dcover K) S :=
    fun S hS => le_trans (by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left κ 1)
        (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (hexp S hS)
  have hw := walks_lower_core (dcover K) hc' hκ' (min_le_right κ 1) hnpos hmin' hmax' hcard'
    hexp' Prod.snd (fun p q h => h.2) k hkodd hkb (x, false) (y, true) (by simp)
  have hw' := hw.trans (dcover_walks_le K (k + 2) x y false true)
  have := paths_from_walks K hc' k n hn0 hcard x y hxy hw'
  exact this


theorem link_paths_of_interface_formula (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ)
    (L : SimpleGraph V) [DecidableRel L.Adj] (n : ℕ) (hn : oddPathOrder c κ ≤ n)
    (hV : Fintype.card V = n) (C : Finset V) (bip : Prop) (col : V → Bool)
    (hI : CompInterface L c κ n C bip col) (x y : V) (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y)
    (hcol : bip → col x ≠ col y) :
    pathDensity c κ * (n : ℝ) ^ pathInteriorCount c κ ≤ (pathsLen L (pathInteriorCount c κ + 1) x y).card := by
  obtain ⟨hmin, hmax, hbip, hnb⟩ := hI
  have hcard : Fintype.card (C : Set V) ≤ n := by
    rw [← hV]; exact Fintype.card_subtype_le _
  set x' : (C : Set V) := ⟨x, hx⟩
  set y' : (C : Set V) := ⟨y, hy⟩
  have htr := card_pathsLen_induce_le L C (oddPathK c κ + 2) x' y'
  have hcount : pathDensity c κ * (n : ℝ) ^ pathInteriorCount c κ ≤
      (pathsLen (L.induce (C : Set V)) (oddPathK c κ + 2) x' y').card := by
    by_cases hb : bip
    · obtain ⟨hproper, hexp⟩ := hbip hb
      exact odd_paths_bip_formula c κ hc hκ (L.induce (C : Set V)) n hn hmin hmax hcard hexp
        (fun w => col w.1) hproper x' y' (hcol hb)
    · exact odd_paths_nonbip_formula c κ hc hκ (L.induce (C : Set V)) n hn hmin hmax hcard
        (hnb hb) x' y' (fun h => hxy (congrArg Subtype.val h))
  exact hcount.trans (by exact_mod_cast htr)


#print axioms oddPathK_spec
#print axioms odd_paths_bip_formula
#print axioms odd_paths_nonbip_formula
#print axioms link_paths_of_interface_formula
end S07V24.Explicit
