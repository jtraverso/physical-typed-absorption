module
public import RequestProject.TypedTriangle.ApplicationsRainbowNeighbors
public import RequestProject.TypedTriangle.ApplicationsOctahedronTransport
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Rainbow

local instance {k : ℕ} {A : Type} : DecidableEq (Fin k × A) := Classical.decEq _

private theorem allowed_triangle_classical {k : ℕ} {A : Type} [Fintype A]
    (u v w : Fin k × A) (huv : u.1 ≠ v.1) (huw : u.1 ≠ w.1) (hvw : v.1 ≠ w.1) :
    IsAllowed (host k A) (types k) {u,v,w} := by
  convert allowed_triangle u v w huv huw hvw using 1 <;> ext x <;> simp

private def vertexMap {k : ℕ} {A : Type} (u v a b : Fin k × A) (x y : A) :
    Fin 6 → Fin k × A := ![u,v,a,b,(u.1,x),(v.1,y)]

private theorem vertexMap_injective {k : ℕ} {A : Type} (u v a b : Fin k × A)
    (hab : a ≠ b) (huv : u.1 ≠ v.1) (hua : u.1 ≠ a.1) (hva : v.1 ≠ a.1)
    (hub : u.1 ≠ b.1) (hvb : v.1 ≠ b.1) (x y : A)
    (hx : x ≠ u.2) (hy : y ≠ v.2) : Function.Injective (vertexMap u v a b x y) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [vertexMap,Prod.ext_iff,eq_comm]

private def vertexEmbedding {k : ℕ} {A : Type} (u v a b : Fin k × A)
    (hab : a ≠ b) (huv : u.1 ≠ v.1) (hua : u.1 ≠ a.1) (hva : v.1 ≠ a.1)
    (hub : u.1 ≠ b.1) (hvb : v.1 ≠ b.1) (x y : A)
    (hx : x ≠ u.2) (hy : y ≠ v.2) : Fin 6 ↪ Fin k × A :=
  ⟨vertexMap u v a b x y,vertexMap_injective u v a b hab huv hua hva hub hvb x y hx hy⟩

theorem hinges_six_card_ge {k : ℕ} {A : Type} [Fintype A]
    (u v a b : Fin k × A) (hab : a ≠ b)
    (hTa : IsAllowed (host k A) (types k) {u,v,a})
    (hTb : IsAllowed (host k A) (types k) {u,v,b}) :
    (Fintype.card A-1)^2 ≤ (hinges (host k A) (types k) u v a b 6).card := by
  obtain ⟨huv',hua',hva'⟩ := distinct_of_card_three hTa.1
  obtain ⟨_,hub',hvb'⟩ := distinct_of_card_three hTb.1
  have huv : u.1 ≠ v.1 := hTa.2.1 u (by simp) v (by simp) huv'
  have hua : u.1 ≠ a.1 := hTa.2.1 u (by simp) a (by simp) hua'
  have hva : v.1 ≠ a.1 := hTa.2.1 v (by simp) a (by simp) hva'
  have hub : u.1 ≠ b.1 := hTb.2.1 u (by simp) b (by simp) hub'
  have hvb : v.1 ≠ b.1 := hTb.2.1 v (by simp) b (by simp) hvb'
  let P : Finset (A×A) := (univ.erase u.2) ×ˢ (univ.erase v.2)
  let f (z : {z // z∈P}) : Fin 6 ↪ Fin k × A :=
    vertexEmbedding u v a b hab huv hua hva hub hvb z.1.1 z.1.2
      (mem_erase.mp (mem_product.mp z.2).1).1
      (mem_erase.mp (mem_product.mp z.2).2).1
  let J (z : {z // z∈P}) := Octahedron.coreImage (f z)
  have hAllowed (z : {z // z∈P}) :
      ∀ T∈Octahedron.mode 2 3 ∪ Octahedron.mode 3 2,
        IsAllowed (host k A) (types k) (T.map (f z)) := by
    intro T hT
    simp only [mem_union,Octahedron.mode,mem_insert,mem_singleton] at hT
    rcases hT with (rfl | rfl | rfl) | (rfl | rfl | rfl)
    all_goals
      simp only [map_insert,map_singleton]
      apply allowed_triangle_classical <;> simp_all [f,vertexEmbedding,vertexMap]
  have hSub : univ.image J ⊆ hinges (host k A) (types k) u v a b 6 := by
    intro E hE
    obtain ⟨z,_,rfl⟩ := mem_image.mp hE
    have hh := Octahedron.hinge_of_modes (host k A) (types k) (f z) (hAllowed z)
    have hc := Octahedron.card_support_coreImage (f z)
    change IsHinge (host k A) (types k) u v a b (J z) at hh
    have hCert : IsHinge (host k A) (types k) u v a b (J z) ∧
        (support (J z)).card=6 := ⟨hh,hc⟩
    simpa only [hinges,mem_filter,mem_univ,true_and] using hCert
  have hJinj : Function.Injective J := by
    intro z z' hEq
    have h0 : s((f z) 0,(f z) 5) ∈ J z :=
      (Octahedron.edge_at_zero (f z) ((f z) 5)).mpr rfl
    have h1 : s((f z) 1,(f z) 4) ∈ J z :=
      (Octahedron.edge_at_one (f z) ((f z) 4)).mpr rfl
    rw [hEq] at h0 h1
    have hy : (f z) 5 = (f z') 5 := (Octahedron.edge_at_zero (f z') ((f z) 5)).mp h0
    have hx : (f z) 4 = (f z') 4 := (Octahedron.edge_at_one (f z') ((f z) 4)).mp h1
    have hx' : z.1.1=z'.1.1 := congrArg (fun w : Fin k × A => w.2) hx
    have hy' : z.1.2=z'.1.2 := congrArg (fun w : Fin k × A => w.2) hy
    apply Subtype.ext
    exact Prod.ext hx' hy'
  have hCard : (univ.image J).card = P.card := by
    rw [card_image_iff.mpr (fun _ _ _ _ h => hJinj h),card_univ,Fintype.card_coe]
  have hP : P.card = (Fintype.card A-1)^2 := by
    simp only [P,card_product,card_erase_of_mem (mem_univ _),card_univ,pow_two]
  rw [←hP,←hCard]
  exact card_le_card hSub

theorem hingeCond (k : ℕ) (A : Type) [Fintype A]
    (hk : 3 ≤ k) (hn : 2 ≤ Fintype.card A) :
    HingeCond (host k A) (types k) (1/(4*(k:ℝ)^2)) 6 := by
  intro u v a b hab hTa hTb
  refine ⟨6,le_rfl,le_rfl,?_⟩
  have hc := hinges_six_card_ge u v a b hab hTa hTb
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (show k≠0 by omega)
  have hnR : (2:ℝ) ≤ Fintype.card A := by exact_mod_cast hn
  have hn1 : 1 ≤ Fintype.card A := by omega
  have hPay : (1/(4*(k:ℝ)^2))*((k:ℝ)*(Fintype.card A:ℝ))^2 =
      (Fintype.card A:ℝ)^2/4 := by field_simp [hk0]
  have hSquare : (Fintype.card A:ℝ)^2/4 ≤ ((Fintype.card A-1:ℕ):ℝ)^2 := by
    rw [Nat.cast_sub hn1,Nat.cast_one]
    nlinarith only [hnR,sq_nonneg ((Fintype.card A:ℝ)-2)]
  norm_num only [Nat.reduceSub,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
  rw [hPay]
  exact hSquare.trans (by exact_mod_cast hc)

#print axioms hinges_six_card_ge
#print axioms hingeCond
end TypedTriangle.Applications.Rainbow
