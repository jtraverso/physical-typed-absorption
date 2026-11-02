module
public import RequestProject.TypedTriangle.ApplicationsFivePartiteBlowup
public import RequestProject.TypedTriangle.ApplicationsFivePartiteSeedAssembly
public import RequestProject.TypedTriangle.ApplicationsRainbowGeometry
public import RequestProject.TypedTriangle.MainPaperIIIPasch
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.FivePartite
open _root_.TypedTriangle.Applications.FivePartite.Uniform

private theorem pasch_error_change_decEq {V : Type} (D U : Finset (Finset V))
    (μ : Finset V → ℝ) (ε : ℝ) (d₁ d₂ : DecidableEq V)
    (h : |(@Pasch.count V d₁ D : ℝ)-@Pasch.target V d₁ μ U|≤ε) :
    |(@Pasch.count V d₂ D : ℝ)-@Pasch.target V d₂ μ U|≤ε := by
  cases Subsingleton.elim d₁ d₂
  exact h

/-- Paper III on the balanced five-partite graph with part size
n=3|A|. The physical certificate is the displayed thirty-block design
and its symmetric Latin blow-up; the seed is exactly 1/(3n). -/
theorem main_theorem (η : ℝ) (q : ℕ) (hη : 0<η) :
    ∃N : ℕ,∀(A : Type) [Fintype A] [AddCommGroup A],
      N≤Fintype.card A →
      ∀(ν : Type) [Fintype ν] (w : ν → Finset (Vertex A) → ℝ),
      (Fintype.card ν : ℝ)≤(Fintype.card (Fin 3 × A) : ℝ)^q →
      (∀k T,IsAllowed (Rainbow.host 5 (Fin 3 × A)) (Rainbow.types 5) T → |w k T|≤1) →
      ∃D : Finset (Finset (Vertex A)),
        IsDecomposition (Rainbow.host 5 (Fin 3 × A)) (Rainbow.types 5)
          (edges (Rainbow.host 5 (Fin 3 × A))) D ∧
        (∀k,|(∑T∈D,w k T)-(∑T∈allowed (Rainbow.host 5 (Fin 3 × A)) (Rainbow.types 5),
          uniformSeed (Fin 3 × A) T*w k T)|≤η*(Fintype.card (Fin 3 × A) : ℝ)^2) ∧
        |(Pasch.count D : ℝ)-Pasch.target (uniformSeed (Fin 3 × A))
          (allowed (Rainbow.host 5 (Fin 3 × A)) (Rainbow.types 5))|≤
            η*(Fintype.card (Fin 3 × A) : ℝ)^2 := by
  obtain ⟨N,hMain⟩ := Vortex.main_theorem_T_with_triangle_monitors_and_pasch
    (Rainbow.types 5) (1/100) (5/3) (η/25) 6 q (by norm_num) (by norm_num) (by omega) (by positivity)
  refine ⟨max 1 N,?_⟩
  intro A _ _ hA ν _ w hν hw
  have hApos : 0<Fintype.card A := by omega
  have hN : N≤Fintype.card A := (le_max_right 1 N).trans hA
  have hHost : N≤Fintype.card (Vertex A) := by
    simp only [Vertex,Fintype.card_prod,Fintype.card_fin]
    omega
  have hPartPos : 0<Fintype.card (Fin 3 × A) := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega
  have hPartTwo : 2≤Fintype.card (Fin 3 × A) := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega
  have hHinge : HingeCond (Rainbow.host 5 (Fin 3 × A)) (Rainbow.types 5) (1/100) 6 := by
    convert Rainbow.hingeCond 5 (Fin 3 × A) (by omega) hPartTwo using 1 <;> norm_num
  have hPartLe : Fintype.card (Fin 3 × A)≤Fintype.card (Vertex A) := by
    simp only [Vertex,Fintype.card_prod,Fintype.card_fin]
    omega
  have hνHost : (Fintype.card ν : ℝ)≤(Fintype.card (Vertex A) : ℝ)^q :=
    hν.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hPartLe) q)
  have hScale : (η/25)*(Fintype.card (Vertex A) : ℝ)^2=
      η*(Fintype.card (Fin 3 × A) : ℝ)^2 := by
    simp only [Vertex,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    ring
  obtain ⟨D,hD,hMon,hPasch⟩ := hMain (Rainbow.host 5 (Fin 3 × A)) (uniformSeed (Fin 3 × A)) hHost
    (diffuse_uniformSeed hPartPos) physical
    (Rainbow.commonNbrCond 5 (Fin 3 × A) (1/100) (by norm_num))
    hHinge ν w hνHost hw
  refine ⟨D,hD,fun k => by simpa only [hScale] using hMon k,?_⟩
  exact pasch_error_change_decEq D
    (allowed (Rainbow.host 5 (Fin 3 × A)) (Rainbow.types 5))
    (uniformSeed (Fin 3 × A)) (η*(Fintype.card (Fin 3 × A) : ℝ)^2)
    (Classical.decEq _) (inferInstance) (hPasch.trans_eq hScale)

/-- In particular, the part size is 3m for every positive modulus m. -/
theorem main_theorem_cyclic (η : ℝ) (q : ℕ) (hη : 0<η) :
    ∃ N : ℕ, ∃ hN : 1 ≤ N, ∀ (m : ℕ) (hm : N ≤ m),
      letI : NeZero m := ⟨by omega⟩
      ∀(ν : Type) [Fintype ν] (w : ν → Finset (Vertex (ZMod m)) → ℝ),
      (Fintype.card ν : ℝ)≤(Fintype.card (Fin 3 × ZMod m) : ℝ)^q →
      (∀k T,IsAllowed (Rainbow.host 5 (Fin 3 × ZMod m)) (Rainbow.types 5) T → |w k T|≤1) →
      ∃D : Finset (Finset (Vertex (ZMod m))),
        IsDecomposition (Rainbow.host 5 (Fin 3 × ZMod m)) (Rainbow.types 5)
          (edges (Rainbow.host 5 (Fin 3 × ZMod m))) D ∧
        (∀k,|(∑T∈D,w k T)-(∑T∈allowed (Rainbow.host 5 (Fin 3 × ZMod m)) (Rainbow.types 5),
          uniformSeed (Fin 3 × ZMod m) T*w k T)|≤η*(Fintype.card (Fin 3 × ZMod m) : ℝ)^2) ∧
        |(Pasch.count D : ℝ)-Pasch.target (uniformSeed (Fin 3 × ZMod m))
          (allowed (Rainbow.host 5 (Fin 3 × ZMod m)) (Rainbow.types 5))|≤
            η*(Fintype.card (Fin 3 × ZMod m) : ℝ)^2 := by
  obtain ⟨N,hN⟩ := main_theorem η q hη
  refine ⟨max 1 N,le_max_left 1 N,?_⟩
  intro m hm
  letI : NeZero m := ⟨by omega⟩
  have hNm : N ≤ m := (le_max_right 1 N).trans hm
  intro ν _ w hν hw
  obtain ⟨D,hD,hMon,hPasch⟩ := hN (ZMod m) (by simpa only [ZMod.card] using hNm) ν w hν hw
  refine ⟨D,hD,hMon,?_⟩
  exact pasch_error_change_decEq D
    (allowed (Rainbow.host 5 (Fin 3 × ZMod m)) (Rainbow.types 5))
    (uniformSeed (Fin 3 × ZMod m)) (η*(Fintype.card (Fin 3 × ZMod m) : ℝ)^2)
    _ (inferInstance) hPasch

#print axioms main_theorem
#print axioms main_theorem_cyclic
end TypedTriangle.Applications.FivePartite
