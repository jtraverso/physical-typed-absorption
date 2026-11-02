/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Triangle decompositions III: physical typed absorption and prescribed statistics

The compared statements are Theorem T (`main_theorem_T`), its strengthening T+ with
prescribed triangle statistics and the Pasch count
(`main_theorem_T_with_triangle_monitors_and_pasch`), the Latin-square applications
(`latin_square_with_profile_statistics`, `uniform_with_intercalates`,
`signed_profile_with_intercalates`, `latin_two_scale_with_blocks`) and the balanced
five-partite application (`FivePartite.main_theorem`).

All definitions below are reproduced from the frozen proof library (preprint 1.0 source
supplement) with their original names, bodies, options and `open` declarations. Only Mathlib
is imported here. Solution imports the proofs.
-/

@[expose] public section

/-! ### Definitions (D1)–(D7): `RequestProject/TypedTriangle/Defs.lean` -/

section
open Finset

noncomputable section
open Classical

namespace TypedTriangle

/-- Un host: un grafo simple finito junto con un etiquetado `lab : V → I`. -/
structure Host (V I : Type*) where
  G : SimpleGraph V
  lab : V → I

variable {V I : Type*} [Fintype V]

/-- `E(T)`: las aristas (pares no diagonales) de un conjunto de vértices `T`. -/
def triEdges (T : Finset V) : Finset (Sym2 V) := T.sym2.filter (fun e => ¬ e.IsDiag)

/-- Las aristas del host como `Finset`. -/
def edges (H : Host V I) : Finset (Sym2 V) := univ.filter (fun e => e ∈ H.G.edgeSet)

/-- Triángulo permitido: tres vértices distintos, mutuamente adyacentes, cuyo multiconjunto
de etiquetas está en `F`. -/
def IsAllowed (H : Host V I) (F : Set (Multiset I)) (T : Finset V) : Prop :=
  T.card = 3 ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → H.G.Adj x y) ∧ T.val.map H.lab ∈ F

/-- `𝒯(G)`: la familia de triángulos permitidos. -/
def allowed (H : Host V I) (F : Set (Multiset I)) : Finset (Finset V) :=
  univ.filter (IsAllowed H F)

/-- (D1) `D` es una descomposición permitida del conjunto de aristas `J`. -/
def IsDecomposition (H : Host V I) (F : Set (Multiset I)) (J : Finset (Sym2 V))
    (D : Finset (Finset V)) : Prop :=
  (∀ T ∈ D, IsAllowed H F T) ∧ (D : Set (Finset V)).PairwiseDisjoint triEdges ∧
    D.biUnion triEdges = J

/-- Indicador entero `𝟏_J` de un conjunto de aristas. -/
def ind (J : Finset (Sym2 V)) : Sym2 V → ℤ := fun e => if e ∈ J then 1 else 0

/-- (D2) Retículo físico `Λ_G`: combinaciones enteras de indicadores de triángulos permitidos. -/
def lattice (H : Host V I) (F : Set (Multiset I)) : Submodule ℤ (Sym2 V → ℤ) :=
  Submodule.span ℤ ((fun T => ind (triEdges T)) '' {T | IsAllowed H F T})

/-- `J` es físico en `G`: `𝟏_J ∈ Λ_G`. -/
def IsPhysical (H : Host V I) (F : Set (Multiset I)) (J : Finset (Sym2 V)) : Prop :=
  ind J ∈ lattice H F

/-- (D3) Semilla exacta difusa de constante `C`. -/
def IsDiffuseSeed (H : Host V I) (F : Set (Multiset I)) (C : ℝ) (φ : Finset V → ℝ) : Prop :=
  (∀ T, IsAllowed H F T →
      1 / (C * Fintype.card V) ≤ φ T ∧ φ T ≤ C / Fintype.card V) ∧
    ∀ e ∈ H.G.edgeSet, ∑ T ∈ (allowed H F).filter (fun T => e ∈ triEdges T), φ T = 1

/-- (D4) Vecinos comunes de `u, v` con etiqueta `k`. -/
def commonNbrs (H : Host V I) (k : I) (u v : V) : Finset V :=
  univ.filter (fun w => H.G.Adj u w ∧ H.G.Adj v w ∧ H.lab w = k)

/-- (D5) Condición de vecinos comunes (para todos los pares distintos, sean o no aristas). -/
def CommonNbrCond (H : Host V I) (F : Set (Multiset I)) (α : ℝ) : Prop :=
  ∀ u v : V, u ≠ v → ∀ k : I, ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
    α * Fintype.card V ≤ (commonNbrs H k u v).card

/-- Vértices incidentes con alguna arista de `J` (soporte). -/
def support (J : Finset (Sym2 V)) : Finset V := univ.filter (fun x => ∃ e ∈ J, x ∈ e)

/-- (D6) La cuña `W_a = {ua, va}`. -/
def wedge (u v a : V) : Finset (Sym2 V) := {s(u, a), s(v, a)}

/-- Bisagra física para el par `T_a = {u,v,a}`, `T_b = {u,v,b}`. -/
def IsHinge (H : Host V I) (F : Set (Multiset I)) (u v a b : V) (J : Finset (Sym2 V)) :
    Prop :=
  J ⊆ edges H ∧ Disjoint J (triEdges {u, v, a} ∪ triEdges {u, v, b}) ∧
    (∃ D, IsDecomposition H F (J ∪ wedge u v a) D) ∧
    (∃ D, IsDecomposition H F (J ∪ wedge u v b) D)

/-- `𝓗_i(T_a,T_b)`: bisagras (como conjuntos de aristas) de orden exactamente `i`. -/
def hinges (H : Host V I) (F : Set (Multiset I)) (u v a b : V) (i : ℕ) :
    Finset (Finset (Sym2 V)) :=
  univ.filter (fun J => IsHinge H F u v a b J ∧ (support J).card = i)

/-- (D7) Condición de bisagras. -/
def HingeCond (H : Host V I) (F : Set (Multiset I)) (α : ℝ) (h : ℕ) : Prop :=
  ∀ u v a b : V, a ≠ b → IsAllowed H F {u, v, a} → IsAllowed H F {u, v, b} →
    ∃ i, 6 ≤ i ∧ i ≤ h ∧
      α * (Fintype.card V : ℝ) ^ (i - 4) ≤ (hinges H F u v a b i).card

end TypedTriangle

end
end

/-! ### Pattern statistics: `RequestProject/TypedTriangle/PatternStatistics.lean` -/

section
open Finset
noncomputable section
open Classical
set_option autoImplicit false
namespace TypedTriangle.PatternStatistics

def statistic {A : Type*} (w : Finset A → ℝ) (l : ℕ) (D : Finset A) : ℝ :=
  ∑ S ∈ D.powersetCard l, w S

end TypedTriangle.PatternStatistics
end
end

/-! ### Pasch configurations: `RequestProject/TypedTriangle/PaschStatistics.lean` -/

section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TypedTriangle.Pasch

/-- An unoriented Pasch configuration: four linear triples on six vertices,
with each vertex incident to exactly two triples. -/
def IsPasch {V : Type*} [DecidableEq V] (S : Finset (Finset V)) : Prop :=
  S.card = 4 ∧ (∀ T ∈ S, T.card = 3) ∧ (S.biUnion id).card = 6 ∧
    (∀ v ∈ S.biUnion id, (S.filter (fun T => v ∈ T)).card = 2) ∧
      (S : Set (Finset V)).Pairwise (fun A B => (A ∩ B).card ≤ 1)

instance decidableIsPasch {V : Type*} [DecidableEq V] (S : Finset (Finset V)) :
    Decidable (IsPasch S) := by unfold IsPasch; infer_instance

def configurations {V : Type*} [DecidableEq V] (D : Finset (Finset V)) : Finset (Finset (Finset V)) :=
  (D.powersetCard 4).filter IsPasch

def count {V : Type*} [DecidableEq V] (D : Finset (Finset V)) : ℕ := (configurations D).card

def weight {V : Type*} [DecidableEq V] (w : Finset (Finset V) → ℝ) (S : Finset (Finset V)) : ℝ :=
  if IsPasch S then w S else 0

def statistic {V : Type*} [DecidableEq V] (w : Finset (Finset V) → ℝ) (D : Finset (Finset V)) : ℝ :=
  PatternStatistics.statistic (weight w) 4 D

def target {V : Type*} [DecidableEq V] (μ : Finset V → ℝ) (D : Finset (Finset V)) : ℝ :=
  statistic (fun S => ∏ T ∈ S, μ T) D

end TypedTriangle.Pasch
end
end

/-! ### Rainbow hosts: `RequestProject/TypedTriangle/ApplicationsRainbowDefs.lean` -/

section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Applications.Rainbow

/-- Complete multipartite host with equally sized labelled parts. -/
def host (k : ℕ) (A : Type) : Host (Fin k × A) (Fin k) where
  G := {
    Adj := fun u v => u.1 ≠ v.1
    symm := ⟨fun _ _ h => h.symm⟩
    loopless := ⟨fun _ h => h rfl⟩ }
  lab := Prod.fst

/-- The allowed label multisets have no repeated colour. -/
def types (k : ℕ) : Set (Multiset (Fin k)) := {s | s.Nodup}

end TypedTriangle.Applications.Rainbow
end
end

/-! ### Latin squares: `RequestProject/TypedTriangle/ApplicationsLatinCore.lean` -/

section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin

abbrev Vertex (A : Type) := Fin 3 × A
abbrev host (A : Type) := Rainbow.host 3 A
abbrev types := Rainbow.types 3

def latinTriangle {A : Type} (x y z : A) : Finset (Vertex A) :=
  {(0,x),(1,y),(2,z)}

/-- A Latin square: every row and every column is a permutation. -/
structure LatinSquare (A : Type) where
  toFun : A → A → A
  row_bijective : ∀ x, Function.Bijective (toFun x)
  column_bijective : ∀ y, Function.Bijective (fun x => toFun x y)

instance {A : Type} : CoeFun (LatinSquare A) (fun _ => A → A → A) := ⟨LatinSquare.toFun⟩

def decomposition {A : Type} [Fintype A] (L : LatinSquare A) : Finset (Finset (Vertex A)) :=
  univ.image (fun p : A×A => latinTriangle p.1 p.2 (L p.1 p.2))

end TypedTriangle.Applications.Latin
end
end

/-! ### Triangle weights of a stochastic array: `ApplicationsLatinProfile.lean` -/

section
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

end TypedTriangle.Applications.Latin
end
end

/-! ### Intercalates: `ApplicationsLatinPaschIntercalates.lean` -/

section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin

/-- The usual alternating two by two subarray, without ordering its rows
or columns. Each element of this finset is its literal four-cell set. -/
def intercalateCells {A : Type} (r r' c c' : A) : Finset (A×A) :=
  {(r,c),(r,c'),(r',c),(r',c')}

def intercalates {A : Type} [Fintype A] (L : LatinSquare A) : Finset (Finset (A×A)) :=
  ((univ : Finset (A×A×A×A)).filter (fun p =>
    p.2.1 ≠ p.1 ∧ p.2.2.2 ≠ p.2.2.1 ∧
      L p.2.1 p.2.2.1=L p.1 p.2.2.2 ∧ L p.2.1 p.2.2.2=L p.1 p.2.2.1)).image
    (fun p => intercalateCells p.1 p.2.1 p.2.2.1 p.2.2.2)

end TypedTriangle.Applications.Latin
end
end

/-! ### Signed profiles: `ApplicationsLatinSignedProfile.lean` -/

section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace TypedTriangle.Applications.Latin

/-- A bounded rank-one perturbation of the uniform stochastic array. -/
def signedProfile {A : Type} [Fintype A] (θ : ℝ) (σ τ υ : A → ℝ) (x y z : A) : ℝ :=
  (1+θ*σ x*τ y*υ z)/(Fintype.card A : ℝ)

end TypedTriangle.Applications.Latin
end
end

/-! ### Two-scale statistics: `ApplicationsTwoScaleRounding.lean` -/

section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin.TwoScale

def kappa (θ t : ℝ) : ℝ := (1+θ^4)*(1+t^4)/4

def linearTarget {A : Type} [Fintype A]
    (p w : A → A → A → ℝ) : ℝ := ∑ r,∑ c,∑ s,p r c s*w r c s

def linearStatistic {A : Type} [Fintype A]
    (L : LatinSquare A) (w : A → A → A → ℝ) : ℝ := ∑ r,∑ c,w r c (L r c)

end TypedTriangle.Applications.Latin.TwoScale
end
end

/-! ### Coarse blocks: `ApplicationsTwoScaleFinal.lean` -/

section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin.TwoScale

def bitSign (a : Bool) : ℝ := if a then 1 else -1

def blockCount {A : Type} [Fintype A] (L : LatinSquare A)
    (σ τ υ : A → ℝ) (a b d : ℝ) : ℕ :=
  ((univ : Finset (A × A)).filter (fun rc =>
    σ rc.1=a ∧ τ rc.2=b ∧ υ (L rc.1 rc.2)=d)).card

end TypedTriangle.Applications.Latin.TwoScale
end
end

/-! ### Five-partite vertices: `ApplicationsFivePartiteBlowup.lean` -/

section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Applications.FivePartite

abbrev Vertex (A : Type) := Fin 5 × (Fin 3 × A)

end TypedTriangle.Applications.FivePartite
end
end

/-! ### The uniform seed: `ApplicationsFivePartiteSeedAssembly.lean` -/

section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Applications.FivePartite.Uniform

/-- The canonical fractional decomposition gives weight 1/(3n) to every
rainbow triangle, where n is the size of each part. -/
def uniformSeed (A : Type) [Fintype A] (_T : Finset (Fin 5 × A)) : ℝ :=
  1/(3*(Fintype.card A : ℝ))

end TypedTriangle.Applications.FivePartite.Uniform
end
end

/-! ### Theorem T: `RequestProject/TypedTriangle/MainPaperIII.lean` -/

section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex

/-- **Theorem T.** Under H1–H4 (a diffuse exact seed, physicality of the edge set, the
common-neighbour condition and the hinge condition) every sufficiently large host has an
allowed triangle decomposition. -/
theorem main_theorem_T {I : Type} (F : Set (Multiset I))
    (αOriginal C : ℝ) (hOriginal : ℕ)
    (hαOriginal : 0 < αOriginal) (hC : 1 ≤ C) (hhOriginal : 6 ≤ hOriginal) :
    ∃ n₀ : ℕ, ∀ {X : Type} [Fintype X] (H : Host X I),
      n₀ ≤ Fintype.card X →
      (∃ μ : Finset X → ℝ, IsDiffuseSeed H F C μ) →
      IsPhysical H F (edges H) → CommonNbrCond H F αOriginal →
      HingeCond H F αOriginal hOriginal →
      ∃ D : Finset (Finset X), IsDecomposition H F (edges H) D := by
  sorry

end TypedTriangle.Vortex
end
end

/-! ### Theorem T+: `RequestProject/TypedTriangle/MainPaperIIIPasch.lean` -/

section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex
open Pasch

/-- **Theorem T+.** The decomposition of Theorem T can be chosen so that polynomially many
bounded triangle statistics and the Pasch count are close to their values under the seed. -/
theorem main_theorem_T_with_triangle_monitors_and_pasch {I : Type} (F : Set (Multiset I))
    (αOriginal C η : ℝ) (hOriginal qStat : ℕ)
    (hαOriginal : 0 < αOriginal) (hC : 1 ≤ C) (hhOriginal : 6 ≤ hOriginal) (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ {X : Type} [Fintype X] (H : Host X I) (μ : Finset X → ℝ),
      n₀ ≤ Fintype.card X → IsDiffuseSeed H F C μ →
      IsPhysical H F (edges H) → CommonNbrCond H F αOriginal →
      HingeCond H F αOriginal hOriginal →
      ∀ (ν : Type) [Fintype ν] (w : ν → Finset X → ℝ),
      (Fintype.card ν : ℝ) ≤ (Fintype.card X : ℝ)^qStat →
      (∀ k Q, IsAllowed H F Q → |w k Q| ≤ 1) →
      ∃ D : Finset (Finset X), IsDecomposition H F (edges H) D ∧
        (∀ k, |(∑ Q ∈ D, w k Q)-(∑ Q ∈ allowed H F, μ Q*w k Q)| ≤
          η*(Fintype.card X : ℝ)^2) ∧
        |(Pasch.count D : ℝ)-Pasch.target μ (allowed H F)| ≤ η*(Fintype.card X : ℝ)^2 := by
  sorry

end TypedTriangle.Vortex
end
end

/-! ### Latin squares with prescribed statistics: `ApplicationsLatinMain.lean` -/

section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin

/-- Latin squares following a bounded stochastic profile: polynomially many bounded linear
statistics and the Pasch count of the associated triangle decomposition are prescribed. -/
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
  sorry

end TypedTriangle.Applications.Latin
end
end

/-! ### Uniform and signed profiles with intercalates: `ApplicationsLatinCorollaries.lean` -/

section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin

/-- Uniform finite-order Latin statistics together with the literal intercalate count. -/
theorem uniform_with_intercalates (η : ℝ) (q : ℕ) (hη : 0<η) :
    ∃ N : ℕ, 2≤N ∧ ∀ (A : Type) [Fintype A],
      N≤Fintype.card A → ∀ (ν : Type) [Fintype ν] (w : ν → A → A → A → ℝ),
      (Fintype.card ν : ℝ)≤(Fintype.card A : ℝ)^q →
      (∀ k x y z,|w k x y z|≤1) →
      ∃ L : LatinSquare A,
        (∀ k,|(∑ x,∑ y,w k x y (L x y))-
          (∑ x,∑ y,∑ z,(1/(Fintype.card A : ℝ))*w k x y z)|≤η*(Fintype.card A : ℝ)^2) ∧
        |((intercalates L).card : ℝ)-
          ((Fintype.card A : ℝ)-1)^3/(4*(Fintype.card A : ℝ))|≤η*(Fintype.card A : ℝ)^2 := by
  sorry

/-- Signed rank-one profiles: prescribed statistics and the predicted intercalate count. -/
theorem signed_profile_with_intercalates (θ η : ℝ) (q : ℕ)
    (hθ : 0≤θ) (hθOne : θ<1) (hη : 0<η) :
    ∃ N : ℕ, 2≤N ∧ ∀ (A : Type) [Fintype A],
      N≤Fintype.card A → ∀ (σ τ υ : A → ℝ),
      (∀ x,σ x=1 ∨ σ x= -1) → (∀ x,τ x=1 ∨ τ x= -1) →
      (∀ x,υ x=1 ∨ υ x= -1) →
      (∑ x,σ x)=0 → (∑ x,τ x)=0 → (∑ x,υ x)=0 →
      ∀ (ν : Type) [Fintype ν] (w : ν → A → A → A → ℝ),
      (Fintype.card ν : ℝ)≤(Fintype.card A : ℝ)^q →
      (∀ k x y z,|w k x y z|≤1) →
      ∃ L : LatinSquare A,
        (∀ k,|(∑ x,∑ y,w k x y (L x y))-
          (∑ x,∑ y,∑ z,signedProfile θ σ τ υ x y z*w k x y z)|≤η*(Fintype.card A : ℝ)^2) ∧
        |((intercalates L).card : ℝ)-
          ((1+θ^4)*((Fintype.card A : ℝ)-1)^3/(4*(Fintype.card A : ℝ))+
            3*θ^2*((Fintype.card A : ℝ)-1)/(2*(Fintype.card A : ℝ)))|≤η*(Fintype.card A : ℝ)^2 := by
  sorry

end TypedTriangle.Applications.Latin
end
end

/-! ### Two-scale Latin squares: `ApplicationsTwoScaleFinal.lean` -/

section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin.TwoScale

/-- Two Latin squares with the same prescribed statistics and the same eight coarse blocks,
whose intercalate counts are close to `κ(θ,0) n²` and `κ(θ,t) n²`. -/
theorem latin_two_scale_with_blocks (θ t ε : ℝ) (q : ℕ)
    (hθ : 0≤θ) (hθ1 : θ<1) (ht : 0≤t) (ht1 : t<1) (hε : 0<ε) :
    ∃ N : ℕ, 12≤N ∧ ∀ (A : Type) [Fintype A], N≤Fintype.card A →
      4 ∣ Fintype.card A → ∀ (σ τ υ : A → ℝ),
      (∀ a, σ a=1 ∨ σ a= -1) → (∀ a, τ a=1 ∨ τ a= -1) → (∀ a, υ a=1 ∨ υ a= -1) →
      (∑ a,σ a)=0 → (∑ a,τ a)=0 → (∑ a,υ a)=0 →
      ∀ (J : Type) [Fintype J] (w : J → A → A → A → ℝ),
      (Fintype.card J : ℝ)≤(Fintype.card A : ℝ)^q →
      (∀ j r c s, |w j r c s|≤1) →
      ∃ L₀ Lₜ : LatinSquare A,
        (∀ j, |linearStatistic L₀ (w j)-linearTarget (signedProfile θ σ τ υ) (w j)|≤
          ε*(Fintype.card A : ℝ)^2) ∧
        (∀ j, |linearStatistic Lₜ (w j)-linearTarget (signedProfile θ σ τ υ) (w j)|≤
          ε*(Fintype.card A : ℝ)^2) ∧
        (∀ a b d : Bool,
          |(blockCount L₀ σ τ υ (bitSign a) (bitSign b) (bitSign d) : ℝ)-
            (1+θ*bitSign a*bitSign b*bitSign d)*(Fintype.card A : ℝ)^2/8|≤ε*(Fintype.card A : ℝ)^2) ∧
        (∀ a b d : Bool,
          |(blockCount Lₜ σ τ υ (bitSign a) (bitSign b) (bitSign d) : ℝ)-
            (1+θ*bitSign a*bitSign b*bitSign d)*(Fintype.card A : ℝ)^2/8|≤ε*(Fintype.card A : ℝ)^2) ∧
        |((intercalates L₀).card : ℝ)-kappa θ 0*(Fintype.card A : ℝ)^2|≤ε*(Fintype.card A : ℝ)^2 ∧
        |((intercalates Lₜ).card : ℝ)-kappa θ t*(Fintype.card A : ℝ)^2|≤ε*(Fintype.card A : ℝ)^2 := by
  sorry

end TypedTriangle.Applications.Latin.TwoScale
end
end

/-! ### The balanced five-partite graph: `ApplicationsFivePartiteMain.lean` -/

section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.FivePartite
open _root_.TypedTriangle.Applications.FivePartite.Uniform

/-- Theorem T+ on the balanced complete five-partite graph with parts of size `3|A|` and the
rainbow triangles: prescribed statistics and Pasch count relative to the uniform seed. -/
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
  sorry

end TypedTriangle.Applications.FivePartite
end
end
