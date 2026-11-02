module
public import RequestProject.TypedTriangle.CompletionSeedAssembly
public import RequestProject.TypedTriangle.CompletionScalarStability
public import RequestProject.TypedTriangle.CompletionLogThreshold
public import RequestProject.TypedTriangle.CompletionExternalApplication
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Applications.Latin.Completion

local instance completionDecidableEq {A : Type} : DecidableEq (Vertex A) := instDecidableEqVertex

/-- Named adapters to the external developments. The sampling/circulation
producer and the residual lattice/geometry verifications are deliberately
visible in the final theorem type. They have not been imported from Lean
Pool / Palomar in this checkout. This is a conditional formalization. -/
structure FiniteResidualInputs (θ : ℝ) where
  threshold : ℕ
  sampling : ∀ (A : Type) [Fintype A] (P : PartialLatin A),
    threshold ≤ Fintype.card A → Dense P θ → Nonempty
      (TypedTriangle.Completion.FiniteSeedData (residual P) types (Fintype.card A)
        (1/800000000) (1/100000000) TypedTriangle.Completion.regularizationCoefficient)
  physical : ∀ (A : Type) [Fintype A] (P : PartialLatin A),
    threshold ≤ Fintype.card A → Dense P θ → IsPhysical (residual P) types (edges (residual P))
  common : ∀ (A : Type) [Fintype A] (P : PartialLatin A),
    threshold ≤ Fintype.card A → Dense P θ → CommonNbrCond (residual P) types (1/2000)
  hinge : ∀ (A : Type) [Fintype A] (P : PartialLatin A),
    threshold ≤ Fintype.card A → Dense P θ → HingeCond (residual P) types (1/2000) 6

def FiniteResidualInputs.verifications {θ : ℝ} (inputs : FiniteResidualInputs θ) :
    ResidualVerificationInputs θ (10^55) where
  threshold := max 1 inputs.threshold
  seed := by
    intro A _ P hn hDense
    have hnBase : inputs.threshold ≤ Fintype.card A := (le_max_right _ _).trans hn
    have hnPos : 0 < (Fintype.card A : ℝ) := by
      have hh := (le_max_left 1 inputs.threshold).trans hn
      exact_mod_cast (by omega : 0 < Fintype.card A)
    obtain ⟨data⟩ := inputs.sampling A P hnBase hDense
    apply TypedTriangle.Completion.diffuseSeed_concrete (residual P) types
      (Fintype.card A) hnPos
    · simp [Fintype.card_prod,Fintype.card_fin]
    · exact data
  physical := by
    intro A _ P hn hDense
    exact inputs.physical A P ((le_max_right _ _).trans hn) hDense
  common := by
    intro A _ P hn hDense
    exact inputs.common A P ((le_max_right _ _).trans hn) hDense
  hinge := by
    intro A _ P hn hDense
    exact inputs.hinge A P ((le_max_right _ _).trans hn) hDense

/-- Final conditional theorem at the incrementally improved density.
Its dependencies are theorem arguments rather than new global axioms. -/
theorem improved_partial_latin_completion (η : ℝ) (q : ℕ) (hη : 0 < η)
    (inputs : FiniteResidualInputs TypedTriangle.Completion.improvedDensity) :
    ∃ N : ℕ, ∀ (A : Type) [Fintype A] (P : PartialLatin A),
      N ≤ Fintype.card A → Dense P TypedTriangle.Completion.improvedDensity →
      ∃ μ : Finset (Vertex A) → ℝ, IsDiffuseSeed (residual P) types (10^55) μ ∧
        ∀ (ν : Type) [Fintype ν] (w : ν → Finset (Vertex A) → ℝ),
          (Fintype.card ν : ℝ) ≤ (Fintype.card A : ℝ)^q →
          (∀ k T, IsAllowed (residual P) types T → |w k T| ≤ 1) →
          ∃ (L : LatinSquare A) (D : Finset (Finset (Vertex A))),
            decomposition L=P.triangles ∪ D ∧ P.triangles ⊆ decomposition L ∧
            IsDecomposition (residual P) types (edges (residual P)) D ∧
            (∀ k, |(∑ T ∈ D,w k T)-(∑ T ∈ allowed (residual P) types,μ T*w k T)| ≤
              η*(Fintype.card A : ℝ)^2) ∧
            |(Pasch.count D : ℝ)-Pasch.target μ (allowed (residual P) types)| ≤
              η*(Fintype.card A : ℝ)^2 := by
  exact partial_latin_completion_with_statistics TypedTriangle.Completion.improvedDensity
    (10^55) η q (by norm_num) hη inputs.verifications

#print axioms FiniteResidualInputs.verifications
#print axioms improved_partial_latin_completion

/-- Explicit inputs for the complete conditional route. `assemble` is the
adapter still to be supplied from the external developments: fractional
criterion, sampling/circulation producer, integral transfer and geometry.
Its type is displayed rather than hidden behind an axiom declaration. -/
structure ExternalTheorems (f m : ℝ → ℝ) where
  scalar : TypedTriangle.Completion.ScalarInput TypedTriangle.Completion.certifiedDefect
    TypedTriangle.Completion.certifiedSurplus f m
  plateau : ∀ x, 0 < x → x ≤ TypedTriangle.Completion.improvedDefect → f x=1/2
  tail : ∀ x, 1-TypedTriangle.Completion.improvedDefect < x → x < 1 → f x=0
  assemble : (∀ x y, TypedTriangle.Completion.Admissible x y →
      1 ≤ TypedTriangle.Completion.scalarBound TypedTriangle.Completion.improvedDefect f m x y) →
    FiniteResidualInputs TypedTriangle.Completion.improvedDensity

/-- This wrapper uses the proved continuous-domain margin transport before
invoking the external adapter. The remaining assumptions are parameters. -/
def verifications_from_external_theorems (f m : ℝ → ℝ) (ext : ExternalTheorems f m) :
    ResidualVerificationInputs TypedTriangle.Completion.improvedDensity (10^55) := by
  have hScalar := TypedTriangle.Completion.incremental_scalar_certificate
    f m ext.scalar ext.plateau ext.tail
  apply FiniteResidualInputs.verifications
  apply ext.assemble
  intro x y hxy
  exact (by norm_num [TypedTriangle.Completion.improvedSurplus] :
    (1:ℝ) ≤ TypedTriangle.Completion.improvedSurplus).trans (hScalar x y hxy)

#print axioms verifications_from_external_theorems

theorem improved_partial_latin_completion_from_external (η : ℝ) (q : ℕ) (hη : 0 < η)
    (f m : ℝ → ℝ) (ext : ExternalTheorems f m) :
    ∃ N : ℕ, ∀ (A : Type) [Fintype A] (P : PartialLatin A),
      N ≤ Fintype.card A → Dense P TypedTriangle.Completion.improvedDensity →
      ∃ μ : Finset (Vertex A) → ℝ, IsDiffuseSeed (residual P) types (10^55) μ ∧
        ∀ (ν : Type) [Fintype ν] (w : ν → Finset (Vertex A) → ℝ),
          (Fintype.card ν : ℝ) ≤ (Fintype.card A : ℝ)^q →
          (∀ k T, IsAllowed (residual P) types T → |w k T| ≤ 1) →
          ∃ (L : LatinSquare A) (D : Finset (Finset (Vertex A))),
            decomposition L=P.triangles ∪ D ∧ P.triangles ⊆ decomposition L ∧
            IsDecomposition (residual P) types (edges (residual P)) D ∧
            (∀ k, |(∑ T ∈ D,w k T)-(∑ T ∈ allowed (residual P) types,μ T*w k T)| ≤
              η*(Fintype.card A : ℝ)^2) ∧
            |(Pasch.count D : ℝ)-Pasch.target μ (allowed (residual P) types)| ≤
              η*(Fintype.card A : ℝ)^2 := by
  exact partial_latin_completion_with_statistics TypedTriangle.Completion.improvedDensity
    (10^55) η q (by norm_num) hη (verifications_from_external_theorems f m ext)

#print axioms improved_partial_latin_completion_from_external
end TypedTriangle.Applications.Latin.Completion
