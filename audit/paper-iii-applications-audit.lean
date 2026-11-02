module
public import RequestProject.TypedTriangle.ApplicationsBalancedSigns
public import RequestProject.TypedTriangle.ApplicationsFivePartiteBase
public import RequestProject.TypedTriangle.ApplicationsFivePartiteBlowup
public import RequestProject.TypedTriangle.ApplicationsFivePartiteMain
public import RequestProject.TypedTriangle.ApplicationsFivePartiteSeedAssembly
public import RequestProject.TypedTriangle.ApplicationsLatinCore
public import RequestProject.TypedTriangle.ApplicationsLatinCorollaries
public import RequestProject.TypedTriangle.ApplicationsLatinCyclic
public import RequestProject.TypedTriangle.ApplicationsLatinExtraction
public import RequestProject.TypedTriangle.ApplicationsLatinMain
public import RequestProject.TypedTriangle.ApplicationsLatinPaschAlgebra
public import RequestProject.TypedTriangle.ApplicationsLatinPaschClassification
public import RequestProject.TypedTriangle.ApplicationsLatinPaschIntercalates
public import RequestProject.TypedTriangle.ApplicationsLatinPaschTarget
public import RequestProject.TypedTriangle.ApplicationsLatinProfile
public import RequestProject.TypedTriangle.ApplicationsLatinSignedProfile
public import RequestProject.TypedTriangle.ApplicationsOctahedronLedger
public import RequestProject.TypedTriangle.ApplicationsOctahedronTransport
public import RequestProject.TypedTriangle.ApplicationsRainbowDefs
public import RequestProject.TypedTriangle.ApplicationsRainbowGeometry
public import RequestProject.TypedTriangle.ApplicationsRainbowNeighbors
public import RequestProject.TypedTriangle.ExamplesRainbowRetention

open Finset Classical TypedTriangle
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Uniform finite-order Latin statistics and the same square's literal
intercalate count, without geometric or completion hypotheses. -/
example (η : ℝ) (q : ℕ) (hη : 0<η) :
    ∃ N : ℕ, 2≤N ∧ ∀ (A : Type) [Fintype A],
      N≤Fintype.card A → ∀ (ν : Type) [Fintype ν] (w : ν → A → A → A → ℝ),
      (Fintype.card ν : ℝ)≤(Fintype.card A : ℝ)^q →
      (∀ k x y z,|w k x y z|≤1) →
      ∃ L : Applications.Latin.LatinSquare A,
        (∀ k,|(∑ x,∑ y,w k x y (L x y))-
          (∑ x,∑ y,∑ z,(1/(Fintype.card A : ℝ))*w k x y z)|≤η*(Fintype.card A : ℝ)^2) ∧
        |((Applications.Latin.intercalates L).card : ℝ)-
          ((Fintype.card A : ℝ)-1)^3/(4*(Fintype.card A : ℝ))|≤η*(Fintype.card A : ℝ)^2 :=
  TypedTriangle.Applications.Latin.uniform_with_intercalates η q hη

/-- The threshold is uniform over all balanced sign functions. The
profile and its finite-order target are both written explicitly. -/
example (θ η : ℝ) (q : ℕ) (hθ : 0≤θ) (hθOne : θ<1) (hη : 0<η) :
    ∃ N : ℕ, 2≤N ∧ ∀ (A : Type) [Fintype A],
      N≤Fintype.card A → ∀ (σ τ υ : A → ℝ),
      (∀ x,σ x=1 ∨ σ x= -1) → (∀ x,τ x=1 ∨ τ x= -1) →
      (∀ x,υ x=1 ∨ υ x= -1) →
      (∑ x,σ x)=0 → (∑ x,τ x)=0 → (∑ x,υ x)=0 →
      ∀ (ν : Type) [Fintype ν] (w : ν → A → A → A → ℝ),
      (Fintype.card ν : ℝ)≤(Fintype.card A : ℝ)^q →
      (∀ k x y z,|w k x y z|≤1) →
      ∃ L : Applications.Latin.LatinSquare A,
        (∀ k,|(∑ x,∑ y,w k x y (L x y))-
          (∑ x,∑ y,∑ z,((1+θ*σ x*τ y*υ z)/(Fintype.card A : ℝ))*w k x y z)|≤
            η*(Fintype.card A : ℝ)^2) ∧
        |((Applications.Latin.intercalates L).card : ℝ)-
          ((1+θ^4)*((Fintype.card A : ℝ)-1)^3/(4*(Fintype.card A : ℝ))+
            3*θ^2*((Fintype.card A : ℝ)-1)/(2*(Fintype.card A : ℝ)))|≤η*(Fintype.card A : ℝ)^2 := by
  simpa only [Applications.Latin.signedProfile] using
    TypedTriangle.Applications.Latin.signed_profile_with_intercalates θ η q hθ hθOne hη

/-- Even order supplies the balanced signs internally, before the test
family is supplied; no sign witness is a premise of the application. -/
example (η : ℝ) (q : ℕ) (hη : 0<η) :
    ∃ N : ℕ, 2≤N ∧ ∀ (A : Type) [Fintype A],
      N≤Fintype.card A → Even (Fintype.card A) →
      ∃ σ : A → ℝ, (∀ x,σ x=1 ∨ σ x= -1) ∧ (∑ x,σ x)=0 ∧
      ∀ (ν : Type) [Fintype ν] (w : ν → A → A → A → ℝ),
      (Fintype.card ν : ℝ)≤(Fintype.card A : ℝ)^q →
      (∀ k x y z,|w k x y z|≤1) →
      ∃ L : Applications.Latin.LatinSquare A,
        (∀ k,|(∑ x,∑ y,w k x y (L x y))-
          (∑ x,∑ y,∑ z,((1+(1/2)*σ x*σ y*σ z)/(Fintype.card A : ℝ))*w k x y z)|≤
            η*(Fintype.card A : ℝ)^2) ∧
        |((Applications.Latin.intercalates L).card : ℝ)-
          (17*((Fintype.card A : ℝ)-1)^3/(64*(Fintype.card A : ℝ))+
            3*((Fintype.card A : ℝ)-1)/(8*(Fintype.card A : ℝ)))|≤η*(Fintype.card A : ℝ)^2 := by
  simpa only [Applications.Latin.signedProfile] using
    TypedTriangle.Applications.Latin.half_profile_with_intercalates η q hη

/-- Complete five-partite hosts with part size 3m. Physicality, the
uniform diffuse seed and the two geometric conditions are not premises. -/
example (η : ℝ) (q : ℕ) (hη : 0<η) :
    ∃ N : ℕ, ∃ hN : 1 ≤ N, ∀ (m : ℕ) (hm : N ≤ m),
      letI : NeZero m := ⟨by omega⟩
      ∀ (ν : Type) [Fintype ν]
        (w : ν → Finset (Fin 5 × (Fin 3 × ZMod m)) → ℝ),
      (Fintype.card ν : ℝ)≤(3*(m : ℝ))^q →
      (∀ k T, IsAllowed (Applications.Rainbow.host 5 (Fin 3 × ZMod m))
        (Applications.Rainbow.types 5) T → |w k T|≤1) →
      ∃ D : Finset (Finset (Fin 5 × (Fin 3 × ZMod m))),
        IsDecomposition (Applications.Rainbow.host 5 (Fin 3 × ZMod m))
          (Applications.Rainbow.types 5)
          (edges (Applications.Rainbow.host 5 (Fin 3 × ZMod m))) D ∧
        (∀ k,|(∑ T∈D,w k T)-
          (∑ T∈allowed (Applications.Rainbow.host 5 (Fin 3 × ZMod m))
            (Applications.Rainbow.types 5),(1/(9*(m : ℝ)))*w k T)|≤η*(3*(m : ℝ))^2) ∧
        |(Pasch.count D : ℝ)-Pasch.target (fun _ => 1/(9*(m : ℝ)))
          (allowed (Applications.Rainbow.host 5 (Fin 3 × ZMod m))
            (Applications.Rainbow.types 5))|≤η*(3*(m : ℝ))^2 := by
  obtain ⟨N,hN,hMain⟩ := TypedTriangle.Applications.FivePartite.main_theorem_cyclic η q hη
  refine ⟨N,hN,?_⟩
  intro m hm
  letI : NeZero m := ⟨by omega⟩
  have hSeed : Applications.FivePartite.Uniform.uniformSeed (Fin 3 × ZMod m) =
      (fun _ => 1/(9*(m : ℝ))) := by
    funext T
    simp only [Applications.FivePartite.Uniform.uniformSeed,
      Fintype.card_prod,Fintype.card_fin,ZMod.card,Nat.cast_mul,Nat.cast_ofNat,
      ←mul_assoc,show (3 : ℝ)*3=9 by norm_num]
  have hSpecialized := hMain m hm
  rw [hSeed] at hSpecialized
  simpa only [Applications.FivePartite.Vertex,Fintype.card_prod,Fintype.card_fin,
    ZMod.card,Nat.cast_mul,Nat.cast_ofNat] using hSpecialized

section
local instance auditRetentionVertexDecEq {A : Type} : DecidableEq (Fin 5 × A) := Classical.decEq _

/-- Even when both decompositions exist, adding the fifth nonempty part
cannot retain every block of a decomposition on the first four parts. -/
example {A : Type} [Fintype A] [Nonempty A]
    (Dold Dfull : Finset (Finset (Fin 5 × A)))
    (hOld : IsDecomposition (Applications.Rainbow.host 5 A) (Applications.Rainbow.types 5)
      (Examples.RainbowRetention.oldEdges A) Dold)
    (hFull : IsDecomposition (Applications.Rainbow.host 5 A) (Applications.Rainbow.types 5)
      (edges (Applications.Rainbow.host 5 A)) Dfull) : ¬Dold⊆Dfull :=
  TypedTriangle.Examples.RainbowRetention.cannot_retain_old_decomposition Dold Dfull hOld hFull
end

#print axioms TypedTriangle.Applications.FivePartite.Uniform.diffuse_uniformSeed
#print axioms TypedTriangle.Applications.FivePartite.Uniform.edgeThirds
#print axioms TypedTriangle.Applications.FivePartite.Uniform.edgeThirds_card
#print axioms TypedTriangle.Applications.FivePartite.Uniform.edge_triangle_count
#print axioms TypedTriangle.Applications.FivePartite.Uniform.uniformSeed
#print axioms TypedTriangle.Applications.FivePartite.Vertex
#print axioms TypedTriangle.Applications.FivePartite.baseBlocks
#print axioms TypedTriangle.Applications.FivePartite.baseBlocks_allowed
#print axioms TypedTriangle.Applications.FivePartite.baseBlocks_card
#print axioms TypedTriangle.Applications.FivePartite.baseBlocks_decomposition
#print axioms TypedTriangle.Applications.FivePartite.baseBlocks_pair_count
#print axioms TypedTriangle.Applications.FivePartite.baseBlocks_physical
#print axioms TypedTriangle.Applications.FivePartite.block_unique
#print axioms TypedTriangle.Applications.FivePartite.blocks
#print axioms TypedTriangle.Applications.FivePartite.coordinate
#print axioms TypedTriangle.Applications.FivePartite.cyclic_part_card
#print axioms TypedTriangle.Applications.FivePartite.decomposition
#print axioms TypedTriangle.Applications.FivePartite.edge_has_block
#print axioms TypedTriangle.Applications.FivePartite.main_theorem
#print axioms TypedTriangle.Applications.FivePartite.main_theorem_cyclic
#print axioms TypedTriangle.Applications.FivePartite.physical
#print axioms TypedTriangle.Applications.FivePartite.physical_cyclic
#print axioms TypedTriangle.Applications.FivePartite.project
#print axioms TypedTriangle.Applications.Latin.LatinSquare
#print axioms TypedTriangle.Applications.Latin.LatinSquare.add
#print axioms TypedTriangle.Applications.Latin.LatinSquare.cyclic
#print axioms TypedTriangle.Applications.Latin.LatinSquare.transport
#print axioms TypedTriangle.Applications.Latin.Vertex
#print axioms TypedTriangle.Applications.Latin.additive_isPhysical
#print axioms TypedTriangle.Applications.Latin.allowed_eq_image
#print axioms TypedTriangle.Applications.Latin.allowed_iff
#print axioms TypedTriangle.Applications.Latin.balanced_distinctPairSum_first
#print axioms TypedTriangle.Applications.Latin.balanced_distinctPairSum_product
#print axioms TypedTriangle.Applications.Latin.balanced_distinctPairSum_product_scaled
#print axioms TypedTriangle.Applications.Latin.balanced_distinctPairSum_scaled_product
#print axioms TypedTriangle.Applications.Latin.balanced_distinctPairSum_second
#print axioms TypedTriangle.Applications.Latin.balanced_signedBoxSum
#print axioms TypedTriangle.Applications.Latin.balanced_signed_target
#print axioms TypedTriangle.Applications.Latin.card_allowed
#print axioms TypedTriangle.Applications.Latin.card_decomposition
#print axioms TypedTriangle.Applications.Latin.configurations_decomposition_iff
#print axioms TypedTriangle.Applications.Latin.count_decomposition_eq_intercalates
#print axioms TypedTriangle.Applications.Latin.cyclic_isPhysical
#print axioms TypedTriangle.Applications.Latin.decomposition
#print axioms TypedTriangle.Applications.Latin.decomposition_exact
#print axioms TypedTriangle.Applications.Latin.decomposition_ofDecomposition
#print axioms TypedTriangle.Applications.Latin.diffuse_of_marginals
#print axioms TypedTriangle.Applications.Latin.diffuse_of_profile
#print axioms TypedTriangle.Applications.Latin.distinctPairSum
#print axioms TypedTriangle.Applications.Latin.distinctPairSum_add
#print axioms TypedTriangle.Applications.Latin.distinctPairSum_const
#print axioms TypedTriangle.Applications.Latin.distinctPairSum_mul_left
#print axioms TypedTriangle.Applications.Latin.distinctPairSum_mul_right
#print axioms TypedTriangle.Applications.Latin.distinctPairSum_neg
#print axioms TypedTriangle.Applications.Latin.edge01_load
#print axioms TypedTriangle.Applications.Latin.edge01_mem
#print axioms TypedTriangle.Applications.Latin.edge02_load
#print axioms TypedTriangle.Applications.Latin.edge02_mem
#print axioms TypedTriangle.Applications.Latin.edge12_load
#print axioms TypedTriangle.Applications.Latin.edge12_mem
#print axioms TypedTriangle.Applications.Latin.encodeCells
#print axioms TypedTriangle.Applications.Latin.encodeCells_injective
#print axioms TypedTriangle.Applications.Latin.encodeCells_mem_configurations
#print axioms TypedTriangle.Applications.Latin.encode_intercalateCells
#print axioms TypedTriangle.Applications.Latin.eq_symbol_of_mem
#print axioms TypedTriangle.Applications.Latin.exists_unique_symbol
#print axioms TypedTriangle.Applications.Latin.four_mul_count_allowed
#print axioms TypedTriangle.Applications.Latin.four_mul_signed_target
#print axioms TypedTriangle.Applications.Latin.four_mul_target_eq_rooted
#print axioms TypedTriangle.Applications.Latin.half_profile_with_intercalates
#print axioms TypedTriangle.Applications.Latin.host
#print axioms TypedTriangle.Applications.Latin.intercalateCells
#print axioms TypedTriangle.Applications.Latin.intercalates
#print axioms TypedTriangle.Applications.Latin.intercalatesEquivPasch
#print axioms TypedTriangle.Applications.Latin.isDecomposition_iff_latinSquare
#print axioms TypedTriangle.Applications.Latin.isPasch_rooted_classification
#print axioms TypedTriangle.Applications.Latin.latinPasch
#print axioms TypedTriangle.Applications.Latin.latinPasch_isPasch
#print axioms TypedTriangle.Applications.Latin.latinPasch_rooted_injective
#print axioms TypedTriangle.Applications.Latin.latinTriangle
#print axioms TypedTriangle.Applications.Latin.latinTriangle_allowed
#print axioms TypedTriangle.Applications.Latin.latinTriangle_card
#print axioms TypedTriangle.Applications.Latin.latinTriangle_eq_iff
#print axioms TypedTriangle.Applications.Latin.latinTriangle_mem_decomposition
#print axioms TypedTriangle.Applications.Latin.latin_square_with_profile_statistics
#print axioms TypedTriangle.Applications.Latin.latin_square_with_uniform_statistics
#print axioms TypedTriangle.Applications.Latin.mem_decomposition
#print axioms TypedTriangle.Applications.Latin.mem_intercalates
#print axioms TypedTriangle.Applications.Latin.mem_latinTriangle
#print axioms TypedTriangle.Applications.Latin.mem_rootedAlternatives
#print axioms TypedTriangle.Applications.Latin.ofDecomposition
#print axioms TypedTriangle.Applications.Latin.prod_latinPasch
#print axioms TypedTriangle.Applications.Latin.profileConstant
#print axioms TypedTriangle.Applications.Latin.profileConstant_ge_one
#print axioms TypedTriangle.Applications.Latin.root_first_sum_eq_pair_sums
#print axioms TypedTriangle.Applications.Latin.rootedAlternatives
#print axioms TypedTriangle.Applications.Latin.rootedAlternatives_injective
#print axioms TypedTriangle.Applications.Latin.rootedCount_allowed
#print axioms TypedTriangle.Applications.Latin.rooted_configurations_eq_image
#print axioms TypedTriangle.Applications.Latin.rooted_target_sum
#print axioms TypedTriangle.Applications.Latin.signedBoxSum
#print axioms TypedTriangle.Applications.Latin.signedProfile
#print axioms TypedTriangle.Applications.Latin.signedProfile_bounds
#print axioms TypedTriangle.Applications.Latin.signedProfile_diffuse
#print axioms TypedTriangle.Applications.Latin.signedProfile_marginals
#print axioms TypedTriangle.Applications.Latin.signed_parity_box_product
#print axioms TypedTriangle.Applications.Latin.signed_profile_with_intercalates
#print axioms TypedTriangle.Applications.Latin.sum_allowed_eq
#print axioms TypedTriangle.Applications.Latin.sum_decomposition_eq
#print axioms TypedTriangle.Applications.Latin.sum_rootedCount
#print axioms TypedTriangle.Applications.Latin.symbol
#print axioms TypedTriangle.Applications.Latin.symbol_column_bijective
#print axioms TypedTriangle.Applications.Latin.symbol_mem
#print axioms TypedTriangle.Applications.Latin.symbol_row_bijective
#print axioms TypedTriangle.Applications.Latin.target_congr_on
#print axioms TypedTriangle.Applications.Latin.target_constant_eq_count
#print axioms TypedTriangle.Applications.Latin.types
#print axioms TypedTriangle.Applications.Latin.uniform_target
#print axioms TypedTriangle.Applications.Latin.uniform_target_choose
#print axioms TypedTriangle.Applications.Latin.uniform_weight_target
#print axioms TypedTriangle.Applications.Latin.uniform_with_intercalates
#print axioms TypedTriangle.Applications.Latin.weight
#print axioms TypedTriangle.Applications.Latin.weight_exact_marginals
#print axioms TypedTriangle.Applications.Latin.weight_triangle
#print axioms TypedTriangle.Applications.Octahedron.card_support_coreImage
#print axioms TypedTriangle.Applications.Octahedron.core
#print axioms TypedTriangle.Applications.Octahedron.coreImage
#print axioms TypedTriangle.Applications.Octahedron.core_avoids
#print axioms TypedTriangle.Applications.Octahedron.core_support
#print axioms TypedTriangle.Applications.Octahedron.edge_at_one
#print axioms TypedTriangle.Applications.Octahedron.edge_at_zero
#print axioms TypedTriangle.Applications.Octahedron.hinge_of_modes
#print axioms TypedTriangle.Applications.Octahedron.mode
#print axioms TypedTriangle.Applications.Octahedron.mode_card_three
#print axioms TypedTriangle.Applications.Octahedron.mode_cover
#print axioms TypedTriangle.Applications.Octahedron.mode_pairwise
#print axioms TypedTriangle.Applications.Octahedron.support_coreImage
#print axioms TypedTriangle.Applications.Rainbow.allowed_triangle
#print axioms TypedTriangle.Applications.Rainbow.commonNbrCond
#print axioms TypedTriangle.Applications.Rainbow.commonNbrs_card
#print axioms TypedTriangle.Applications.Rainbow.hingeCond
#print axioms TypedTriangle.Applications.Rainbow.hinges_six_card_ge
#print axioms TypedTriangle.Applications.Rainbow.host
#print axioms TypedTriangle.Applications.Rainbow.host_adj
#print axioms TypedTriangle.Applications.Rainbow.host_lab
#print axioms TypedTriangle.Applications.Rainbow.mem_types
#print axioms TypedTriangle.Applications.Rainbow.types
#print axioms TypedTriangle.Applications.exists_balanced_signs
#print axioms TypedTriangle.Examples.RainbowRetention.Vertex
#print axioms TypedTriangle.Examples.RainbowRetention.cannot_retain_old_decomposition
#print axioms TypedTriangle.Examples.RainbowRetention.oldEdges
