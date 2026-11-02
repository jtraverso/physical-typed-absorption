module
public import RequestProject.TypedTriangle.TowerTriangleThresholdAssembly
@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace TypedTriangle.PrintedHeight

/-! Complete arithmetic expansion of the triangle-monitor height.
All definitions below use only natural-number arithmetic and finite recursion.
The final theorem checks identity with the original audited height. -/

def initialHingeOrder (h : ℕ) : ℕ := 2*h-3

theorem initialHingeOrder_agrees : initialHingeOrder = TypedTriangle.TowerBounds.initialHingeOrder := by
  funext h
  simp only [initialHingeOrder, TypedTriangle.TowerBounds.initialHingeOrder]

def compressionPowerMajorant (M : ℕ) : ℕ := 2^(M^2)

theorem compressionPowerMajorant_agrees : compressionPowerMajorant = TypedTriangle.TowerBounds.compressionPowerMajorant := by
  funext M
  simp only [compressionPowerMajorant, TypedTriangle.TowerBounds.compressionPowerMajorant]

def hingeDensityMajorant (M : ℕ) : ℕ :=
  (M^3*M^(2*M+1))*((2048*M^2)*compressionPowerMajorant (2*M))

theorem hingeDensityMajorant_agrees : hingeDensityMajorant = TypedTriangle.TowerBounds.hingeDensityMajorant := by
  funext M
  simp only [hingeDensityMajorant, TypedTriangle.TowerBounds.hingeDensityMajorant, compressionPowerMajorant_agrees]

def normalizedDensityMajorant (K : ℕ) : ℕ := max K (hingeDensityMajorant K)*8

theorem normalizedDensityMajorant_agrees : normalizedDensityMajorant = TypedTriangle.TowerBounds.normalizedDensityMajorant := by
  funext K
  simp only [normalizedDensityMajorant, TypedTriangle.TowerBounds.normalizedDensityMajorant, hingeDensityMajorant_agrees]

def normalizedInputScale (K : ℕ) : ℕ := K+2*K+normalizedDensityMajorant K+1

theorem normalizedInputScale_agrees : normalizedInputScale = TypedTriangle.TowerBounds.normalizedInputScale := by
  funext K
  simp only [normalizedInputScale, TypedTriangle.TowerBounds.normalizedInputScale, normalizedDensityMajorant_agrees]

def thresholdWorkingScale (K : ℕ) : ℕ := normalizedInputScale K*32

theorem thresholdWorkingScale_agrees : thresholdWorkingScale = TypedTriangle.TowerBounds.thresholdWorkingScale := by
  funext K
  simp only [thresholdWorkingScale, TypedTriangle.TowerBounds.thresholdWorkingScale, normalizedInputScale_agrees]

def deletionBudgetMajorant (M : ℕ) : ℕ := max 2 (M*(4*compressionPowerMajorant (M+1)))

theorem deletionBudgetMajorant_agrees : deletionBudgetMajorant = TypedTriangle.TowerBounds.deletionBudgetMajorant := by
  funext M
  simp only [deletionBudgetMajorant, TypedTriangle.TowerBounds.deletionBudgetMajorant, compressionPowerMajorant_agrees]

def nestedBudgetMajorant (M : ℕ) : ℕ :=
  max (deletionBudgetMajorant M) (M*(128*compressionPowerMajorant (M+1)))

theorem nestedBudgetMajorant_agrees : nestedBudgetMajorant = TypedTriangle.TowerBounds.nestedBudgetMajorant := by
  funext M
  simp only [nestedBudgetMajorant, TypedTriangle.TowerBounds.nestedBudgetMajorant, compressionPowerMajorant_agrees, deletionBudgetMajorant_agrees]

def coreToleranceMajorant (M : ℕ) : ℕ := max (max (deletionBudgetMajorant M) (nestedBudgetMajorant M)) 2

theorem coreToleranceMajorant_agrees : coreToleranceMajorant = TypedTriangle.TowerBounds.coreToleranceMajorant := by
  funext M
  simp only [coreToleranceMajorant, TypedTriangle.TowerBounds.coreToleranceMajorant, deletionBudgetMajorant_agrees, nestedBudgetMajorant_agrees]

def preparationToleranceMajorant (M : ℕ) : ℕ :=
  max (max (nestedBudgetMajorant M) (coreToleranceMajorant M)) (max 2 (M*(2*compressionPowerMajorant M)))

theorem preparationToleranceMajorant_agrees : preparationToleranceMajorant = TypedTriangle.TowerBounds.preparationToleranceMajorant := by
  funext M
  simp only [preparationToleranceMajorant, TypedTriangle.TowerBounds.preparationToleranceMajorant, compressionPowerMajorant_agrees, coreToleranceMajorant_agrees, nestedBudgetMajorant_agrees]

def hingeRatioMajorant (M k : ℕ) : ℕ := M*(k*compressionPowerMajorant M)

theorem hingeRatioMajorant_agrees : hingeRatioMajorant = TypedTriangle.TowerBounds.hingeRatioMajorant := by
  funext M k
  simp only [hingeRatioMajorant, TypedTriangle.TowerBounds.hingeRatioMajorant, compressionPowerMajorant_agrees]

def rawToleranceMajorant (M : ℕ) : ℕ :=
  max (preparationToleranceMajorant (M*4)) (max (hingeRatioMajorant M 4) (8*max 1 (2*M)))

theorem rawToleranceMajorant_agrees : rawToleranceMajorant = TypedTriangle.TowerBounds.rawToleranceMajorant := by
  funext M
  simp only [rawToleranceMajorant, TypedTriangle.TowerBounds.rawToleranceMajorant, hingeRatioMajorant_agrees, preparationToleranceMajorant_agrees]

def sampleLcMajorant (M : ℕ) : ℕ := 30*M+1

theorem sampleLcMajorant_agrees : sampleLcMajorant = TypedTriangle.TowerBounds.sampleLcMajorant := by
  funext M
  simp only [sampleLcMajorant, TypedTriangle.TowerBounds.sampleLcMajorant]

def sampleAMajorant (M : ℕ) : ℕ := 3*M*(27*M^3+1+M)+M

theorem sampleAMajorant_agrees : sampleAMajorant = TypedTriangle.TowerBounds.sampleAMajorant := by
  funext M
  simp only [sampleAMajorant, TypedTriangle.TowerBounds.sampleAMajorant]

def sampleTMajorant (M : ℕ) : ℕ := 6*sampleAMajorant M*M+1

theorem sampleTMajorant_agrees : sampleTMajorant = TypedTriangle.TowerBounds.sampleTMajorant := by
  funext M
  simp only [sampleTMajorant, TypedTriangle.TowerBounds.sampleTMajorant, sampleAMajorant_agrees]

def sampleJMajorant (M : ℕ) : ℕ :=
  max (4*M) (max (12*(sampleLcMajorant M+1)*M)
    (6*(sampleLcMajorant M+1)*(sampleTMajorant M+1)*M))+1

theorem sampleJMajorant_agrees : sampleJMajorant = TypedTriangle.TowerBounds.sampleJMajorant := by
  funext M
  simp only [sampleJMajorant, TypedTriangle.TowerBounds.sampleJMajorant, sampleLcMajorant_agrees, sampleTMajorant_agrees]

def sampleEtaMajorant (M : ℕ) : ℕ := 2^sampleJMajorant M

theorem sampleEtaMajorant_agrees : sampleEtaMajorant = TypedTriangle.TowerBounds.sampleEtaMajorant := by
  funext M
  simp only [sampleEtaMajorant, TypedTriangle.TowerBounds.sampleEtaMajorant, sampleJMajorant_agrees]

def sampleLMajorant (M : ℕ) : ℕ := 2*M*sampleEtaMajorant M+1

theorem sampleLMajorant_agrees : sampleLMajorant = TypedTriangle.TowerBounds.sampleLMajorant := by
  funext M
  simp only [sampleLMajorant, TypedTriangle.TowerBounds.sampleLMajorant, sampleEtaMajorant_agrees]

def compressionClipMajorant (M : ℕ) : ℕ := M+1

theorem compressionClipMajorant_agrees : compressionClipMajorant = TypedTriangle.TowerBounds.compressionClipMajorant := by
  funext M
  simp only [compressionClipMajorant, TypedTriangle.TowerBounds.compressionClipMajorant]

def compressionThetaMajorant (M : ℕ) : ℕ := compressionClipMajorant M*(64*compressionPowerMajorant M)

theorem compressionThetaMajorant_agrees : compressionThetaMajorant = TypedTriangle.TowerBounds.compressionThetaMajorant := by
  funext M
  simp only [compressionThetaMajorant, TypedTriangle.TowerBounds.compressionThetaMajorant, compressionClipMajorant_agrees, compressionPowerMajorant_agrees]

def compressionKappaMajorant (M : ℕ) : ℕ :=
  max ((compressionClipMajorant M*2)*4)
    (((compressionThetaMajorant M*4)*(compressionThetaMajorant M*2))*16)

theorem compressionKappaMajorant_agrees : compressionKappaMajorant = TypedTriangle.TowerBounds.compressionKappaMajorant := by
  funext M
  simp only [compressionKappaMajorant, TypedTriangle.TowerBounds.compressionKappaMajorant, compressionClipMajorant_agrees, compressionThetaMajorant_agrees]

def compressionPrecisionMajorant (M : ℕ) : ℕ :=
  (compressionClipMajorant M*compressionThetaMajorant M)*16

theorem compressionPrecisionMajorant_agrees : compressionPrecisionMajorant = TypedTriangle.TowerBounds.compressionPrecisionMajorant := by
  funext M
  simp only [compressionPrecisionMajorant, TypedTriangle.TowerBounds.compressionPrecisionMajorant, compressionClipMajorant_agrees, compressionThetaMajorant_agrees]

def compressionInitialMajorant (M : ℕ) : ℕ :=
  32*(compressionClipMajorant M*compressionThetaMajorant M^2)

theorem compressionInitialMajorant_agrees : compressionInitialMajorant = TypedTriangle.TowerBounds.compressionInitialMajorant := by
  funext M
  simp only [compressionInitialMajorant, TypedTriangle.TowerBounds.compressionInitialMajorant, compressionClipMajorant_agrees, compressionThetaMajorant_agrees]

def compressionInputMajorant (M : ℕ) : ℕ :=
  2*compressionClipMajorant M+compressionKappaMajorant M+
    compressionPrecisionMajorant M+compressionInitialMajorant M+1

theorem compressionInputMajorant_agrees : compressionInputMajorant = TypedTriangle.TowerBounds.compressionInputMajorant := by
  funext M
  simp only [compressionInputMajorant, TypedTriangle.TowerBounds.compressionInputMajorant, compressionClipMajorant_agrees, compressionInitialMajorant_agrees, compressionKappaMajorant_agrees, compressionPrecisionMajorant_agrees]

def sampleQMajorant (M : ℕ) : ℕ :=
  9*sampleLMajorant M*M*sampleEtaMajorant M*M+1+M

theorem sampleQMajorant_agrees : sampleQMajorant = TypedTriangle.TowerBounds.sampleQMajorant := by
  funext M
  simp only [sampleQMajorant, TypedTriangle.TowerBounds.sampleQMajorant, sampleEtaMajorant_agrees, sampleLMajorant_agrees]

def sampleBMajorant (M : ℕ) : ℕ :=
  sampleLcMajorant M*(sampleJMajorant M+sampleTMajorant M)

theorem sampleBMajorant_agrees : sampleBMajorant = TypedTriangle.TowerBounds.sampleBMajorant := by
  funext M
  simp only [sampleBMajorant, TypedTriangle.TowerBounds.sampleBMajorant, sampleJMajorant_agrees, sampleLcMajorant_agrees, sampleTMajorant_agrees]

def compressionSampleMajorant (M : ℕ) : ℕ :=
  sampleLMajorant (compressionInputMajorant M)*sampleQMajorant (compressionInputMajorant M)+
    sampleBMajorant (compressionInputMajorant M)

theorem compressionSampleMajorant_agrees : compressionSampleMajorant = TypedTriangle.TowerBounds.compressionSampleMajorant := by
  funext M
  simp only [compressionSampleMajorant, TypedTriangle.TowerBounds.compressionSampleMajorant, compressionInputMajorant_agrees, sampleBMajorant_agrees, sampleLMajorant_agrees, sampleQMajorant_agrees]

def physicalRankMajorant (M : ℕ) : ℕ := (compressionSampleMajorant M+1)^2

theorem physicalRankMajorant_agrees : physicalRankMajorant = TypedTriangle.TowerBounds.physicalRankMajorant := by
  funext M
  simp only [physicalRankMajorant, TypedTriangle.TowerBounds.physicalRankMajorant, compressionSampleMajorant_agrees]

def preparationRankMajorant (M : ℕ) : ℕ := physicalRankMajorant (M*2)

theorem preparationRankMajorant_agrees : preparationRankMajorant = TypedTriangle.TowerBounds.preparationRankMajorant := by
  funext M
  simp only [preparationRankMajorant, TypedTriangle.TowerBounds.preparationRankMajorant, physicalRankMajorant_agrees]

def rawRankMajorant (M : ℕ) : ℕ := preparationRankMajorant (M*4)

theorem rawRankMajorant_agrees : rawRankMajorant = TypedTriangle.TowerBounds.rawRankMajorant := by
  funext M
  simp only [rawRankMajorant, TypedTriangle.TowerBounds.rawRankMajorant, preparationRankMajorant_agrees]

def explicitTorsionRadius (d R : ℕ) : ℕ := R * (2 * R + 1) ^ d

theorem explicitTorsionRadius_agrees : explicitTorsionRadius = TypedTriangle.QuotientBox.explicitTorsionRadius := by
  funext d R
  simp only [explicitTorsionRadius, TypedTriangle.QuotientBox.explicitTorsionRadius]

def explicitTorsionBound (d R : ℕ) : ℕ := (2 * explicitTorsionRadius d R + 1) ^ d

theorem explicitTorsionBound_agrees : explicitTorsionBound = TypedTriangle.QuotientBox.explicitTorsionBound := by
  funext d R
  simp only [explicitTorsionBound, TypedTriangle.QuotientBox.explicitTorsionBound, explicitTorsionRadius_agrees]

def compL2Majorant (M : ℕ) : ℕ := 2*(3*(2*M))+1

theorem compL2Majorant_agrees : compL2Majorant = TypedTriangle.TowerBounds.compL2Majorant := by
  funext M
  simp only [compL2Majorant, TypedTriangle.TowerBounds.compL2Majorant]

def compNMajorant (M : ℕ) : ℕ := 4+24*compL2Majorant M

theorem compNMajorant_agrees : compNMajorant = TypedTriangle.TowerBounds.compNMajorant := by
  funext M
  simp only [compNMajorant, TypedTriangle.TowerBounds.compNMajorant, compL2Majorant_agrees]

def compDMajorant (M s : ℕ) : ℕ := 16*compNMajorant M+96*(2*s+1)*compNMajorant M

theorem compDMajorant_agrees : compDMajorant = TypedTriangle.TowerBounds.compDMajorant := by
  funext M s
  simp only [compDMajorant, TypedTriangle.TowerBounds.compDMajorant, compNMajorant_agrees]

def physicalColumnMajorant (M : ℕ) : ℕ :=
  3*compDMajorant (compressionClipMajorant M) (compressionSampleMajorant M)

theorem physicalColumnMajorant_agrees : physicalColumnMajorant = TypedTriangle.TowerBounds.physicalColumnMajorant := by
  funext M
  simp only [physicalColumnMajorant, TypedTriangle.TowerBounds.physicalColumnMajorant, compDMajorant_agrees, compressionClipMajorant_agrees, compressionSampleMajorant_agrees]

def physicalTorsionMajorant (M : ℕ) : ℕ :=
  max 1 (explicitTorsionBound (physicalRankMajorant M) (physicalColumnMajorant M))

theorem physicalTorsionMajorant_agrees : physicalTorsionMajorant = TypedTriangle.TowerBounds.physicalTorsionMajorant := by
  funext M
  simp only [physicalTorsionMajorant, TypedTriangle.TowerBounds.physicalTorsionMajorant, explicitTorsionBound_agrees, physicalColumnMajorant_agrees, physicalRankMajorant_agrees]

def preparationTorsionMajorant (M : ℕ) : ℕ := physicalTorsionMajorant (M*2)

theorem preparationTorsionMajorant_agrees : preparationTorsionMajorant = TypedTriangle.TowerBounds.preparationTorsionMajorant := by
  funext M
  simp only [preparationTorsionMajorant, TypedTriangle.TowerBounds.preparationTorsionMajorant, physicalTorsionMajorant_agrees]

def rawTorsionMajorant (M : ℕ) : ℕ := preparationTorsionMajorant (M*4)

theorem rawTorsionMajorant_agrees : rawTorsionMajorant = TypedTriangle.TowerBounds.rawTorsionMajorant := by
  funext M
  simp only [rawTorsionMajorant, TypedTriangle.TowerBounds.rawTorsionMajorant, preparationTorsionMajorant_agrees]

def rawLengthMajorant (M : ℕ) : ℕ := rawRankMajorant M+(rawRankMajorant M+1)*rawTorsionMajorant M

theorem rawLengthMajorant_agrees : rawLengthMajorant = TypedTriangle.TowerBounds.rawLengthMajorant := by
  funext M
  simp only [rawLengthMajorant, TypedTriangle.TowerBounds.rawLengthMajorant, rawRankMajorant_agrees, rawTorsionMajorant_agrees]

def oddPathMajorant (M : ℕ) : ℕ := 2*(4*((M+1)^2*(M+1)^5))+1

theorem oddPathMajorant_agrees : oddPathMajorant = TypedTriangle.TowerBounds.oddPathMajorant := by
  funext M
  simp only [oddPathMajorant, TypedTriangle.TowerBounds.oddPathMajorant]

def nativeRhoMajorant (M : ℕ) : ℕ := max 1 (M*(8*compressionPowerMajorant M))

theorem nativeRhoMajorant_agrees : nativeRhoMajorant = TypedTriangle.TowerBounds.nativeRhoMajorant := by
  funext M
  simp only [nativeRhoMajorant, TypedTriangle.TowerBounds.nativeRhoMajorant, compressionPowerMajorant_agrees]

def nativeKappaMajorant (M : ℕ) : ℕ := nativeRhoMajorant M^2*2

theorem nativeKappaMajorant_agrees : nativeKappaMajorant = TypedTriangle.TowerBounds.nativeKappaMajorant := by
  funext M
  simp only [nativeKappaMajorant, TypedTriangle.TowerBounds.nativeKappaMajorant, nativeRhoMajorant_agrees]

def nativePathInputMajorant (M : ℕ) : ℕ := M+nativeKappaMajorant M+1

theorem nativePathInputMajorant_agrees : nativePathInputMajorant = TypedTriangle.TowerBounds.nativePathInputMajorant := by
  funext M
  simp only [nativePathInputMajorant, TypedTriangle.TowerBounds.nativePathInputMajorant, nativeKappaMajorant_agrees]

def nativeInteriorMajorant (M : ℕ) : ℕ := oddPathMajorant (nativePathInputMajorant M)+1

theorem nativeInteriorMajorant_agrees : nativeInteriorMajorant = TypedTriangle.TowerBounds.nativeInteriorMajorant := by
  funext M
  simp only [nativeInteriorMajorant, TypedTriangle.TowerBounds.nativeInteriorMajorant, nativePathInputMajorant_agrees, oddPathMajorant_agrees]

def pathDensityMajorant (M : ℕ) : ℕ := (M+1)^(oddPathMajorant M+3)*4

theorem pathDensityMajorant_agrees : pathDensityMajorant = TypedTriangle.TowerBounds.pathDensityMajorant := by
  funext M
  simp only [pathDensityMajorant, TypedTriangle.TowerBounds.pathDensityMajorant, oddPathMajorant_agrees]

def nativeDensityMajorant (M : ℕ) : ℕ := pathDensityMajorant (nativePathInputMajorant M)

theorem nativeDensityMajorant_agrees : nativeDensityMajorant = TypedTriangle.TowerBounds.nativeDensityMajorant := by
  funext M
  simp only [nativeDensityMajorant, TypedTriangle.TowerBounds.nativeDensityMajorant, nativePathInputMajorant_agrees, pathDensityMajorant_agrees]

def nativeAvoidMajorant (M : ℕ) : ℕ := nativeDensityMajorant M*(4*nativeInteriorMajorant M)

theorem nativeAvoidMajorant_agrees : nativeAvoidMajorant = TypedTriangle.TowerBounds.nativeAvoidMajorant := by
  funext M
  simp only [nativeAvoidMajorant, TypedTriangle.TowerBounds.nativeAvoidMajorant, nativeDensityMajorant_agrees, nativeInteriorMajorant_agrees]

def nativeOuterAvoidMajorant (M : ℕ) : ℕ := max (nativeAvoidMajorant M) (max (M*2) 2)

theorem nativeOuterAvoidMajorant_agrees : nativeOuterAvoidMajorant = TypedTriangle.TowerBounds.nativeOuterAvoidMajorant := by
  funext M
  simp only [nativeOuterAvoidMajorant, TypedTriangle.TowerBounds.nativeOuterAvoidMajorant, nativeAvoidMajorant_agrees]

def referenceProviderBound (M : ℕ) : ℕ :=
  let Z := compressionPowerMajorant M * (M*2)
  let A := 1+3*(2*M)
  Z*(A+A^2)*(1+2*(1+3*(2*M)+3*Z))

theorem referenceProviderBound_agrees : referenceProviderBound = TypedTriangle.TowerBounds.referenceProviderBound := by
  funext M
  simp only [referenceProviderBound, TypedTriangle.TowerBounds.referenceProviderBound, compressionPowerMajorant_agrees]

def referenceSeedBudgetBound (M : ℕ) : ℕ :=
  max (M*(10*compressionPowerMajorant M))
    (max (32*M) (M*(2*(16*M+4)*(referenceProviderBound (2*M)+1))))

theorem referenceSeedBudgetBound_agrees : referenceSeedBudgetBound = TypedTriangle.TowerBounds.referenceSeedBudgetBound := by
  funext M
  simp only [referenceSeedBudgetBound, TypedTriangle.TowerBounds.referenceSeedBudgetBound, compressionPowerMajorant_agrees, referenceProviderBound_agrees]

def hingeBudgetMajorant (M : ℕ) : ℕ := M*(64*compressionPowerMajorant M)

theorem hingeBudgetMajorant_agrees : hingeBudgetMajorant = TypedTriangle.TowerBounds.hingeBudgetMajorant := by
  funext M
  simp only [hingeBudgetMajorant, TypedTriangle.TowerBounds.hingeBudgetMajorant, compressionPowerMajorant_agrees]

def geometryBudgetMajorant (M : ℕ) : ℕ := max (M*4) (hingeBudgetMajorant M)

theorem geometryBudgetMajorant_agrees : geometryBudgetMajorant = TypedTriangle.TowerBounds.geometryBudgetMajorant := by
  funext M
  simp only [geometryBudgetMajorant, TypedTriangle.TowerBounds.geometryBudgetMajorant, hingeBudgetMajorant_agrees]

def latticeBudgetMajorant (M : ℕ) : ℕ := M*(8*compressionPowerMajorant M)

theorem latticeBudgetMajorant_agrees : latticeBudgetMajorant = TypedTriangle.TowerBounds.latticeBudgetMajorant := by
  funext M
  simp only [latticeBudgetMajorant, TypedTriangle.TowerBounds.latticeBudgetMajorant, compressionPowerMajorant_agrees]

def initialComplementMajorant (M : ℕ) : ℕ :=
  max (referenceSeedBudgetBound M) (max (geometryBudgetMajorant M) (latticeBudgetMajorant M))

theorem initialComplementMajorant_agrees : initialComplementMajorant = TypedTriangle.TowerBounds.initialComplementMajorant := by
  funext M
  simp only [initialComplementMajorant, TypedTriangle.TowerBounds.initialComplementMajorant, geometryBudgetMajorant_agrees, latticeBudgetMajorant_agrees, referenceSeedBudgetBound_agrees]

def referencePrecisionBound (M : ℕ) : ℕ := max (M*2) 2

theorem referencePrecisionBound_agrees : referencePrecisionBound = TypedTriangle.TowerBounds.referencePrecisionBound := by
  funext M
  simp only [referencePrecisionBound, TypedTriangle.TowerBounds.referencePrecisionBound]

def referenceToleranceBound (M : ℕ) : ℕ := referencePrecisionBound M*8

theorem referenceToleranceBound_agrees : referenceToleranceBound = TypedTriangle.TowerBounds.referenceToleranceBound := by
  funext M
  simp only [referenceToleranceBound, TypedTriangle.TowerBounds.referenceToleranceBound, referencePrecisionBound_agrees]

def referenceWeightBound (M : ℕ) : ℕ := M+M*2

theorem referenceWeightBound_agrees : referenceWeightBound = TypedTriangle.TowerBounds.referenceWeightBound := by
  funext M
  simp only [referenceWeightBound, TypedTriangle.TowerBounds.referenceWeightBound]

def referenceAvoidBound (M : ℕ) : ℕ := max (M*2) (referenceToleranceBound M*(8*referenceWeightBound M))

theorem referenceAvoidBound_agrees : referenceAvoidBound = TypedTriangle.TowerBounds.referenceAvoidBound := by
  funext M
  simp only [referenceAvoidBound, TypedTriangle.TowerBounds.referenceAvoidBound, referenceToleranceBound_agrees, referenceWeightBound_agrees]

def resourceStockMajorant (M : ℕ) : ℕ := referenceAvoidBound (8*M)

theorem resourceStockMajorant_agrees : resourceStockMajorant = TypedTriangle.TowerBounds.resourceStockMajorant := by
  funext M
  simp only [resourceStockMajorant, TypedTriangle.TowerBounds.resourceStockMajorant, referenceAvoidBound_agrees]

def supplyBudgetBound (M h : ℕ) : ℕ := max (max M 2) (M*(40*2^(h.choose 2)))

theorem supplyBudgetBound_agrees : supplyBudgetBound = TypedTriangle.TowerBounds.supplyBudgetBound := by
  funext M h
  simp only [supplyBudgetBound, TypedTriangle.TowerBounds.supplyBudgetBound]

def cellDegreeBudgetBound (M h : ℕ) : ℕ := max (M*8) (supplyBudgetBound (M*2) h*2)

theorem cellDegreeBudgetBound_agrees : cellDegreeBudgetBound = TypedTriangle.TowerBounds.cellDegreeBudgetBound := by
  funext M h
  simp only [cellDegreeBudgetBound, TypedTriangle.TowerBounds.cellDegreeBudgetBound, supplyBudgetBound_agrees]

def bankProtectionBound (M h : ℕ) : ℕ := cellDegreeBudgetBound M h*2

theorem bankProtectionBound_agrees : bankProtectionBound = TypedTriangle.TowerBounds.bankProtectionBound := by
  funext M h
  simp only [bankProtectionBound, TypedTriangle.TowerBounds.bankProtectionBound, cellDegreeBudgetBound_agrees]

def cleanHingeOrderMajorant (M : ℕ) : ℕ := max (48*M) (8*(M+6)*compressionPowerMajorant M*M)

theorem cleanHingeOrderMajorant_agrees : cleanHingeOrderMajorant = TypedTriangle.TowerBounds.cleanHingeOrderMajorant := by
  funext M
  simp only [cleanHingeOrderMajorant, TypedTriangle.TowerBounds.cleanHingeOrderMajorant, compressionPowerMajorant_agrees]

def thresholdInputMajorant (K hOriginal : ℕ) : ℕ :=
  let M := thresholdWorkingScale K
  M+rawToleranceMajorant M+rawRankMajorant M+rawTorsionMajorant M+rawLengthMajorant M+
    nativeInteriorMajorant M+nativeDensityMajorant M+nativeOuterAvoidMajorant M+
    initialComplementMajorant M+resourceStockMajorant M+
    bankProtectionBound M (initialHingeOrder hOriginal)+cleanHingeOrderMajorant K+1

theorem thresholdInputMajorant_agrees : thresholdInputMajorant = TypedTriangle.TowerBounds.thresholdInputMajorant := by
  funext K hOriginal
  simp only [thresholdInputMajorant, TypedTriangle.TowerBounds.thresholdInputMajorant, bankProtectionBound_agrees, cleanHingeOrderMajorant_agrees, initialComplementMajorant_agrees, initialHingeOrder_agrees, nativeDensityMajorant_agrees, nativeInteriorMajorant_agrees, nativeOuterAvoidMajorant_agrees, rawLengthMajorant_agrees, rawRankMajorant_agrees, rawToleranceMajorant_agrees, rawTorsionMajorant_agrees, resourceStockMajorant_agrees, thresholdWorkingScale_agrees]

def triangleThresholdInputBase (K h q : ℕ) : ℕ :=
  let M := thresholdInputMajorant K h
  M+32*M+4*K+q+1

theorem triangleThresholdInputBase_agrees : triangleThresholdInputBase = TypedTriangle.TowerBounds.triangleThresholdInputBase := by
  funext K h q
  simp only [triangleThresholdInputBase, TypedTriangle.TowerBounds.triangleThresholdInputBase, thresholdInputMajorant_agrees]

def layerComplementBudgetMajorant (M : ℕ) : ℕ :=
  max (referenceSeedBudgetBound M) (max (geometryBudgetMajorant M) (latticeBudgetMajorant M))

theorem layerComplementBudgetMajorant_agrees : layerComplementBudgetMajorant = TypedTriangle.TowerBounds.layerComplementBudgetMajorant := by
  funext M
  simp only [layerComplementBudgetMajorant, TypedTriangle.TowerBounds.layerComplementBudgetMajorant, geometryBudgetMajorant_agrees, latticeBudgetMajorant_agrees, referenceSeedBudgetBound_agrees]

def seedPointwisePlusTwoMajorant (M : ℕ) : ℕ :=
  (16*M+4)*referenceProviderBound (2*M)+2

theorem seedPointwisePlusTwoMajorant_agrees : seedPointwisePlusTwoMajorant = TypedTriangle.TowerBounds.seedPointwisePlusTwoMajorant := by
  funext M
  simp only [seedPointwisePlusTwoMajorant, TypedTriangle.TowerBounds.seedPointwisePlusTwoMajorant, referenceProviderBound_agrees]

def triangleComplementMajorant (M : ℕ) : ℕ :=
  max (layerComplementBudgetMajorant M) (max (referenceSeedBudgetBound M)
    (max M (M*seedPointwisePlusTwoMajorant M)))

theorem triangleComplementMajorant_agrees : triangleComplementMajorant = TypedTriangle.TowerBounds.triangleComplementMajorant := by
  funext M
  simp only [triangleComplementMajorant, TypedTriangle.TowerBounds.triangleComplementMajorant, layerComplementBudgetMajorant_agrees, referenceSeedBudgetBound_agrees, seedPointwisePlusTwoMajorant_agrees]

def triangleThresholdInputMajorant (K h q : ℕ) : ℕ :=
  let U := triangleThresholdInputBase K h q
  U+triangleComplementMajorant U+1

theorem triangleThresholdInputMajorant_agrees : triangleThresholdInputMajorant = TypedTriangle.TowerBounds.triangleThresholdInputMajorant := by
  funext K h q
  simp only [triangleThresholdInputMajorant, TypedTriangle.TowerBounds.triangleThresholdInputMajorant, triangleComplementMajorant_agrees, triangleThresholdInputBase_agrees]

def thresholdDensityScale (M : ℕ) : ℕ := M+8*M+1

theorem thresholdDensityScale_agrees : thresholdDensityScale = TypedTriangle.TowerBounds.thresholdDensityScale := by
  funext M
  simp only [thresholdDensityScale, TypedTriangle.TowerBounds.thresholdDensityScale]

def envelopeLoadBound (M : ℕ) : ℕ := 4*M+1

theorem envelopeLoadBound_agrees : envelopeLoadBound = TypedTriangle.TowerBounds.envelopeLoadBound := by
  funext M
  simp only [envelopeLoadBound, TypedTriangle.TowerBounds.envelopeLoadBound]

def envelopeBudgetBound (M : ℕ) : ℕ := M*(64*(envelopeLoadBound M+4))

theorem envelopeBudgetBound_agrees : envelopeBudgetBound = TypedTriangle.TowerBounds.envelopeBudgetBound := by
  funext M
  simp only [envelopeBudgetBound, TypedTriangle.TowerBounds.envelopeBudgetBound, envelopeLoadBound_agrees]

def referenceStockBudgetBound (M : ℕ) : ℕ := max (referenceSeedBudgetBound M) (8*M)

theorem referenceStockBudgetBound_agrees : referenceStockBudgetBound = TypedTriangle.TowerBounds.referenceStockBudgetBound := by
  funext M
  simp only [referenceStockBudgetBound, TypedTriangle.TowerBounds.referenceStockBudgetBound, referenceSeedBudgetBound_agrees]

def envelopeDegreeBound (M : ℕ) : ℕ := 2+2*envelopeLoadBound M

theorem envelopeDegreeBound_agrees : envelopeDegreeBound = TypedTriangle.TowerBounds.envelopeDegreeBound := by
  funext M
  simp only [envelopeDegreeBound, TypedTriangle.TowerBounds.envelopeDegreeBound, envelopeLoadBound_agrees]

def prescribedBudgetBound (M : ℕ) : ℕ :=
  max (envelopeBudgetBound M) (referenceStockBudgetBound M*(2*(envelopeDegreeBound M+1)))

theorem prescribedBudgetBound_agrees : prescribedBudgetBound = TypedTriangle.TowerBounds.prescribedBudgetBound := by
  funext M
  simp only [prescribedBudgetBound, TypedTriangle.TowerBounds.prescribedBudgetBound, envelopeBudgetBound_agrees, envelopeDegreeBound_agrees, referenceStockBudgetBound_agrees]

def futureDensityMajorant (M : ℕ) : ℕ := prescribedBudgetBound (12*M)

theorem futureDensityMajorant_agrees : futureDensityMajorant = TypedTriangle.TowerBounds.futureDensityMajorant := by
  funext M
  simp only [futureDensityMajorant, TypedTriangle.TowerBounds.futureDensityMajorant, prescribedBudgetBound_agrees]

def thresholdGlobalScale (M : ℕ) : ℕ :=
  let U := thresholdDensityScale M
  U+futureDensityMajorant U+1

theorem thresholdGlobalScale_agrees : thresholdGlobalScale = TypedTriangle.TowerBounds.thresholdGlobalScale := by
  funext M
  simp only [thresholdGlobalScale, TypedTriangle.TowerBounds.thresholdGlobalScale, futureDensityMajorant_agrees, thresholdDensityScale_agrees]

def pathRatioMajorant (M k : ℕ) : ℕ := M*(k*M*2^M)

theorem pathRatioMajorant_agrees : pathRatioMajorant = TypedTriangle.TowerBounds.pathRatioMajorant := by
  funext M k
  simp only [pathRatioMajorant, TypedTriangle.TowerBounds.pathRatioMajorant]

def uniformInnerRateMajorant (M : ℕ) : ℕ :=
  max 32 (max (M*4) (max (M*2) (max (M*16) (max (M*8)
    (max (hingeRatioMajorant M 64) (pathRatioMajorant M 64))))))

theorem uniformInnerRateMajorant_agrees : uniformInnerRateMajorant = TypedTriangle.TowerBounds.uniformInnerRateMajorant := by
  funext M
  simp only [uniformInnerRateMajorant, TypedTriangle.TowerBounds.uniformInnerRateMajorant, hingeRatioMajorant_agrees, pathRatioMajorant_agrees]

def adjustedBankWindowMajorant (M : ℕ) : ℕ := max M (pathRatioMajorant M 32)

theorem adjustedBankWindowMajorant_agrees : adjustedBankWindowMajorant = TypedTriangle.TowerBounds.adjustedBankWindowMajorant := by
  funext M
  simp only [adjustedBankWindowMajorant, TypedTriangle.TowerBounds.adjustedBankWindowMajorant, pathRatioMajorant_agrees]

def globalInnerInputMajorant (M : ℕ) : ℕ := max M (adjustedBankWindowMajorant M)

theorem globalInnerInputMajorant_agrees : globalInnerInputMajorant = TypedTriangle.TowerBounds.globalInnerInputMajorant := by
  funext M
  simp only [globalInnerInputMajorant, TypedTriangle.TowerBounds.globalInnerInputMajorant, adjustedBankWindowMajorant_agrees]

def globalInnerRateMajorant (M : ℕ) : ℕ := uniformInnerRateMajorant (globalInnerInputMajorant M)

theorem globalInnerRateMajorant_agrees : globalInnerRateMajorant = TypedTriangle.TowerBounds.globalInnerRateMajorant := by
  funext M
  simp only [globalInnerRateMajorant, TypedTriangle.TowerBounds.globalInnerRateMajorant, globalInnerInputMajorant_agrees, uniformInnerRateMajorant_agrees]

def windowRouteRateMajorant (M : ℕ) : ℕ := M*M*(32*(M+1)*4^M)

theorem windowRouteRateMajorant_agrees : windowRouteRateMajorant = TypedTriangle.TowerBounds.windowRouteRateMajorant := by
  funext M
  simp only [windowRouteRateMajorant, TypedTriangle.TowerBounds.windowRouteRateMajorant]

def stateHoleCapMajorant (M : ℕ) : ℕ := max (windowRouteRateMajorant M*4) (M*M*128)

theorem stateHoleCapMajorant_agrees : stateHoleCapMajorant = TypedTriangle.TowerBounds.stateHoleCapMajorant := by
  funext M
  simp only [stateHoleCapMajorant, TypedTriangle.TowerBounds.stateHoleCapMajorant, windowRouteRateMajorant_agrees]

def assemblyStateInputMajorant (M : ℕ) : ℕ := max M (globalInnerRateMajorant M)

theorem assemblyStateInputMajorant_agrees : assemblyStateInputMajorant = TypedTriangle.TowerBounds.assemblyStateInputMajorant := by
  funext M
  simp only [assemblyStateInputMajorant, TypedTriangle.TowerBounds.assemblyStateInputMajorant, globalInnerRateMajorant_agrees]

def assemblyStateMajorant (M : ℕ) : ℕ := stateHoleCapMajorant (assemblyStateInputMajorant M)

theorem assemblyStateMajorant_agrees : assemblyStateMajorant = TypedTriangle.TowerBounds.assemblyStateMajorant := by
  funext M
  simp only [assemblyStateMajorant, TypedTriangle.TowerBounds.assemblyStateMajorant, assemblyStateInputMajorant_agrees, stateHoleCapMajorant_agrees]

def preparationDebtMajorant (M : ℕ) : ℕ :=
  max M (max M (max (hingeRatioMajorant M 4) (8*max 1 (2*M))))

theorem preparationDebtMajorant_agrees : preparationDebtMajorant = TypedTriangle.TowerBounds.preparationDebtMajorant := by
  funext M
  simp only [preparationDebtMajorant, TypedTriangle.TowerBounds.preparationDebtMajorant, hingeRatioMajorant_agrees]

def globalDebtMajorant (M : ℕ) : ℕ :=
  max 8 (max (M*128) (max (pathRatioMajorant M 64)
    (max (pathRatioMajorant M 128) (preparationDebtMajorant M))))

theorem globalDebtMajorant_agrees : globalDebtMajorant = TypedTriangle.TowerBounds.globalDebtMajorant := by
  funext M
  simp only [globalDebtMajorant, TypedTriangle.TowerBounds.globalDebtMajorant, pathRatioMajorant_agrees, preparationDebtMajorant_agrees]

def thresholdRadiusScale (M : ℕ) : ℕ :=
  let V := thresholdGlobalScale M
  V+globalInnerRateMajorant V+assemblyStateMajorant V+2*globalDebtMajorant V+1

theorem thresholdRadiusScale_agrees : thresholdRadiusScale = TypedTriangle.TowerBounds.thresholdRadiusScale := by
  funext M
  simp only [thresholdRadiusScale, TypedTriangle.TowerBounds.thresholdRadiusScale, assemblyStateMajorant_agrees, globalDebtMajorant_agrees, globalInnerRateMajorant_agrees, thresholdGlobalScale_agrees]

def radiusNextCap (K : ℕ) : ℕ := max (K*2) (K*(16*K*(K+1)))*2

theorem radiusNextCap_agrees : radiusNextCap = TypedTriangle.TowerBounds.radiusNextCap := by
  funext K
  simp only [radiusNextCap, TypedTriangle.TowerBounds.radiusNextCap]

def radiusInputCap (K : ℕ) : ℕ := K+radiusNextCap K+1

theorem radiusInputCap_agrees : radiusInputCap = TypedTriangle.TowerBounds.radiusInputCap := by
  funext K
  simp only [radiusInputCap, TypedTriangle.TowerBounds.radiusInputCap, radiusNextCap_agrees]

def radiusMajorant (F : ℕ → ℕ) (M : ℕ) : ℕ → ℕ
  | 0 => M+F M
  | r+1 => let U := radiusInputCap (radiusMajorant F M r); U+F U

theorem radiusMajorant_agrees : radiusMajorant = TypedTriangle.TowerBounds.radiusMajorant := by
  funext F M r
  induction r with
  | zero => rfl
  | succ j ih => simp only [radiusMajorant, TypedTriangle.TowerBounds.radiusMajorant, radiusInputCap_agrees, ih]

def kernelCapMajorant (M : ℕ) : ℕ := max 1 ((compressionPowerMajorant M*2)*M)

theorem kernelCapMajorant_agrees : kernelCapMajorant = TypedTriangle.TowerBounds.kernelCapMajorant := by
  funext M
  simp only [kernelCapMajorant, TypedTriangle.TowerBounds.kernelCapMajorant, compressionPowerMajorant_agrees]

def smoothCoefficientMajorant (M : ℕ) : ℕ :=
  let D := 12*kernelCapMajorant M
  6*M+((3*M)*2)*(14*(3*D^2+D^3*3)+36*M^2)

theorem smoothCoefficientMajorant_agrees : smoothCoefficientMajorant = TypedTriangle.TowerBounds.smoothCoefficientMajorant := by
  funext M
  simp only [smoothCoefficientMajorant, TypedTriangle.TowerBounds.smoothCoefficientMajorant, kernelCapMajorant_agrees]

def natKernel : ℕ → ℕ → ℕ
  | 0, _ => 1
  | d+1, R => (2*R+1)*natKernel d (R*(2*R+1))

theorem natKernel_agrees : natKernel = TypedTriangle.TowerBounds.natKernel := by
  funext d R
  induction d generalizing R with
  | zero => rfl
  | succ j ih => simp only [natKernel, TypedTriangle.TowerBounds.natKernel, ih]

def natSolver : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d+1, K => (1+2*(d+1)*(max 1 K)^2)*(natSolver d (2*(max 1 K)^2)+1)

theorem natSolver_agrees : natSolver = TypedTriangle.TowerBounds.natSolver := by
  funext d K
  induction d generalizing K with
  | zero => rfl
  | succ j ih => simp only [natSolver, TypedTriangle.TowerBounds.natSolver, ih]

def natStep (M : ℕ) : ℕ :=
  (M+1)+(M+1)^2+(M+1)^(M+1)+(M+1).factorial+natKernel M M+natSolver M M

theorem natStep_agrees : natStep = TypedTriangle.TowerBounds.natStep := by
  funext M
  simp only [natStep, TypedTriangle.TowerBounds.natStep, natKernel_agrees, natSolver_agrees]

def natEnvelope : ℕ → ℕ → ℕ
  | 0, M => M+2
  | k+1, M => natStep (natEnvelope k M)

theorem natEnvelope_agrees : natEnvelope = TypedTriangle.TowerBounds.natEnvelope := by
  funext k M
  induction k generalizing M with
  | zero => rfl
  | succ j ih => simp only [natEnvelope, TypedTriangle.TowerBounds.natEnvelope, natStep_agrees, ih]

def compHMajorant (M S : ℕ) : ℕ :=
  1+8*compL2Majorant M+5*compNMajorant M+32*(2*S+1)*compNMajorant M

theorem compHMajorant_agrees : compHMajorant = TypedTriangle.TowerBounds.compHMajorant := by
  funext M S
  simp only [compHMajorant, TypedTriangle.TowerBounds.compHMajorant, compL2Majorant_agrees, compNMajorant_agrees]

def uniformCertMajorant (M : ℕ) : ℕ :=
  let S := compressionSampleMajorant M
  natEnvelope 6 (S+compHMajorant M S+compDMajorant M S)

theorem uniformCertMajorant_agrees : uniformCertMajorant = TypedTriangle.TowerBounds.uniformCertMajorant := by
  funext M
  simp only [uniformCertMajorant, TypedTriangle.TowerBounds.uniformCertMajorant, compDMajorant_agrees, compHMajorant_agrees, compressionSampleMajorant_agrees, natEnvelope_agrees]

def smoothSampleMajorant (M : ℕ) : ℕ := compressionSampleMajorant (2*M)

theorem smoothSampleMajorant_agrees : smoothSampleMajorant = TypedTriangle.TowerBounds.smoothSampleMajorant := by
  funext M
  simp only [smoothSampleMajorant, TypedTriangle.TowerBounds.smoothSampleMajorant, compressionSampleMajorant_agrees]

def smoothDMajorant (M : ℕ) : ℕ := compDMajorant (2*M) (smoothSampleMajorant M)

theorem smoothDMajorant_agrees : smoothDMajorant = TypedTriangle.TowerBounds.smoothDMajorant := by
  funext M
  simp only [smoothDMajorant, TypedTriangle.TowerBounds.smoothDMajorant, compDMajorant_agrees, smoothSampleMajorant_agrees]

def routingCompMajorant (M : ℕ) : ℕ := M+1

theorem routingCompMajorant_agrees : routingCompMajorant = TypedTriangle.TowerBounds.routingCompMajorant := by
  funext M
  simp only [routingCompMajorant, TypedTriangle.TowerBounds.routingCompMajorant]

def routeDMajorant (M : ℕ) : ℕ := 12*routingCompMajorant M^2

theorem routeDMajorant_agrees : routeDMajorant = TypedTriangle.TowerBounds.routeDMajorant := by
  funext M
  simp only [routeDMajorant, TypedTriangle.TowerBounds.routeDMajorant, routingCompMajorant_agrees]

def smoothDemandMajorant (M : ℕ) : ℕ :=
  let S := smoothSampleMajorant M
  let D := smoothDMajorant M
  let R := routeDMajorant (2*M)
  3*R*natKernel ((S+1)^2) (max (D*(3*R)) (3*D))

theorem smoothDemandMajorant_agrees : smoothDemandMajorant = TypedTriangle.TowerBounds.smoothDemandMajorant := by
  funext M
  simp only [smoothDemandMajorant, TypedTriangle.TowerBounds.smoothDemandMajorant, natKernel_agrees, routeDMajorant_agrees, smoothDMajorant_agrees, smoothSampleMajorant_agrees]

def smoothCertMajorant (M : ℕ) : ℕ := uniformCertMajorant (4*M)*smoothDemandMajorant M

theorem smoothCertMajorant_agrees : smoothCertMajorant = TypedTriangle.TowerBounds.smoothCertMajorant := by
  funext M
  simp only [smoothCertMajorant, TypedTriangle.TowerBounds.smoothCertMajorant, smoothDemandMajorant_agrees, uniformCertMajorant_agrees]

def routeBudgetMajorant (M : ℕ) : ℕ := max (M*(8*compressionPowerMajorant M)) (routingCompMajorant M)

theorem routeBudgetMajorant_agrees : routeBudgetMajorant = TypedTriangle.TowerBounds.routeBudgetMajorant := by
  funext M
  simp only [routeBudgetMajorant, TypedTriangle.TowerBounds.routeBudgetMajorant, compressionPowerMajorant_agrees, routingCompMajorant_agrees]

def congestionMajorant (M : ℕ) : ℕ :=
  let K := smoothCertMajorant M
  let D := routeDMajorant (2*M)
  let δ := routeBudgetMajorant (2*M)
  K*(4*D+3+32*D*δ+12*K*M+2*D+2)+1

theorem congestionMajorant_agrees : congestionMajorant = TypedTriangle.TowerBounds.congestionMajorant := by
  funext M
  simp only [congestionMajorant, TypedTriangle.TowerBounds.congestionMajorant, routeBudgetMajorant_agrees, routeDMajorant_agrees, smoothCertMajorant_agrees]

def inverseCostMajorant (M : ℕ) : ℕ := smoothCoefficientMajorant (M+congestionMajorant M)

theorem inverseCostMajorant_agrees : inverseCostMajorant = TypedTriangle.TowerBounds.inverseCostMajorant := by
  funext M
  simp only [inverseCostMajorant, TypedTriangle.TowerBounds.inverseCostMajorant, congestionMajorant_agrees, smoothCoefficientMajorant_agrees]

def paidDensityMajorant (M : ℕ) : ℕ := max (M*2) (hingeDensityMajorant M)

theorem paidDensityMajorant_agrees : paidDensityMajorant = TypedTriangle.TowerBounds.paidDensityMajorant := by
  funext M
  simp only [paidDensityMajorant, TypedTriangle.TowerBounds.paidDensityMajorant, hingeDensityMajorant_agrees]

def paidSmoothInputMajorant (M : ℕ) : ℕ :=
  M+paidDensityMajorant M+max M 2+2*M+1

theorem paidSmoothInputMajorant_agrees : paidSmoothInputMajorant = TypedTriangle.TowerBounds.paidSmoothInputMajorant := by
  funext M
  simp only [paidSmoothInputMajorant, TypedTriangle.TowerBounds.paidSmoothInputMajorant, paidDensityMajorant_agrees]

def paidBudgetMajorant (M : ℕ) : ℕ := max (geometryBudgetMajorant M*2) (latticeBudgetMajorant M*2)

theorem paidBudgetMajorant_agrees : paidBudgetMajorant = TypedTriangle.TowerBounds.paidBudgetMajorant := by
  funext M
  simp only [paidBudgetMajorant, TypedTriangle.TowerBounds.paidBudgetMajorant, geometryBudgetMajorant_agrees, latticeBudgetMajorant_agrees]

def paidCostMajorant (M : ℕ) : ℕ :=
  max (inverseCostMajorant (paidSmoothInputMajorant M)) (paidBudgetMajorant M)

theorem paidCostMajorant_agrees : paidCostMajorant = TypedTriangle.TowerBounds.paidCostMajorant := by
  funext M
  simp only [paidCostMajorant, TypedTriangle.TowerBounds.paidCostMajorant, inverseCostMajorant_agrees, paidBudgetMajorant_agrees, paidSmoothInputMajorant_agrees]

def referenceLoadBound (M : ℕ) : ℕ := max (referenceToleranceBound M*4) 4

theorem referenceLoadBound_agrees : referenceLoadBound = TypedTriangle.TowerBounds.referenceLoadBound := by
  funext M
  simp only [referenceLoadBound, TypedTriangle.TowerBounds.referenceLoadBound, referenceToleranceBound_agrees]

def prescribedLoadBound (M : ℕ) : ℕ := max (referenceLoadBound M) 2

theorem prescribedLoadBound_agrees : prescribedLoadBound = TypedTriangle.TowerBounds.prescribedLoadBound := by
  funext M
  simp only [prescribedLoadBound, TypedTriangle.TowerBounds.prescribedLoadBound, referenceLoadBound_agrees]

def referencePrecisionMajorant (M : ℕ) : ℕ :=
  max M (max (M*(10*compressionPowerMajorant M))
    (max (paidBudgetMajorant M*4) (512*M*M*paidCostMajorant M)))

theorem referencePrecisionMajorant_agrees : referencePrecisionMajorant = TypedTriangle.TowerBounds.referencePrecisionMajorant := by
  funext M
  simp only [referencePrecisionMajorant, TypedTriangle.TowerBounds.referencePrecisionMajorant, compressionPowerMajorant_agrees, paidBudgetMajorant_agrees, paidCostMajorant_agrees]

def referenceLoadMajorant (M : ℕ) : ℕ := prescribedLoadBound (referencePrecisionMajorant M)

theorem referenceLoadMajorant_agrees : referenceLoadMajorant = TypedTriangle.TowerBounds.referenceLoadMajorant := by
  funext M
  simp only [referenceLoadMajorant, TypedTriangle.TowerBounds.referenceLoadMajorant, prescribedLoadBound_agrees, referencePrecisionMajorant_agrees]

def profileToleranceMajorant (M : ℕ) : ℕ :=
  max (2*M*paidCostMajorant M) (referenceLoadMajorant M)

theorem profileToleranceMajorant_agrees : profileToleranceMajorant = TypedTriangle.TowerBounds.profileToleranceMajorant := by
  funext M
  simp only [profileToleranceMajorant, TypedTriangle.TowerBounds.profileToleranceMajorant, paidCostMajorant_agrees, referenceLoadMajorant_agrees]

def innerRadiusInput (M : ℕ) : ℕ := M+2*M+max M (M*(2*(M+1)))+1

theorem innerRadiusInput_agrees : innerRadiusInput = TypedTriangle.TowerBounds.innerRadiusInput := by
  funext M
  simp only [innerRadiusInput, TypedTriangle.TowerBounds.innerRadiusInput]

def innerRadiusMajorant (M : ℕ) : ℕ :=
  radiusMajorant profileToleranceMajorant (innerRadiusInput M) M

theorem innerRadiusMajorant_agrees : innerRadiusMajorant = TypedTriangle.TowerBounds.innerRadiusMajorant := by
  funext M
  simp only [innerRadiusMajorant, TypedTriangle.TowerBounds.innerRadiusMajorant, innerRadiusInput_agrees, profileToleranceMajorant_agrees, radiusMajorant_agrees]

def geometryOrderMajorant (M : ℕ) : ℕ := 128*(M+2)*compressionPowerMajorant M*M+1

theorem geometryOrderMajorant_agrees : geometryOrderMajorant = TypedTriangle.TowerBounds.geometryOrderMajorant := by
  funext M
  simp only [geometryOrderMajorant, TypedTriangle.TowerBounds.geometryOrderMajorant, compressionPowerMajorant_agrees]

def latticeOrderMajorant (M : ℕ) : ℕ := 4*M+1

theorem latticeOrderMajorant_agrees : latticeOrderMajorant = TypedTriangle.TowerBounds.latticeOrderMajorant := by
  funext M
  simp only [latticeOrderMajorant, TypedTriangle.TowerBounds.latticeOrderMajorant]

def paidOrderMajorant (M : ℕ) : ℕ := max (geometryOrderMajorant M) (latticeOrderMajorant M)

theorem paidOrderMajorant_agrees : paidOrderMajorant = TypedTriangle.TowerBounds.paidOrderMajorant := by
  funext M
  simp only [paidOrderMajorant, TypedTriangle.TowerBounds.paidOrderMajorant, geometryOrderMajorant_agrees, latticeOrderMajorant_agrees]

def compressionOrderMajorant (M : ℕ) : ℕ :=
  4*compressionClipMajorant M+4*M*compressionPowerMajorant M*compressionClipMajorant M+1

theorem compressionOrderMajorant_agrees : compressionOrderMajorant = TypedTriangle.TowerBounds.compressionOrderMajorant := by
  funext M
  simp only [compressionOrderMajorant, TypedTriangle.TowerBounds.compressionOrderMajorant, compressionClipMajorant_agrees, compressionPowerMajorant_agrees]

def paidPreparedInputMajorant (M : ℕ) : ℕ := paidDensityMajorant M*4+2*M+1

theorem paidPreparedInputMajorant_agrees : paidPreparedInputMajorant = TypedTriangle.TowerBounds.paidPreparedInputMajorant := by
  funext M
  simp only [paidPreparedInputMajorant, TypedTriangle.TowerBounds.paidPreparedInputMajorant, paidDensityMajorant_agrees]

def paidPreparedOrderMajorant (M : ℕ) : ℕ := compressionOrderMajorant (paidPreparedInputMajorant M)

theorem paidPreparedOrderMajorant_agrees : paidPreparedOrderMajorant = TypedTriangle.TowerBounds.paidPreparedOrderMajorant := by
  funext M
  simp only [paidPreparedOrderMajorant, TypedTriangle.TowerBounds.paidPreparedOrderMajorant, compressionOrderMajorant_agrees, paidPreparedInputMajorant_agrees]

def routeOrderMajorant (M : ℕ) : ℕ := (8+4*M*compressionPowerMajorant M)*M+1

theorem routeOrderMajorant_agrees : routeOrderMajorant = TypedTriangle.TowerBounds.routeOrderMajorant := by
  funext M
  simp only [routeOrderMajorant, TypedTriangle.TowerBounds.routeOrderMajorant, compressionPowerMajorant_agrees]

def nZeroMajorant (M : ℕ) : ℕ := 2*(12*M+3)*compressionPowerMajorant M*M

theorem nZeroMajorant_agrees : nZeroMajorant = TypedTriangle.TowerBounds.nZeroMajorant := by
  funext M
  simp only [nZeroMajorant, TypedTriangle.TowerBounds.nZeroMajorant, compressionPowerMajorant_agrees]

def inverseOrderMajorant (M : ℕ) : ℕ :=
  max (max (compressionOrderMajorant (4*M))
    (max (compressionOrderMajorant (2*M)) (routeOrderMajorant (2*M)))) (nZeroMajorant M)

theorem inverseOrderMajorant_agrees : inverseOrderMajorant = TypedTriangle.TowerBounds.inverseOrderMajorant := by
  funext M
  simp only [inverseOrderMajorant, TypedTriangle.TowerBounds.inverseOrderMajorant, compressionOrderMajorant_agrees, nZeroMajorant_agrees, routeOrderMajorant_agrees]

def paidInverseOrderMajorant (M : ℕ) : ℕ := inverseOrderMajorant (paidSmoothInputMajorant M)

theorem paidInverseOrderMajorant_agrees : paidInverseOrderMajorant = TypedTriangle.TowerBounds.paidInverseOrderMajorant := by
  funext M
  simp only [paidInverseOrderMajorant, TypedTriangle.TowerBounds.paidInverseOrderMajorant, inverseOrderMajorant_agrees, paidSmoothInputMajorant_agrees]

def envelopeOrderBound (M : ℕ) : ℕ := 32*envelopeLoadBound M*M+1

theorem envelopeOrderBound_agrees : envelopeOrderBound = TypedTriangle.TowerBounds.envelopeOrderBound := by
  funext M
  simp only [envelopeOrderBound, TypedTriangle.TowerBounds.envelopeOrderBound, envelopeLoadBound_agrees]

def analyticCutBound (M : ℕ) : ℕ := (2 * M * M) ^ (2 * M)

theorem analyticCutBound_agrees : analyticCutBound = TypedTriangle.TowerBounds.analyticCutBound := by
  funext M
  simp only [analyticCutBound, TypedTriangle.TowerBounds.analyticCutBound]

def nibbleThreeBound : ℕ := analyticCutBound 1000000

theorem nibbleThreeBound_agrees : nibbleThreeBound = TypedTriangle.TowerBounds.nibbleThreeBound := by
  simp only [nibbleThreeBound, TypedTriangle.TowerBounds.nibbleThreeBound, analyticCutBound_agrees]

def egjFourInputBound : ℕ := 30000000 + 2 * nibbleThreeBound

theorem egjFourInputBound_agrees : egjFourInputBound = TypedTriangle.TowerBounds.egjFourInputBound := by
  simp only [egjFourInputBound, TypedTriangle.TowerBounds.egjFourInputBound, nibbleThreeBound_agrees]

def egjFourBound : ℕ := analyticCutBound egjFourInputBound

theorem egjFourBound_agrees : egjFourBound = TypedTriangle.TowerBounds.egjFourBound := by
  simp only [egjFourBound, TypedTriangle.TowerBounds.egjFourBound, analyticCutBound_agrees, egjFourInputBound_agrees]

def cloneInputBound (M : ℕ) : ℕ :=
  max 5120000 (max egjFourBound (4*M*M+2))

theorem cloneInputBound_agrees : cloneInputBound = TypedTriangle.TowerBounds.cloneInputBound := by
  funext M
  simp only [cloneInputBound, TypedTriangle.TowerBounds.cloneInputBound, egjFourBound_agrees]

def cloneBound (M : ℕ) : ℕ := analyticCutBound (cloneInputBound M)

theorem cloneBound_agrees : cloneBound = TypedTriangle.TowerBounds.cloneBound := by
  funext M
  simp only [cloneBound, TypedTriangle.TowerBounds.cloneBound, analyticCutBound_agrees, cloneInputBound_agrees]

def approxPackingBound (M : ℕ) : ℕ := cloneBound (16*M)

theorem approxPackingBound_agrees : approxPackingBound = TypedTriangle.TowerBounds.approxPackingBound := by
  funext M
  simp only [approxPackingBound, TypedTriangle.TowerBounds.approxPackingBound, cloneBound_agrees]

def referenceOrderInput (M : ℕ) : ℕ := 1+referenceWeightBound M+referencePrecisionBound M

theorem referenceOrderInput_agrees : referenceOrderInput = TypedTriangle.TowerBounds.referenceOrderInput := by
  funext M
  simp only [referenceOrderInput, TypedTriangle.TowerBounds.referenceOrderInput, referencePrecisionBound_agrees, referenceWeightBound_agrees]

def referenceOrderBound (M : ℕ) : ℕ :=
  max (max (16*M+1) (approxPackingBound (referenceOrderInput M))) 1

theorem referenceOrderBound_agrees : referenceOrderBound = TypedTriangle.TowerBounds.referenceOrderBound := by
  funext M
  simp only [referenceOrderBound, TypedTriangle.TowerBounds.referenceOrderBound, approxPackingBound_agrees, referenceOrderInput_agrees]

def prescribedOrderBound (M : ℕ) : ℕ :=
  max (envelopeOrderBound M) (max (referenceOrderBound M)
    (2*envelopeDegreeBound M*referenceStockBudgetBound M))

theorem prescribedOrderBound_agrees : prescribedOrderBound = TypedTriangle.TowerBounds.prescribedOrderBound := by
  funext M
  simp only [prescribedOrderBound, TypedTriangle.TowerBounds.prescribedOrderBound, envelopeDegreeBound_agrees, envelopeOrderBound_agrees, referenceOrderBound_agrees, referenceStockBudgetBound_agrees]

def referenceAgendaInput (M : ℕ) : ℕ := 12*M+referencePrecisionMajorant M

theorem referenceAgendaInput_agrees : referenceAgendaInput = TypedTriangle.TowerBounds.referenceAgendaInput := by
  funext M
  simp only [referenceAgendaInput, TypedTriangle.TowerBounds.referenceAgendaInput, referencePrecisionMajorant_agrees]

def referenceThresholdMajorant (M : ℕ) : ℕ := prescribedOrderBound (referenceAgendaInput M)

theorem referenceThresholdMajorant_agrees : referenceThresholdMajorant = TypedTriangle.TowerBounds.referenceThresholdMajorant := by
  funext M
  simp only [referenceThresholdMajorant, TypedTriangle.TowerBounds.referenceThresholdMajorant, prescribedOrderBound_agrees, referenceAgendaInput_agrees]

def innerNodeOrderMajorant (M : ℕ) : ℕ :=
  max (max (max (paidOrderMajorant M) (paidPreparedOrderMajorant M))
    (paidInverseOrderMajorant M)) (referenceThresholdMajorant M)

theorem innerNodeOrderMajorant_agrees : innerNodeOrderMajorant = TypedTriangle.TowerBounds.innerNodeOrderMajorant := by
  funext M
  simp only [innerNodeOrderMajorant, TypedTriangle.TowerBounds.innerNodeOrderMajorant, paidInverseOrderMajorant_agrees, paidOrderMajorant_agrees, paidPreparedOrderMajorant_agrees, referenceThresholdMajorant_agrees]

def innerScheduleMajorant (M : ℕ) : ℕ :=
  max (paidOrderMajorant M) (innerNodeOrderMajorant (M+innerRadiusMajorant M))

theorem innerScheduleMajorant_agrees : innerScheduleMajorant = TypedTriangle.TowerBounds.innerScheduleMajorant := by
  funext M
  simp only [innerScheduleMajorant, TypedTriangle.TowerBounds.innerScheduleMajorant, innerNodeOrderMajorant_agrees, innerRadiusMajorant_agrees, paidOrderMajorant_agrees]

def thresholdProfileScale (M : ℕ) : ℕ :=
  let W := thresholdRadiusScale M
  W+innerRadiusMajorant W+innerScheduleMajorant W+1

theorem thresholdProfileScale_agrees : thresholdProfileScale = TypedTriangle.TowerBounds.thresholdProfileScale := by
  funext M
  simp only [thresholdProfileScale, TypedTriangle.TowerBounds.thresholdProfileScale, innerRadiusMajorant_agrees, innerScheduleMajorant_agrees, thresholdRadiusScale_agrees]

def prescribedAvoidBound (M : ℕ) : ℕ := max (referenceAvoidBound M) (envelopeBudgetBound M)

theorem prescribedAvoidBound_agrees : prescribedAvoidBound = TypedTriangle.TowerBounds.prescribedAvoidBound := by
  funext M
  simp only [prescribedAvoidBound, TypedTriangle.TowerBounds.prescribedAvoidBound, envelopeBudgetBound_agrees, referenceAvoidBound_agrees]

def referenceAvoidMajorant (M : ℕ) : ℕ := prescribedAvoidBound (referenceAgendaInput M)

theorem referenceAvoidMajorant_agrees : referenceAvoidMajorant = TypedTriangle.TowerBounds.referenceAvoidMajorant := by
  funext M
  simp only [referenceAvoidMajorant, TypedTriangle.TowerBounds.referenceAvoidMajorant, prescribedAvoidBound_agrees, referenceAgendaInput_agrees]

def thresholdAgendaMajorant (M : ℕ) : ℕ :=
  let P := thresholdProfileScale M
  P+paidCostMajorant P+referenceLoadMajorant P+referenceAvoidMajorant P+
    referenceThresholdMajorant P+paidInverseOrderMajorant P+paidOrderMajorant P+1

theorem thresholdAgendaMajorant_agrees : thresholdAgendaMajorant = TypedTriangle.TowerBounds.thresholdAgendaMajorant := by
  funext M
  simp only [thresholdAgendaMajorant, TypedTriangle.TowerBounds.thresholdAgendaMajorant, paidCostMajorant_agrees, paidInverseOrderMajorant_agrees, paidOrderMajorant_agrees, referenceAvoidMajorant_agrees, referenceLoadMajorant_agrees, referenceThresholdMajorant_agrees, thresholdProfileScale_agrees]

def catalogDimensionMajorant (M : ℕ) : ℕ := (compressionSampleMajorant M+1)^2

theorem catalogDimensionMajorant_agrees : catalogDimensionMajorant = TypedTriangle.TowerBounds.catalogDimensionMajorant := by
  funext M
  simp only [catalogDimensionMajorant, TypedTriangle.TowerBounds.catalogDimensionMajorant, compressionSampleMajorant_agrees]

def catalogCoefficientMajorant (M : ℕ) : ℕ :=
  compDMajorant (compressionClipMajorant M) (compressionSampleMajorant M)

theorem catalogCoefficientMajorant_agrees : catalogCoefficientMajorant = TypedTriangle.TowerBounds.catalogCoefficientMajorant := by
  funext M
  simp only [catalogCoefficientMajorant, TypedTriangle.TowerBounds.catalogCoefficientMajorant, compDMajorant_agrees, compressionClipMajorant_agrees, compressionSampleMajorant_agrees]

def catalogColumnMajorant (M : ℕ) : ℕ := 3*catalogCoefficientMajorant M

theorem catalogColumnMajorant_agrees : catalogColumnMajorant = TypedTriangle.TowerBounds.catalogColumnMajorant := by
  funext M
  simp only [catalogColumnMajorant, TypedTriangle.TowerBounds.catalogColumnMajorant, catalogCoefficientMajorant_agrees]

def atomRadiusMajorant (M : ℕ) : ℕ := 3*routeDMajorant (M*2)

theorem atomRadiusMajorant_agrees : atomRadiusMajorant = TypedTriangle.TowerBounds.atomRadiusMajorant := by
  funext M
  simp only [atomRadiusMajorant, TypedTriangle.TowerBounds.atomRadiusMajorant, routeDMajorant_agrees]

def bankCatalogInputMajorant (M : ℕ) : ℕ :=
  atomRadiusMajorant M+catalogDimensionMajorant M+catalogCoefficientMajorant M+
    catalogColumnMajorant M+catalogDimensionMajorant (M*2)+
    catalogCoefficientMajorant (M*2)+catalogColumnMajorant (M*2)

theorem bankCatalogInputMajorant_agrees : bankCatalogInputMajorant = TypedTriangle.TowerBounds.bankCatalogInputMajorant := by
  funext M
  simp only [bankCatalogInputMajorant, TypedTriangle.TowerBounds.bankCatalogInputMajorant, atomRadiusMajorant_agrees, catalogCoefficientMajorant_agrees, catalogColumnMajorant_agrees, catalogDimensionMajorant_agrees]

def bankRadiusMajorant (M : ℕ) : ℕ := natEnvelope 5 (bankCatalogInputMajorant M)

theorem bankRadiusMajorant_agrees : bankRadiusMajorant = TypedTriangle.TowerBounds.bankRadiusMajorant := by
  funext M
  simp only [bankRadiusMajorant, TypedTriangle.TowerBounds.bankRadiusMajorant, bankCatalogInputMajorant_agrees, natEnvelope_agrees]

def bankCatalogSizeMajorant (M : ℕ) : ℕ := natEnvelope 8 (bankCatalogInputMajorant M)

theorem bankCatalogSizeMajorant_agrees : bankCatalogSizeMajorant = TypedTriangle.TowerBounds.bankCatalogSizeMajorant := by
  funext M
  simp only [bankCatalogSizeMajorant, TypedTriangle.TowerBounds.bankCatalogSizeMajorant, bankCatalogInputMajorant_agrees, natEnvelope_agrees]

def supplySizeBound (K h k : ℕ) : ℕ := K*k*(4*(2*h-2).choose 2+6)

theorem supplySizeBound_agrees : supplySizeBound = TypedTriangle.TowerBounds.supplySizeBound := by
  funext K h k
  simp only [supplySizeBound, TypedTriangle.TowerBounds.supplySizeBound]

def boundedPieceSizeMajorant (M h k : ℕ) : ℕ := supplySizeBound (uniformCertMajorant M) h k

theorem boundedPieceSizeMajorant_agrees : boundedPieceSizeMajorant = TypedTriangle.TowerBounds.boundedPieceSizeMajorant := by
  funext M h k
  simp only [boundedPieceSizeMajorant, TypedTriangle.TowerBounds.boundedPieceSizeMajorant, supplySizeBound_agrees, uniformCertMajorant_agrees]

def bankRerouteMajorant (M : ℕ) : ℕ := natEnvelope 9 (bankCatalogInputMajorant M)

theorem bankRerouteMajorant_agrees : bankRerouteMajorant = TypedTriangle.TowerBounds.bankRerouteMajorant := by
  funext M
  simp only [bankRerouteMajorant, TypedTriangle.TowerBounds.bankRerouteMajorant, bankCatalogInputMajorant_agrees, natEnvelope_agrees]

def bankCellSizeMajorant (M h : ℕ) : ℕ :=
  boundedPieceSizeMajorant (M*2) h (4*bankRerouteMajorant M)+4*bankRerouteMajorant M

theorem bankCellSizeMajorant_agrees : bankCellSizeMajorant = TypedTriangle.TowerBounds.bankCellSizeMajorant := by
  funext M h
  simp only [bankCellSizeMajorant, TypedTriangle.TowerBounds.bankCellSizeMajorant, bankRerouteMajorant_agrees, boundedPieceSizeMajorant_agrees]

def coreDeltaBound (M h : ℕ) : ℕ := max 2 (M*(2*2^(h.choose 2)))

theorem coreDeltaBound_agrees : coreDeltaBound = TypedTriangle.TowerBounds.coreDeltaBound := by
  funext M h
  simp only [coreDeltaBound, TypedTriangle.TowerBounds.coreDeltaBound]

def nativeDeleteMajorant (M : ℕ) : ℕ := nativeRhoMajorant M*4

theorem nativeDeleteMajorant_agrees : nativeDeleteMajorant = TypedTriangle.TowerBounds.nativeDeleteMajorant := by
  funext M
  simp only [nativeDeleteMajorant, TypedTriangle.TowerBounds.nativeDeleteMajorant, nativeRhoMajorant_agrees]

def bankToleranceBound (M h : ℕ) : ℕ := max (bankProtectionBound M h) M

theorem bankToleranceBound_agrees : bankToleranceBound = TypedTriangle.TowerBounds.bankToleranceBound := by
  funext M h
  simp only [bankToleranceBound, TypedTriangle.TowerBounds.bankToleranceBound, bankProtectionBound_agrees]

def quadraticRateMajorant (M E B : ℕ) : ℕ := M*M*(32*(E*B+1))

theorem quadraticRateMajorant_agrees : quadraticRateMajorant = TypedTriangle.TowerBounds.quadraticRateMajorant := by
  funext M E B
  simp only [quadraticRateMajorant, TypedTriangle.TowerBounds.quadraticRateMajorant]

def geometricDeletionBound (M h : ℕ) : ℕ := max 2 (M*(4*2^((h+1).choose 2)))

theorem geometricDeletionBound_agrees : geometricDeletionBound = TypedTriangle.TowerBounds.geometricDeletionBound := by
  funext M h
  simp only [geometricDeletionBound, TypedTriangle.TowerBounds.geometricDeletionBound]

def cellDeletionBound (M h : ℕ) : ℕ := max (geometricDeletionBound M h) (coreDeltaBound M h)

theorem cellDeletionBound_agrees : cellDeletionBound = TypedTriangle.TowerBounds.cellDeletionBound := by
  funext M h
  simp only [cellDeletionBound, TypedTriangle.TowerBounds.cellDeletionBound, coreDeltaBound_agrees, geometricDeletionBound_agrees]

def bankDeletionBound (M h : ℕ) : ℕ :=
  max (geometricDeletionBound M h) (max (max (cellDeletionBound M h) (coreDeltaBound M h)) M)

theorem bankDeletionBound_agrees : bankDeletionBound = TypedTriangle.TowerBounds.bankDeletionBound := by
  funext M h
  simp only [bankDeletionBound, TypedTriangle.TowerBounds.bankDeletionBound, cellDeletionBound_agrees, coreDeltaBound_agrees, geometricDeletionBound_agrees]

def bankCopiesMajorant (M P : ℕ) : ℕ := 2*bankCatalogSizeMajorant M*P

theorem bankCopiesMajorant_agrees : bankCopiesMajorant = TypedTriangle.TowerBounds.bankCopiesMajorant := by
  funext M P
  simp only [bankCopiesMajorant, TypedTriangle.TowerBounds.bankCopiesMajorant, bankCatalogSizeMajorant_agrees]

def nativeBankRateMajorant (M h P : ℕ) : ℕ :=
  quadraticRateMajorant (max (bankToleranceBound M h) (bankDeletionBound M h))
    (bankCellSizeMajorant M h) (bankCopiesMajorant M P)

theorem nativeBankRateMajorant_agrees : nativeBankRateMajorant = TypedTriangle.TowerBounds.nativeBankRateMajorant := by
  funext M h P
  simp only [nativeBankRateMajorant, TypedTriangle.TowerBounds.nativeBankRateMajorant, bankCellSizeMajorant_agrees, bankCopiesMajorant_agrees, bankDeletionBound_agrees, bankToleranceBound_agrees, quadraticRateMajorant_agrees]

def preparedBankInputMajorant (M h : ℕ) : ℕ := max M (coreDeltaBound M h)

theorem preparedBankInputMajorant_agrees : preparedBankInputMajorant = TypedTriangle.TowerBounds.preparedBankInputMajorant := by
  funext M h
  simp only [preparedBankInputMajorant, TypedTriangle.TowerBounds.preparedBankInputMajorant, coreDeltaBound_agrees]

def preparedBankRateMajorant (M h P : ℕ) : ℕ := nativeBankRateMajorant (preparedBankInputMajorant M h) h P

theorem preparedBankRateMajorant_agrees : preparedBankRateMajorant = TypedTriangle.TowerBounds.preparedBankRateMajorant := by
  funext M h P
  simp only [preparedBankRateMajorant, TypedTriangle.TowerBounds.preparedBankRateMajorant, nativeBankRateMajorant_agrees, preparedBankInputMajorant_agrees]

def natExtensionCost (d D E R : ℕ) : ℕ := d*natSolver d (D*R+E)*R*D

theorem natExtensionCost_agrees : natExtensionCost = TypedTriangle.TowerBounds.natExtensionCost := by
  funext d D E R
  simp only [natExtensionCost, TypedTriangle.TowerBounds.natExtensionCost, natSolver_agrees]

def deletedExtensionMajorant (M : ℕ) : ℕ :=
  let D := compDMajorant (M+1) (compressionSampleMajorant M)
  natExtensionCost (physicalRankMajorant M) D (3*D) (3*routeDMajorant M)

theorem deletedExtensionMajorant_agrees : deletedExtensionMajorant = TypedTriangle.TowerBounds.deletedExtensionMajorant := by
  funext M
  simp only [deletedExtensionMajorant, TypedTriangle.TowerBounds.deletedExtensionMajorant, compDMajorant_agrees, compressionSampleMajorant_agrees, natExtensionCost_agrees, physicalRankMajorant_agrees, routeDMajorant_agrees]

def physicalGlueMajorant (M : ℕ) : ℕ := deletedExtensionMajorant M+1

theorem physicalGlueMajorant_agrees : physicalGlueMajorant = TypedTriangle.TowerBounds.physicalGlueMajorant := by
  funext M
  simp only [physicalGlueMajorant, TypedTriangle.TowerBounds.physicalGlueMajorant, deletedExtensionMajorant_agrees]

def physicalWeightMajorant (M : ℕ) : ℕ :=
  max ((1+4*(6*M^2+1))*physicalGlueMajorant M*(M*(M*M))) (M*(M*M))+1

theorem physicalWeightMajorant_agrees : physicalWeightMajorant = TypedTriangle.TowerBounds.physicalWeightMajorant := by
  funext M
  simp only [physicalWeightMajorant, TypedTriangle.TowerBounds.physicalWeightMajorant, physicalGlueMajorant_agrees]

def bankGammaBound (M : ℕ) : ℕ := M*M*8

theorem bankGammaBound_agrees : bankGammaBound = TypedTriangle.TowerBounds.bankGammaBound := by
  funext M
  simp only [bankGammaBound, TypedTriangle.TowerBounds.bankGammaBound]

def bankEtaBound (M B : ℕ) : ℕ := max (M*(M^2)*8) (bankGammaBound M*(B+1))

theorem bankEtaBound_agrees : bankEtaBound = TypedTriangle.TowerBounds.bankEtaBound := by
  funext M B
  simp only [bankEtaBound, TypedTriangle.TowerBounds.bankEtaBound, bankGammaBound_agrees]

def monitorCapBound (M K : ℕ) : ℕ := (M*(K+1))*(2+15*M)

theorem monitorCapBound_agrees : monitorCapBound = TypedTriangle.TowerBounds.monitorCapBound := by
  funext M K
  simp only [monitorCapBound, TypedTriangle.TowerBounds.monitorCapBound]

def forkEpsilonMajorant (M : ℕ) : ℕ := M^2*(1024*(M+1))

theorem forkEpsilonMajorant_agrees : forkEpsilonMajorant = TypedTriangle.TowerBounds.forkEpsilonMajorant := by
  funext M
  simp only [forkEpsilonMajorant, TypedTriangle.TowerBounds.forkEpsilonMajorant]

def withdrawalKappaMajorant (M : ℕ) : ℕ := M*M*2

theorem withdrawalKappaMajorant_agrees : withdrawalKappaMajorant = TypedTriangle.TowerBounds.withdrawalKappaMajorant := by
  funext M
  simp only [withdrawalKappaMajorant, TypedTriangle.TowerBounds.withdrawalKappaMajorant]

def selectorEpsilonMajorant (M B : ℕ) : ℕ := (M+1)^2*(10000*B)

theorem selectorEpsilonMajorant_agrees : selectorEpsilonMajorant = TypedTriangle.TowerBounds.selectorEpsilonMajorant := by
  funext M B
  simp only [selectorEpsilonMajorant, TypedTriangle.TowerBounds.selectorEpsilonMajorant]

def selectorAMajorant (M : ℕ) : ℕ := 200*M+8

theorem selectorAMajorant_agrees : selectorAMajorant = TypedTriangle.TowerBounds.selectorAMajorant := by
  funext M
  simp only [selectorAMajorant, TypedTriangle.TowerBounds.selectorAMajorant]

def paymentGammaMajorant (M : ℕ) : ℕ := max (M*M*32) (M*8)

theorem paymentGammaMajorant_agrees : paymentGammaMajorant = TypedTriangle.TowerBounds.paymentGammaMajorant := by
  funext M
  simp only [paymentGammaMajorant, TypedTriangle.TowerBounds.paymentGammaMajorant]

def paymentTMajorant (M : ℕ) : ℕ := M+61*M+61

theorem paymentTMajorant_agrees : paymentTMajorant = TypedTriangle.TowerBounds.paymentTMajorant := by
  funext M
  simp only [paymentTMajorant, TypedTriangle.TowerBounds.paymentTMajorant]

def paymentCostMajorant (M : ℕ) : ℕ := 2*(paymentGammaMajorant M+8)*paymentTMajorant M+4

theorem paymentCostMajorant_agrees : paymentCostMajorant = TypedTriangle.TowerBounds.paymentCostMajorant := by
  funext M
  simp only [paymentCostMajorant, TypedTriangle.TowerBounds.paymentCostMajorant, paymentGammaMajorant_agrees, paymentTMajorant_agrees]

def paymentInputMajorant (M : ℕ) : ℕ :=
  max (M*M*(8*paymentCostMajorant M)) (M*(12*paymentTMajorant M))

theorem paymentInputMajorant_agrees : paymentInputMajorant = TypedTriangle.TowerBounds.paymentInputMajorant := by
  funext M
  simp only [paymentInputMajorant, TypedTriangle.TowerBounds.paymentInputMajorant, paymentCostMajorant_agrees, paymentTMajorant_agrees]

def selectorQMajorant (M B : ℕ) : ℕ := 4*B*(M+1)+2

theorem selectorQMajorant_agrees : selectorQMajorant = TypedTriangle.TowerBounds.selectorQMajorant := by
  funext M B
  simp only [selectorQMajorant, TypedTriangle.TowerBounds.selectorQMajorant]

def selectorScale (M : ℕ) : ℕ :=
  M+M*M*2+M*2+selectorAMajorant M+selectorQMajorant M (selectorAMajorant M)+1

theorem selectorScale_agrees : selectorScale = TypedTriangle.TowerBounds.selectorScale := by
  funext M
  simp only [selectorScale, TypedTriangle.TowerBounds.selectorScale, selectorAMajorant_agrees, selectorQMajorant_agrees]

def selectorInputMajorant (M : ℕ) : ℕ :=
  max (selectorEpsilonMajorant M (selectorAMajorant M)) (paymentInputMajorant (selectorScale M))

theorem selectorInputMajorant_agrees : selectorInputMajorant = TypedTriangle.TowerBounds.selectorInputMajorant := by
  funext M
  simp only [selectorInputMajorant, TypedTriangle.TowerBounds.selectorInputMajorant, paymentInputMajorant_agrees, selectorAMajorant_agrees, selectorEpsilonMajorant_agrees, selectorScale_agrees]

def forkQMajorant (M : ℕ) : ℕ := 128*M+1

theorem forkQMajorant_agrees : forkQMajorant = TypedTriangle.TowerBounds.forkQMajorant := by
  funext M
  simp only [forkQMajorant, TypedTriangle.TowerBounds.forkQMajorant]

def withdrawalKMajorant (M : ℕ) : ℕ := forkQMajorant (withdrawalKappaMajorant M)+6

theorem withdrawalKMajorant_agrees : withdrawalKMajorant = TypedTriangle.TowerBounds.withdrawalKMajorant := by
  funext M
  simp only [withdrawalKMajorant, TypedTriangle.TowerBounds.withdrawalKMajorant, forkQMajorant_agrees, withdrawalKappaMajorant_agrees]

def paymentForbiddenMajorant (M : ℕ) : ℕ := M*M*16

theorem paymentForbiddenMajorant_agrees : paymentForbiddenMajorant = TypedTriangle.TowerBounds.paymentForbiddenMajorant := by
  funext M
  simp only [paymentForbiddenMajorant, TypedTriangle.TowerBounds.paymentForbiddenMajorant]

def selectorStockMajorant (M : ℕ) : ℕ :=
  max (selectorEpsilonMajorant M (selectorAMajorant M)) (paymentForbiddenMajorant (selectorScale M))

theorem selectorStockMajorant_agrees : selectorStockMajorant = TypedTriangle.TowerBounds.selectorStockMajorant := by
  funext M
  simp only [selectorStockMajorant, TypedTriangle.TowerBounds.selectorStockMajorant, paymentForbiddenMajorant_agrees, selectorAMajorant_agrees, selectorEpsilonMajorant_agrees, selectorScale_agrees]

def withdrawalInputMajorant (M : ℕ) : ℕ :=
  max (forkEpsilonMajorant (withdrawalKappaMajorant M))
    (max (max (selectorInputMajorant (2*M)) (M*2)*(4*withdrawalKMajorant M))
      (selectorStockMajorant M*(8*withdrawalKMajorant M)))

theorem withdrawalInputMajorant_agrees : withdrawalInputMajorant = TypedTriangle.TowerBounds.withdrawalInputMajorant := by
  funext M
  simp only [withdrawalInputMajorant, TypedTriangle.TowerBounds.withdrawalInputMajorant, forkEpsilonMajorant_agrees, selectorInputMajorant_agrees, selectorStockMajorant_agrees, withdrawalKMajorant_agrees, withdrawalKappaMajorant_agrees]

def resourceOutputMajorant (M : ℕ) : ℕ := max (M*M*16) M

theorem resourceOutputMajorant_agrees : resourceOutputMajorant = TypedTriangle.TowerBounds.resourceOutputMajorant := by
  funext M
  simp only [resourceOutputMajorant, TypedTriangle.TowerBounds.resourceOutputMajorant]

def resourceInputScale (M : ℕ) : ℕ := M+resourceOutputMajorant M+1

theorem resourceInputScale_agrees : resourceInputScale = TypedTriangle.TowerBounds.resourceInputScale := by
  funext M
  simp only [resourceInputScale, TypedTriangle.TowerBounds.resourceInputScale, resourceOutputMajorant_agrees]

def resourceInputMajorant (M : ℕ) : ℕ :=
  max (withdrawalInputMajorant (resourceInputScale M)*4) (max (resourceOutputMajorant M) M)

theorem resourceInputMajorant_agrees : resourceInputMajorant = TypedTriangle.TowerBounds.resourceInputMajorant := by
  funext M
  simp only [resourceInputMajorant, TypedTriangle.TowerBounds.resourceInputMajorant, resourceInputScale_agrees, resourceOutputMajorant_agrees, withdrawalInputMajorant_agrees]

def resourceCompletionMajorant (M : ℕ) : ℕ :=
  M*2*(max (resourceInputMajorant M*12) 2)^2*2

theorem resourceCompletionMajorant_agrees : resourceCompletionMajorant = TypedTriangle.TowerBounds.resourceCompletionMajorant := by
  funext M
  simp only [resourceCompletionMajorant, TypedTriangle.TowerBounds.resourceCompletionMajorant, resourceInputMajorant_agrees]

def samplingPrecisionMajorant (M : ℕ) : ℕ := max (M^2*4) (M*M^4*128)

theorem samplingPrecisionMajorant_agrees : samplingPrecisionMajorant = TypedTriangle.TowerBounds.samplingPrecisionMajorant := by
  funext M
  simp only [samplingPrecisionMajorant, TypedTriangle.TowerBounds.samplingPrecisionMajorant]

def basalSamplingMajorant (M : ℕ) : ℕ := 96*samplingPrecisionMajorant M^4+1

theorem basalSamplingMajorant_agrees : basalSamplingMajorant = TypedTriangle.TowerBounds.basalSamplingMajorant := by
  funext M
  simp only [basalSamplingMajorant, TypedTriangle.TowerBounds.basalSamplingMajorant, samplingPrecisionMajorant_agrees]

def stockRateMajorant (M : ℕ) : ℕ := max (M*12) 2

theorem stockRateMajorant_agrees : stockRateMajorant = TypedTriangle.TowerBounds.stockRateMajorant := by
  funext M
  simp only [stockRateMajorant, TypedTriangle.TowerBounds.stockRateMajorant]

def rawStockSamplingScale (M : ℕ) : ℕ := M+stockRateMajorant M+M*2+1

theorem rawStockSamplingScale_agrees : rawStockSamplingScale = TypedTriangle.TowerBounds.rawStockSamplingScale := by
  funext M
  simp only [rawStockSamplingScale, TypedTriangle.TowerBounds.rawStockSamplingScale, stockRateMajorant_agrees]

def rawStockOrderMajorant (M : ℕ) : ℕ :=
  max (referenceOrderBound (8*M)) (basalSamplingMajorant (rawStockSamplingScale M))

theorem rawStockOrderMajorant_agrees : rawStockOrderMajorant = TypedTriangle.TowerBounds.rawStockOrderMajorant := by
  funext M
  simp only [rawStockOrderMajorant, TypedTriangle.TowerBounds.rawStockOrderMajorant, basalSamplingMajorant_agrees, rawStockSamplingScale_agrees, referenceOrderBound_agrees]

def resourceStockOrderScale (M : ℕ) : ℕ := M+resourceInputMajorant M+1

theorem resourceStockOrderScale_agrees : resourceStockOrderScale = TypedTriangle.TowerBounds.resourceStockOrderScale := by
  funext M
  simp only [resourceStockOrderScale, TypedTriangle.TowerBounds.resourceStockOrderScale, resourceInputMajorant_agrees]

def paymentOrderMajorant (M : ℕ) : ℕ := max (max (paymentInputMajorant M) (paymentGammaMajorant M)) 1

theorem paymentOrderMajorant_agrees : paymentOrderMajorant = TypedTriangle.TowerBounds.paymentOrderMajorant := by
  funext M
  simp only [paymentOrderMajorant, TypedTriangle.TowerBounds.paymentOrderMajorant, paymentGammaMajorant_agrees, paymentInputMajorant_agrees]

def selectorOrderMajorant (M : ℕ) : ℕ :=
  max (paymentOrderMajorant (selectorScale M)) (200*(M+1))

theorem selectorOrderMajorant_agrees : selectorOrderMajorant = TypedTriangle.TowerBounds.selectorOrderMajorant := by
  funext M
  simp only [selectorOrderMajorant, TypedTriangle.TowerBounds.selectorOrderMajorant, paymentOrderMajorant_agrees, selectorScale_agrees]

def withdrawalOrderMajorant (M : ℕ) : ℕ :=
  max (max (selectorOrderMajorant (2*M)) (32*withdrawalKappaMajorant M)) (withdrawalInputMajorant M)

theorem withdrawalOrderMajorant_agrees : withdrawalOrderMajorant = TypedTriangle.TowerBounds.withdrawalOrderMajorant := by
  funext M
  simp only [withdrawalOrderMajorant, TypedTriangle.TowerBounds.withdrawalOrderMajorant, selectorOrderMajorant_agrees, withdrawalInputMajorant_agrees, withdrawalKappaMajorant_agrees]

def resourceOrderMajorant (M : ℕ) : ℕ :=
  max (rawStockOrderMajorant (resourceStockOrderScale M))
    (max (withdrawalOrderMajorant (resourceInputScale M))
      (4*withdrawalInputMajorant (resourceInputScale M)))

theorem resourceOrderMajorant_agrees : resourceOrderMajorant = TypedTriangle.TowerBounds.resourceOrderMajorant := by
  funext M
  simp only [resourceOrderMajorant, TypedTriangle.TowerBounds.resourceOrderMajorant, rawStockOrderMajorant_agrees, resourceInputScale_agrees, resourceStockOrderScale_agrees, withdrawalInputMajorant_agrees, withdrawalOrderMajorant_agrees]

def stockBankResourceScale (M h : ℕ) : ℕ := M+bankProtectionBound M h*2+1

theorem stockBankResourceScale_agrees : stockBankResourceScale = TypedTriangle.TowerBounds.stockBankResourceScale := by
  funext M h
  simp only [stockBankResourceScale, TypedTriangle.TowerBounds.stockBankResourceScale, bankProtectionBound_agrees]

def catalogCompressionOrderMajorant (M : ℕ) : ℕ :=
  max (compressionOrderMajorant M) (2*compressionOrderMajorant (M*2))

theorem catalogCompressionOrderMajorant_agrees : catalogCompressionOrderMajorant = TypedTriangle.TowerBounds.catalogCompressionOrderMajorant := by
  funext M
  simp only [catalogCompressionOrderMajorant, TypedTriangle.TowerBounds.catalogCompressionOrderMajorant, compressionOrderMajorant_agrees]

def deletionNumerator (U h : ℕ) : ℕ := 8*((U+3)+(U+1+h)*2^(h.choose 2))

theorem deletionNumerator_agrees : deletionNumerator = TypedTriangle.TowerBounds.deletionNumerator := by
  funext U h
  simp only [deletionNumerator, TypedTriangle.TowerBounds.deletionNumerator]

def deletionOrderBound (M U h N : ℕ) : ℕ := deletionNumerator U h*M+1+2*N

theorem deletionOrderBound_agrees : deletionOrderBound = TypedTriangle.TowerBounds.deletionOrderBound := by
  funext M U h N
  simp only [deletionOrderBound, TypedTriangle.TowerBounds.deletionOrderBound, deletionNumerator_agrees]

def supplySupportBound (K h k : ℕ) : ℕ :=
  2*k+3*(K*k)+K*k*(2*h-2)+3*(K*k)*(2*h-3)

theorem supplySupportBound_agrees : supplySupportBound = TypedTriangle.TowerBounds.supplySupportBound := by
  funext K h k
  simp only [supplySupportBound, TypedTriangle.TowerBounds.supplySupportBound]

def supplyOrderBound (M K h k : ℕ) : ℕ := deletionOrderBound M (supplySupportBound K h k) h 0

theorem supplyOrderBound_agrees : supplyOrderBound = TypedTriangle.TowerBounds.supplyOrderBound := by
  funext M K h k
  simp only [supplyOrderBound, TypedTriangle.TowerBounds.supplyOrderBound, deletionOrderBound_agrees, supplySupportBound_agrees]

def boundedPieceOrderMajorant (M h k : ℕ) : ℕ :=
  max (compressionOrderMajorant M) (supplyOrderBound M (uniformCertMajorant M) h k)

theorem boundedPieceOrderMajorant_agrees : boundedPieceOrderMajorant = TypedTriangle.TowerBounds.boundedPieceOrderMajorant := by
  funext M h k
  simp only [boundedPieceOrderMajorant, TypedTriangle.TowerBounds.boundedPieceOrderMajorant, compressionOrderMajorant_agrees, supplyOrderBound_agrees, uniformCertMajorant_agrees]

def bankCellOrderMajorant (M h : ℕ) : ℕ :=
  2*boundedPieceOrderMajorant (M*2) h (4*bankRerouteMajorant M)+40*bankRerouteMajorant M*M+1

theorem bankCellOrderMajorant_agrees : bankCellOrderMajorant = TypedTriangle.TowerBounds.bankCellOrderMajorant := by
  funext M h
  simp only [bankCellOrderMajorant, TypedTriangle.TowerBounds.bankCellOrderMajorant, bankRerouteMajorant_agrees, boundedPieceOrderMajorant_agrees]

def atomCoreOrderMajorant (M : ℕ) : ℕ := 2*(routeOrderMajorant (M*2)+(3*(M*2)+1))

theorem atomCoreOrderMajorant_agrees : atomCoreOrderMajorant = TypedTriangle.TowerBounds.atomCoreOrderMajorant := by
  funext M
  simp only [atomCoreOrderMajorant, TypedTriangle.TowerBounds.atomCoreOrderMajorant, routeOrderMajorant_agrees]

def quadraticOrderMajorant (M E B : ℕ) : ℕ := max 1 (max (4*M) (max (2*M) (2*(B*E)*M)))

theorem quadraticOrderMajorant_agrees : quadraticOrderMajorant = TypedTriangle.TowerBounds.quadraticOrderMajorant := by
  funext M E B
  simp only [quadraticOrderMajorant, TypedTriangle.TowerBounds.quadraticOrderMajorant]

def nativeBankOrderMajorant (M h P : ℕ) : ℕ :=
  max (catalogCompressionOrderMajorant M) (max (bankCellOrderMajorant M h)
    (max (atomCoreOrderMajorant M)
      (quadraticOrderMajorant (max (bankToleranceBound M h) (bankDeletionBound M h))
        (bankCellSizeMajorant M h) (bankCopiesMajorant M P))))

theorem nativeBankOrderMajorant_agrees : nativeBankOrderMajorant = TypedTriangle.TowerBounds.nativeBankOrderMajorant := by
  funext M h P
  simp only [nativeBankOrderMajorant, TypedTriangle.TowerBounds.nativeBankOrderMajorant, atomCoreOrderMajorant_agrees, bankCellOrderMajorant_agrees, bankCellSizeMajorant_agrees, bankCopiesMajorant_agrees, bankDeletionBound_agrees, bankToleranceBound_agrees, catalogCompressionOrderMajorant_agrees, quadraticOrderMajorant_agrees]

def preparedBankOrderMajorant (M h P : ℕ) : ℕ :=
  max (nativeBankOrderMajorant (preparedBankInputMajorant M h) h P)
    (atomCoreOrderMajorant (preparedBankInputMajorant M h))

theorem preparedBankOrderMajorant_agrees : preparedBankOrderMajorant = TypedTriangle.TowerBounds.preparedBankOrderMajorant := by
  funext M h P
  simp only [preparedBankOrderMajorant, TypedTriangle.TowerBounds.preparedBankOrderMajorant, atomCoreOrderMajorant_agrees, nativeBankOrderMajorant_agrees, preparedBankInputMajorant_agrees]

def stockBankOrderMajorant (M h : ℕ) : ℕ :=
  max (resourceOrderMajorant (stockBankResourceScale M h)) (2*preparedBankOrderMajorant M h M*M)

theorem stockBankOrderMajorant_agrees : stockBankOrderMajorant = TypedTriangle.TowerBounds.stockBankOrderMajorant := by
  funext M h
  simp only [stockBankOrderMajorant, TypedTriangle.TowerBounds.stockBankOrderMajorant, preparedBankOrderMajorant_agrees, resourceOrderMajorant_agrees, stockBankResourceScale_agrees]

def layerComplementOrderMajorant (M : ℕ) : ℕ :=
  max (16*M+1) (max (geometryOrderMajorant M) (latticeOrderMajorant M))

theorem layerComplementOrderMajorant_agrees : layerComplementOrderMajorant = TypedTriangle.TowerBounds.layerComplementOrderMajorant := by
  funext M
  simp only [layerComplementOrderMajorant, TypedTriangle.TowerBounds.layerComplementOrderMajorant, geometryOrderMajorant_agrees, latticeOrderMajorant_agrees]

def monitoredPackingOrderBound (M : ℕ) : ℕ := max 2 (cloneBound (3*M+2))

theorem monitoredPackingOrderBound_agrees : monitoredPackingOrderBound = TypedTriangle.TowerBounds.monitoredPackingOrderBound := by
  funext M
  simp only [monitoredPackingOrderBound, TypedTriangle.TowerBounds.monitoredPackingOrderBound, cloneBound_agrees]

def packingSignedScale (M : ℕ) : ℕ := max M (max (M*3) (max (M*(5*M)) (M+1)))

theorem packingSignedScale_agrees : packingSignedScale = TypedTriangle.TowerBounds.packingSignedScale := by
  funext M
  simp only [packingSignedScale, TypedTriangle.TowerBounds.packingSignedScale]

def signedEnvelopeOrderBound (M : ℕ) : ℕ := max 2 (monitoredPackingOrderBound (packingSignedScale M))

theorem signedEnvelopeOrderBound_agrees : signedEnvelopeOrderBound = TypedTriangle.TowerBounds.signedEnvelopeOrderBound := by
  funext M
  simp only [signedEnvelopeOrderBound, TypedTriangle.TowerBounds.signedEnvelopeOrderBound, monitoredPackingOrderBound_agrees, packingSignedScale_agrees]

def packingLocalizedScale (M : ℕ) : ℕ := max M (max (M*6) (max (6*M) (9*M)))

theorem packingLocalizedScale_agrees : packingLocalizedScale = TypedTriangle.TowerBounds.packingLocalizedScale := by
  funext M
  simp only [packingLocalizedScale, TypedTriangle.TowerBounds.packingLocalizedScale]

def localizedSignedOrderBound (M : ℕ) : ℕ := signedEnvelopeOrderBound (packingLocalizedScale M)

theorem localizedSignedOrderBound_agrees : localizedSignedOrderBound = TypedTriangle.TowerBounds.localizedSignedOrderBound := by
  funext M
  simp only [localizedSignedOrderBound, TypedTriangle.TowerBounds.localizedSignedOrderBound, packingLocalizedScale_agrees, signedEnvelopeOrderBound_agrees]

def packingPhysicalScale (M : ℕ) : ℕ := max M (max (2*M) (M*2))

theorem packingPhysicalScale_agrees : packingPhysicalScale = TypedTriangle.TowerBounds.packingPhysicalScale := by
  funext M
  simp only [packingPhysicalScale, TypedTriangle.TowerBounds.packingPhysicalScale]

def physicalMomentOrderBound (M : ℕ) : ℕ :=
  max (16*M+1) (localizedSignedOrderBound (packingPhysicalScale M))

theorem physicalMomentOrderBound_agrees : physicalMomentOrderBound = TypedTriangle.TowerBounds.physicalMomentOrderBound := by
  funext M
  simp only [physicalMomentOrderBound, TypedTriangle.TowerBounds.physicalMomentOrderBound, localizedSignedOrderBound_agrees, packingPhysicalScale_agrees]

def packingCoverRateBound (M : ℕ) : ℕ := max (M*64) (max (M*64) 64)

theorem packingCoverRateBound_agrees : packingCoverRateBound = TypedTriangle.TowerBounds.packingCoverRateBound := by
  funext M
  simp only [packingCoverRateBound, TypedTriangle.TowerBounds.packingCoverRateBound]

def packingCoverBudgetBound (M : ℕ) : ℕ := (packingCoverRateBound M)^2

theorem packingCoverBudgetBound_agrees : packingCoverBudgetBound = TypedTriangle.TowerBounds.packingCoverBudgetBound := by
  funext M
  simp only [packingCoverBudgetBound, TypedTriangle.TowerBounds.packingCoverBudgetBound, packingCoverRateBound_agrees]

def packingStockScale (M : ℕ) : ℕ := max M (max (packingCoverBudgetBound M*4) 4)

theorem packingStockScale_agrees : packingStockScale = TypedTriangle.TowerBounds.packingStockScale := by
  funext M
  simp only [packingStockScale, TypedTriangle.TowerBounds.packingStockScale, packingCoverBudgetBound_agrees]

def stockMomentOrderBound (M : ℕ) : ℕ :=
  max (physicalMomentOrderBound (packingStockScale M))
    (max (packingCoverRateBound M) (2*packingCoverBudgetBound M))

theorem stockMomentOrderBound_agrees : stockMomentOrderBound = TypedTriangle.TowerBounds.stockMomentOrderBound := by
  funext M
  simp only [stockMomentOrderBound, TypedTriangle.TowerBounds.stockMomentOrderBound, packingCoverBudgetBound_agrees, packingCoverRateBound_agrees, packingStockScale_agrees, physicalMomentOrderBound_agrees]

def fixedPackingOrderBound (M : ℕ) : ℕ := stockMomentOrderBound M

theorem fixedPackingOrderBound_agrees : fixedPackingOrderBound = TypedTriangle.TowerBounds.fixedPackingOrderBound := by
  funext M
  simp only [fixedPackingOrderBound, TypedTriangle.TowerBounds.fixedPackingOrderBound, stockMomentOrderBound_agrees]

def nativePartitionInputMajorant (M : ℕ) : ℕ := M+2*M+paidDensityMajorant M+1

theorem nativePartitionInputMajorant_agrees : nativePartitionInputMajorant = TypedTriangle.TowerBounds.nativePartitionInputMajorant := by
  funext M
  simp only [nativePartitionInputMajorant, TypedTriangle.TowerBounds.nativePartitionInputMajorant, paidDensityMajorant_agrees]

def nativePartitionOrderMajorant (M : ℕ) : ℕ :=
  max (layerComplementOrderMajorant M) (fixedPackingOrderBound (nativePartitionInputMajorant M))

theorem nativePartitionOrderMajorant_agrees : nativePartitionOrderMajorant = TypedTriangle.TowerBounds.nativePartitionOrderMajorant := by
  funext M
  simp only [nativePartitionOrderMajorant, TypedTriangle.TowerBounds.nativePartitionOrderMajorant, fixedPackingOrderBound_agrees, layerComplementOrderMajorant_agrees, nativePartitionInputMajorant_agrees]

def physicalGlueOrderMajorant (M : ℕ) : ℕ :=
  max (max (compressionOrderMajorant M) (max (routeOrderMajorant M) (3*M+1))) (3*M+1)

theorem physicalGlueOrderMajorant_agrees : physicalGlueOrderMajorant = TypedTriangle.TowerBounds.physicalGlueOrderMajorant := by
  funext M
  simp only [physicalGlueOrderMajorant, TypedTriangle.TowerBounds.physicalGlueOrderMajorant, compressionOrderMajorant_agrees, routeOrderMajorant_agrees]

def nativeWeightOrderMajorant (M : ℕ) : ℕ := 4*physicalGlueOrderMajorant (2*M)*M+1

theorem nativeWeightOrderMajorant_agrees : nativeWeightOrderMajorant = TypedTriangle.TowerBounds.nativeWeightOrderMajorant := by
  funext M
  simp only [nativeWeightOrderMajorant, TypedTriangle.TowerBounds.nativeWeightOrderMajorant, physicalGlueOrderMajorant_agrees]

def bankOrderBound (M : ℕ) : ℕ := 8*(M*(M^2))+1

theorem bankOrderBound_agrees : bankOrderBound = TypedTriangle.TowerBounds.bankOrderBound := by
  funext M
  simp only [bankOrderBound, TypedTriangle.TowerBounds.bankOrderBound]

def bankStep (M h : ℕ) : ℕ :=
  M+4096+128*M+64*M^2+4*M^3+(M+2)*M+
  catalogDimensionMajorant M+catalogCoefficientMajorant M+catalogColumnMajorant M+
  bankRadiusMajorant M+bankCatalogSizeMajorant M+bankCellSizeMajorant M h+
  bankProtectionBound M h+coreDeltaBound M h+deletionBudgetMajorant M+nativeDeleteMajorant M+
  natEnvelope 20 M+2*natEnvelope 4 M+bankToleranceBound M h+
  preparedBankRateMajorant M h M+physicalWeightMajorant M+bankEtaBound M M+monitorCapBound M M+
  resourceInputMajorant M+resourceOutputMajorant M+resourceCompletionMajorant M+
  stockBankOrderMajorant M h+nativePartitionOrderMajorant M+nativeWeightOrderMajorant M+bankOrderBound M

theorem bankStep_agrees : bankStep = TypedTriangle.TowerBounds.bankStep := by
  funext M h
  simp only [bankStep, TypedTriangle.TowerBounds.bankStep, bankCatalogSizeMajorant_agrees, bankCellSizeMajorant_agrees, bankEtaBound_agrees, bankOrderBound_agrees, bankProtectionBound_agrees, bankRadiusMajorant_agrees, bankToleranceBound_agrees, catalogCoefficientMajorant_agrees, catalogColumnMajorant_agrees, catalogDimensionMajorant_agrees, coreDeltaBound_agrees, deletionBudgetMajorant_agrees, monitorCapBound_agrees, natEnvelope_agrees, nativeDeleteMajorant_agrees, nativePartitionOrderMajorant_agrees, nativeWeightOrderMajorant_agrees, physicalWeightMajorant_agrees, preparedBankRateMajorant_agrees, resourceCompletionMajorant_agrees, resourceInputMajorant_agrees, resourceOutputMajorant_agrees, stockBankOrderMajorant_agrees]

def bankStage (h : ℕ) : ℕ → ℕ → ℕ
  | 0,M => M
  | k+1,M => bankStep (bankStage h k M) h

theorem bankStage_agrees : bankStage = TypedTriangle.TowerBounds.bankStage := by
  funext h k M
  induction k generalizing M with
  | zero => rfl
  | succ j ih => simp only [bankStage, TypedTriangle.TowerBounds.bankStage, bankStep_agrees, ih]

def layerThresholdMajorant (M h : ℕ) : ℕ := bankStage h 16 M

theorem layerThresholdMajorant_agrees : layerThresholdMajorant = TypedTriangle.TowerBounds.layerThresholdMajorant := by
  funext M h
  simp only [layerThresholdMajorant, TypedTriangle.TowerBounds.layerThresholdMajorant, bankStage_agrees]

def cleanLayerThresholdMajorant (M h : ℕ) : ℕ :=
  max (layerThresholdMajorant (3*M+1) h) (2*max 1 M*M)

theorem cleanLayerThresholdMajorant_agrees : cleanLayerThresholdMajorant = TypedTriangle.TowerBounds.cleanLayerThresholdMajorant := by
  funext M h
  simp only [cleanLayerThresholdMajorant, TypedTriangle.TowerBounds.cleanLayerThresholdMajorant, layerThresholdMajorant_agrees]

def windowRouteMajorant (M : ℕ) : ℕ := M*M*(32*(M+1)*4^M)

theorem windowRouteMajorant_agrees : windowRouteMajorant = TypedTriangle.TowerBounds.windowRouteMajorant := by
  funext M
  simp only [windowRouteMajorant, TypedTriangle.TowerBounds.windowRouteMajorant]

def outerLayerParameterScale (M : ℕ) : ℕ :=
  M+M*16+2*M+M*32+M*4+windowRouteMajorant (2*M)*4+(M+1)+1

theorem outerLayerParameterScale_agrees : outerLayerParameterScale = TypedTriangle.TowerBounds.outerLayerParameterScale := by
  funext M
  simp only [outerLayerParameterScale, TypedTriangle.TowerBounds.outerLayerParameterScale, windowRouteMajorant_agrees]

def scheduledPrecisionMajorant (M : ℕ) : ℕ := max (M*8) (128*M*M)

theorem scheduledPrecisionMajorant_agrees : scheduledPrecisionMajorant = TypedTriangle.TowerBounds.scheduledPrecisionMajorant := by
  funext M
  simp only [scheduledPrecisionMajorant, TypedTriangle.TowerBounds.scheduledPrecisionMajorant]

def scheduledOrderMajorant (M : ℕ) : ℕ := max 1 ((scheduledPrecisionMajorant M)^4)

theorem scheduledOrderMajorant_agrees : scheduledOrderMajorant = TypedTriangle.TowerBounds.scheduledOrderMajorant := by
  funext M
  simp only [scheduledOrderMajorant, TypedTriangle.TowerBounds.scheduledOrderMajorant, scheduledPrecisionMajorant_agrees]

def innerLayerOrderMajorant (M h : ℕ) : ℕ :=
  max 1 (max (cleanLayerThresholdMajorant (outerLayerParameterScale M) h) (max (scheduledOrderMajorant M) (2*M)))

theorem innerLayerOrderMajorant_agrees : innerLayerOrderMajorant = TypedTriangle.TowerBounds.innerLayerOrderMajorant := by
  funext M h
  simp only [innerLayerOrderMajorant, TypedTriangle.TowerBounds.innerLayerOrderMajorant, cleanLayerThresholdMajorant_agrees, outerLayerParameterScale_agrees, scheduledOrderMajorant_agrees]

def thresholdLayerScale (A h : ℕ) : ℕ :=
  A+innerLayerOrderMajorant A h+max 1 (scheduledOrderMajorant A)+1

theorem thresholdLayerScale_agrees : thresholdLayerScale = TypedTriangle.TowerBounds.thresholdLayerScale := by
  funext A h
  simp only [thresholdLayerScale, TypedTriangle.TowerBounds.thresholdLayerScale, innerLayerOrderMajorant_agrees, scheduledOrderMajorant_agrees]

def rawPolynomialBound (R : ℕ) : ℕ := max 1 ((4*Nat.factorial 14)*R^14)

theorem rawPolynomialBound_agrees : rawPolynomialBound = TypedTriangle.TowerBounds.rawPolynomialBound := by
  funext R
  simp only [rawPolynomialBound, TypedTriangle.TowerBounds.rawPolynomialBound]

def rawHingeRateBound (M : ℕ) : ℕ :=
  (M^2 * M^(2*(M+2))) * ((4*(compressionPowerMajorant (M+6))^2)*(M+2))

theorem rawHingeRateBound_agrees : rawHingeRateBound = TypedTriangle.TowerBounds.rawHingeRateBound := by
  funext M
  simp only [rawHingeRateBound, TypedTriangle.TowerBounds.rawHingeRateBound, compressionPowerMajorant_agrees]

def rawGeometryRateBound (M : ℕ) : ℕ :=
  max (M^2*4) (max ((M^2*M^2)*4) (rawHingeRateBound M))

theorem rawGeometryRateBound_agrees : rawGeometryRateBound = TypedTriangle.TowerBounds.rawGeometryRateBound := by
  funext M
  simp only [rawGeometryRateBound, TypedTriangle.TowerBounds.rawGeometryRateBound, rawHingeRateBound_agrees]

def rawTestRateBound (M T : ℕ) : ℕ :=
  max (rawGeometryRateBound M) (max (M^2*(8*M)) T)

theorem rawTestRateBound_agrees : rawTestRateBound = TypedTriangle.TowerBounds.rawTestRateBound := by
  funext M T
  simp only [rawTestRateBound, TypedTriangle.TowerBounds.rawTestRateBound, rawGeometryRateBound_agrees]

def rawAutomaticOrderBound (M T : ℕ) : ℕ :=
  max 1 (max (rawPolynomialBound (rawTestRateBound M T)) 3)

theorem rawAutomaticOrderBound_agrees : rawAutomaticOrderBound = TypedTriangle.TowerBounds.rawAutomaticOrderBound := by
  funext M T
  simp only [rawAutomaticOrderBound, TypedTriangle.TowerBounds.rawAutomaticOrderBound, rawPolynomialBound_agrees, rawTestRateBound_agrees]

def rawNativeTailBound (M : ℕ) : ℕ :=
  (nativeDensityMajorant M * M^(2*nativeInteriorMajorant M)) * (16*(nativeInteriorMajorant M)^2)

theorem rawNativeTailBound_agrees : rawNativeTailBound = TypedTriangle.TowerBounds.rawNativeTailBound := by
  funext M
  simp only [rawNativeTailBound, TypedTriangle.TowerBounds.rawNativeTailBound, nativeDensityMajorant_agrees, nativeInteriorMajorant_agrees]

def oddPathOrderMajorant (M : ℕ) : ℕ :=
  4*(oddPathMajorant M+2)^2*((M+1)^(oddPathMajorant M+3))+1

theorem oddPathOrderMajorant_agrees : oddPathOrderMajorant = TypedTriangle.TowerBounds.oddPathOrderMajorant := by
  funext M
  simp only [oddPathOrderMajorant, TypedTriangle.TowerBounds.oddPathOrderMajorant, oddPathMajorant_agrees]

def nativeRouteOrderMajorant (M : ℕ) : ℕ :=
  max (oddPathOrderMajorant (nativePathInputMajorant M)) (3*M+1)

theorem nativeRouteOrderMajorant_agrees : nativeRouteOrderMajorant = TypedTriangle.TowerBounds.nativeRouteOrderMajorant := by
  funext M
  simp only [nativeRouteOrderMajorant, TypedTriangle.TowerBounds.nativeRouteOrderMajorant, nativePathInputMajorant_agrees, oddPathOrderMajorant_agrees]

def rawNativeSampleOrderBound (M : ℕ) : ℕ :=
  max (rawAutomaticOrderBound M (rawNativeTailBound M)) (max (nativeRouteOrderMajorant M) 1)

theorem rawNativeSampleOrderBound_agrees : rawNativeSampleOrderBound = TypedTriangle.TowerBounds.rawNativeSampleOrderBound := by
  funext M
  simp only [rawNativeSampleOrderBound, TypedTriangle.TowerBounds.rawNativeSampleOrderBound, nativeRouteOrderMajorant_agrees, rawAutomaticOrderBound_agrees, rawNativeTailBound_agrees]

def rawGlobalInputBound (M : ℕ) : ℕ := max M (max (M*2) (2*M))

theorem rawGlobalInputBound_agrees : rawGlobalInputBound = TypedTriangle.TowerBounds.rawGlobalInputBound := by
  funext M
  simp only [rawGlobalInputBound, TypedTriangle.TowerBounds.rawGlobalInputBound]

def globalRawStepOrderBound (M : ℕ) : ℕ :=
  max (max (rawNativeSampleOrderBound (rawGlobalInputBound M)) ((8*(M+1))^4))
    (max (2*M*M) 1)

theorem globalRawStepOrderBound_agrees : globalRawStepOrderBound = TypedTriangle.TowerBounds.globalRawStepOrderBound := by
  funext M
  simp only [globalRawStepOrderBound, TypedTriangle.TowerBounds.globalRawStepOrderBound, rawGlobalInputBound_agrees, rawNativeSampleOrderBound_agrees]

def nestedOrderMajorant (M : ℕ) : ℕ := (16+16*M*compressionPowerMajorant M)*M+1

theorem nestedOrderMajorant_agrees : nestedOrderMajorant = TypedTriangle.TowerBounds.nestedOrderMajorant := by
  funext M
  simp only [nestedOrderMajorant, TypedTriangle.TowerBounds.nestedOrderMajorant, compressionPowerMajorant_agrees]

def entryOrderMajorant (M : ℕ) : ℕ := max (nestedOrderMajorant M) (2*compressionOrderMajorant (M*2))

theorem entryOrderMajorant_agrees : entryOrderMajorant = TypedTriangle.TowerBounds.entryOrderMajorant := by
  funext M
  simp only [entryOrderMajorant, TypedTriangle.TowerBounds.entryOrderMajorant, compressionOrderMajorant_agrees, nestedOrderMajorant_agrees]

def coreOrderMajorant (M : ℕ) : ℕ := max (nestedOrderMajorant M) (2*M)

theorem coreOrderMajorant_agrees : coreOrderMajorant = TypedTriangle.TowerBounds.coreOrderMajorant := by
  funext M
  simp only [coreOrderMajorant, TypedTriangle.TowerBounds.coreOrderMajorant, nestedOrderMajorant_agrees]

def preparationOrderMajorant (M : ℕ) : ℕ :=
  max (entryOrderMajorant M) (2*max (entryOrderMajorant M) (coreOrderMajorant M))

theorem preparationOrderMajorant_agrees : preparationOrderMajorant = TypedTriangle.TowerBounds.preparationOrderMajorant := by
  funext M
  simp only [preparationOrderMajorant, TypedTriangle.TowerBounds.preparationOrderMajorant, coreOrderMajorant_agrees, entryOrderMajorant_agrees]

def rawGeometryShapeBound (M K A : ℕ) : ℕ :=
  max ((A*(M+1))^4) (max (32^4) (max (4*K) (((2*(M+1))*compressionPowerMajorant M)*K)))

theorem rawGeometryShapeBound_agrees : rawGeometryShapeBound = TypedTriangle.TowerBounds.rawGeometryShapeBound := by
  funext M K A
  simp only [rawGeometryShapeBound, TypedTriangle.TowerBounds.rawGeometryShapeBound, compressionPowerMajorant_agrees]

def rawRequiredGeometryBound (M : ℕ) : ℕ := rawGeometryShapeBound M ((M*M^M)*4) 8

theorem rawRequiredGeometryBound_agrees : rawRequiredGeometryBound = TypedTriangle.TowerBounds.rawRequiredGeometryBound := by
  funext M
  simp only [rawRequiredGeometryBound, TypedTriangle.TowerBounds.rawRequiredGeometryBound, rawGeometryShapeBound_agrees]

def rawMinimumOrderBound (M : ℕ) : ℕ :=
  max (max (preparationOrderMajorant (M*4)) M) (max 1 (rawRequiredGeometryBound M+1))

theorem rawMinimumOrderBound_agrees : rawMinimumOrderBound = TypedTriangle.TowerBounds.rawMinimumOrderBound := by
  funext M
  simp only [rawMinimumOrderBound, TypedTriangle.TowerBounds.rawMinimumOrderBound, preparationOrderMajorant_agrees, rawRequiredGeometryBound_agrees]

def rawTerminalInputBound (M : ℕ) : ℕ := max M (2*rawMinimumOrderBound M)

theorem rawTerminalInputBound_agrees : rawTerminalInputBound = TypedTriangle.TowerBounds.rawTerminalInputBound := by
  funext M
  simp only [rawTerminalInputBound, TypedTriangle.TowerBounds.rawTerminalInputBound, rawMinimumOrderBound_agrees]

def rawTerminalOrderBound (M : ℕ) : ℕ :=
  max (globalRawStepOrderBound (rawTerminalInputBound M)) (rawMinimumOrderBound M)

theorem rawTerminalOrderBound_agrees : rawTerminalOrderBound = TypedTriangle.TowerBounds.rawTerminalOrderBound := by
  funext M
  simp only [rawTerminalOrderBound, TypedTriangle.TowerBounds.rawTerminalOrderBound, globalRawStepOrderBound_agrees, rawMinimumOrderBound_agrees, rawTerminalInputBound_agrees]

def thresholdTerminalScale (R : ℕ) : ℕ := R+rawTerminalOrderBound R+8*R+1

theorem thresholdTerminalScale_agrees : thresholdTerminalScale = TypedTriangle.TowerBounds.thresholdTerminalScale := by
  funext R
  simp only [thresholdTerminalScale, TypedTriangle.TowerBounds.thresholdTerminalScale, rawTerminalOrderBound_agrees]

def placementDenBound (M k s : ℕ) : ℕ := 2*(1+k+s+2*s*s*(M+1))

theorem placementDenBound_agrees : placementDenBound = TypedTriangle.TowerBounds.placementDenBound := by
  funext M k s
  simp only [placementDenBound, TypedTriangle.TowerBounds.placementDenBound]

def terminalBudgetBound (M t s : ℕ) : ℕ := 2*(M*placementDenBound M t s)

theorem terminalBudgetBound_agrees : terminalBudgetBound = TypedTriangle.TowerBounds.terminalBudgetBound := by
  funext M t s
  simp only [terminalBudgetBound, TypedTriangle.TowerBounds.terminalBudgetBound, placementDenBound_agrees]

def reserveBudgetBound (M K h t : ℕ) : ℕ :=
  terminalBudgetBound (supplyBudgetBound M h) t (supplySizeBound K h (t*t))

theorem reserveBudgetBound_agrees : reserveBudgetBound = TypedTriangle.TowerBounds.reserveBudgetBound := by
  funext M K h t
  simp only [reserveBudgetBound, TypedTriangle.TowerBounds.reserveBudgetBound, supplyBudgetBound_agrees, supplySizeBound_agrees, terminalBudgetBound_agrees]

def reserveRateBound (M K h t : ℕ) : ℕ := max 64 (reserveBudgetBound M K h t*4)

theorem reserveRateBound_agrees : reserveRateBound = TypedTriangle.TowerBounds.reserveRateBound := by
  funext M K h t
  simp only [reserveRateBound, TypedTriangle.TowerBounds.reserveRateBound, reserveBudgetBound_agrees]

def terminalUniformRateMajorant (M h : ℕ) : ℕ := reserveRateBound M (uniformCertMajorant M) h M

theorem terminalUniformRateMajorant_agrees : terminalUniformRateMajorant = TypedTriangle.TowerBounds.terminalUniformRateMajorant := by
  funext M h
  simp only [terminalUniformRateMajorant, TypedTriangle.TowerBounds.terminalUniformRateMajorant, reserveRateBound_agrees, uniformCertMajorant_agrees]

def placementOrderBound (M s : ℕ) : ℕ := 2*s*M+1

theorem placementOrderBound_agrees : placementOrderBound = TypedTriangle.TowerBounds.placementOrderBound := by
  funext M s
  simp only [placementOrderBound, TypedTriangle.TowerBounds.placementOrderBound]

def terminalOrderBound (M t s : ℕ) : ℕ :=
  placementOrderBound M s+2*(2^(t*t)+t)*(M*placementDenBound M t s)

theorem terminalOrderBound_agrees : terminalOrderBound = TypedTriangle.TowerBounds.terminalOrderBound := by
  funext M t s
  simp only [terminalOrderBound, TypedTriangle.TowerBounds.terminalOrderBound, placementDenBound_agrees, placementOrderBound_agrees]

def reserveOrderBound (M K h t : ℕ) : ℕ :=
  max (supplyOrderBound M K h (t*t))
    (terminalOrderBound (supplyBudgetBound M h) t (supplySizeBound K h (t*t)))

theorem reserveOrderBound_agrees : reserveOrderBound = TypedTriangle.TowerBounds.reserveOrderBound := by
  funext M K h t
  simp only [reserveOrderBound, TypedTriangle.TowerBounds.reserveOrderBound, supplyBudgetBound_agrees, supplyOrderBound_agrees, supplySizeBound_agrees, terminalOrderBound_agrees]

def terminalUniformOrderMajorant (M h : ℕ) : ℕ := reserveOrderBound M (uniformCertMajorant M) h M

theorem terminalUniformOrderMajorant_agrees : terminalUniformOrderMajorant = TypedTriangle.TowerBounds.terminalUniformOrderMajorant := by
  funext M h
  simp only [terminalUniformOrderMajorant, TypedTriangle.TowerBounds.terminalUniformOrderMajorant, reserveOrderBound_agrees, uniformCertMajorant_agrees]

def reserveSizeBound (K h t : ℕ) : ℕ := supplySizeBound K h (t*t)*2^(t*t)

theorem reserveSizeBound_agrees : reserveSizeBound = TypedTriangle.TowerBounds.reserveSizeBound := by
  funext K h t
  simp only [reserveSizeBound, TypedTriangle.TowerBounds.reserveSizeBound, supplySizeBound_agrees]

def terminalReserveSizeMajorant (M h : ℕ) : ℕ := reserveSizeBound (uniformCertMajorant M) h M

theorem terminalReserveSizeMajorant_agrees : terminalReserveSizeMajorant = TypedTriangle.TowerBounds.terminalReserveSizeMajorant := by
  funext M h
  simp only [terminalReserveSizeMajorant, TypedTriangle.TowerBounds.terminalReserveSizeMajorant, reserveSizeBound_agrees, uniformCertMajorant_agrees]

def thresholdReserveScale (T h : ℕ) : ℕ :=
  T+terminalUniformRateMajorant T h+4*T+terminalUniformOrderMajorant T h+
    compressionOrderMajorant T+terminalReserveSizeMajorant T h+1

theorem thresholdReserveScale_agrees : thresholdReserveScale = TypedTriangle.TowerBounds.thresholdReserveScale := by
  funext T h
  simp only [thresholdReserveScale, TypedTriangle.TowerBounds.thresholdReserveScale, compressionOrderMajorant_agrees, terminalReserveSizeMajorant_agrees, terminalUniformOrderMajorant_agrees, terminalUniformRateMajorant_agrees]

def outerRawRequiredGeometryBound (M : ℕ) : ℕ := rawGeometryShapeBound M (M*M^M) 4

theorem outerRawRequiredGeometryBound_agrees : outerRawRequiredGeometryBound = TypedTriangle.TowerBounds.outerRawRequiredGeometryBound := by
  funext M
  simp only [outerRawRequiredGeometryBound, TypedTriangle.TowerBounds.outerRawRequiredGeometryBound, rawGeometryShapeBound_agrees]

def outerRawMinimumOrderBound (M : ℕ) : ℕ :=
  max (max (preparationOrderMajorant (M*4)) M) (max 1 (outerRawRequiredGeometryBound M+1))

theorem outerRawMinimumOrderBound_agrees : outerRawMinimumOrderBound = TypedTriangle.TowerBounds.outerRawMinimumOrderBound := by
  funext M
  simp only [outerRawMinimumOrderBound, TypedTriangle.TowerBounds.outerRawMinimumOrderBound, outerRawRequiredGeometryBound_agrees, preparationOrderMajorant_agrees]

def outerRawAutoInputBound (M : ℕ) : ℕ := max M (max (4*M) (2*M))

theorem outerRawAutoInputBound_agrees : outerRawAutoInputBound = TypedTriangle.TowerBounds.outerRawAutoInputBound := by
  funext M
  simp only [outerRawAutoInputBound, TypedTriangle.TowerBounds.outerRawAutoInputBound]

def outerRawRootOrderBound (M T : ℕ) : ℕ :=
  let B := outerRawMinimumOrderBound M
  2*max (rawAutomaticOrderBound (outerRawAutoInputBound M) T) (max B (2*B*M))+2

theorem outerRawRootOrderBound_agrees : outerRawRootOrderBound = TypedTriangle.TowerBounds.outerRawRootOrderBound := by
  funext M T
  simp only [outerRawRootOrderBound, TypedTriangle.TowerBounds.outerRawRootOrderBound, outerRawAutoInputBound_agrees, outerRawMinimumOrderBound_agrees, rawAutomaticOrderBound_agrees]

def rawOuterTestRateBound (M : ℕ) : ℕ :=
  max (((M*2)^2*M^2)*16)
    (((nativeDensityMajorant M*2)*M^(2*nativeInteriorMajorant M)) * (16*(nativeInteriorMajorant M)^2))

theorem rawOuterTestRateBound_agrees : rawOuterTestRateBound = TypedTriangle.TowerBounds.rawOuterTestRateBound := by
  funext M
  simp only [rawOuterTestRateBound, TypedTriangle.TowerBounds.rawOuterTestRateBound, nativeDensityMajorant_agrees, nativeInteriorMajorant_agrees]

def nativeOuterInputBound (M : ℕ) : ℕ := max M (8*M)

theorem nativeOuterInputBound_agrees : nativeOuterInputBound = TypedTriangle.TowerBounds.nativeOuterInputBound := by
  funext M
  simp only [nativeOuterInputBound, TypedTriangle.TowerBounds.nativeOuterInputBound]

def nativeOuterRootOrderBound (M : ℕ) : ℕ :=
  max (outerRawRootOrderBound M (rawOuterTestRateBound (nativeOuterInputBound M)))
    (nativeRouteOrderMajorant (nativeOuterInputBound M))

theorem nativeOuterRootOrderBound_agrees : nativeOuterRootOrderBound = TypedTriangle.TowerBounds.nativeOuterRootOrderBound := by
  funext M
  simp only [nativeOuterRootOrderBound, TypedTriangle.TowerBounds.nativeOuterRootOrderBound, nativeOuterInputBound_agrees, nativeRouteOrderMajorant_agrees, outerRawRootOrderBound_agrees, rawOuterTestRateBound_agrees]

def rawRootOrderBound (M : ℕ) : ℕ := 2*rawMinimumOrderBound M

theorem rawRootOrderBound_agrees : rawRootOrderBound = TypedTriangle.TowerBounds.rawRootOrderBound := by
  funext M
  simp only [rawRootOrderBound, TypedTriangle.TowerBounds.rawRootOrderBound, rawMinimumOrderBound_agrees]

def outerInnerInputBound (M : ℕ) : ℕ := max M (max 16 (rawRootOrderBound M))

theorem outerInnerInputBound_agrees : outerInnerInputBound = TypedTriangle.TowerBounds.outerInnerInputBound := by
  funext M
  simp only [outerInnerInputBound, TypedTriangle.TowerBounds.outerInnerInputBound, rawRootOrderBound_agrees]

def outerInnerRootOrderBound (M : ℕ) : ℕ := nativeOuterRootOrderBound (outerInnerInputBound M)

theorem outerInnerRootOrderBound_agrees : outerInnerRootOrderBound = TypedTriangle.TowerBounds.outerInnerRootOrderBound := by
  funext M
  simp only [outerInnerRootOrderBound, TypedTriangle.TowerBounds.outerInnerRootOrderBound, nativeOuterRootOrderBound_agrees, outerInnerInputBound_agrees]

def jointTrianglePackingOrderMajorant (M : ℕ) : ℕ := localizedSignedOrderBound (M+1)

theorem jointTrianglePackingOrderMajorant_agrees : jointTrianglePackingOrderMajorant = TypedTriangle.TowerBounds.jointTrianglePackingOrderMajorant := by
  funext M
  simp only [jointTrianglePackingOrderMajorant, TypedTriangle.TowerBounds.jointTrianglePackingOrderMajorant, localizedSignedOrderBound_agrees]

def triangleStockInputMajorant (M : ℕ) : ℕ := M+packingCoverBudgetBound M*4+4+1

theorem triangleStockInputMajorant_agrees : triangleStockInputMajorant = TypedTriangle.TowerBounds.triangleStockInputMajorant := by
  funext M
  simp only [triangleStockInputMajorant, TypedTriangle.TowerBounds.triangleStockInputMajorant, packingCoverBudgetBound_agrees]

def triangleStockOrderMajorant (M : ℕ) : ℕ :=
  max (jointTrianglePackingOrderMajorant (triangleStockInputMajorant M))
    (max (packingCoverRateBound M) (2*packingCoverBudgetBound M))

theorem triangleStockOrderMajorant_agrees : triangleStockOrderMajorant = TypedTriangle.TowerBounds.triangleStockOrderMajorant := by
  funext M
  simp only [triangleStockOrderMajorant, TypedTriangle.TowerBounds.triangleStockOrderMajorant, jointTrianglePackingOrderMajorant_agrees, packingCoverBudgetBound_agrees, packingCoverRateBound_agrees, triangleStockInputMajorant_agrees]

def triangleFixedPackingOrderMajorant (M : ℕ) : ℕ := triangleStockOrderMajorant M

theorem triangleFixedPackingOrderMajorant_agrees : triangleFixedPackingOrderMajorant = TypedTriangle.TowerBounds.triangleFixedPackingOrderMajorant := by
  funext M
  simp only [triangleFixedPackingOrderMajorant, TypedTriangle.TowerBounds.triangleFixedPackingOrderMajorant, triangleStockOrderMajorant_agrees]

def monitorFixedPartitionOrderMajorant (M : ℕ) : ℕ :=
  max (triangleFixedPackingOrderMajorant (M+2)) 2

theorem monitorFixedPartitionOrderMajorant_agrees : monitorFixedPartitionOrderMajorant = TypedTriangle.TowerBounds.monitorFixedPartitionOrderMajorant := by
  funext M
  simp only [monitorFixedPartitionOrderMajorant, TypedTriangle.TowerBounds.monitorFixedPartitionOrderMajorant, triangleFixedPackingOrderMajorant_agrees]

def triangleNativePartitionOrderMajorant (M : ℕ) : ℕ :=
  max (layerComplementOrderMajorant M)
    (max (monitorFixedPartitionOrderMajorant (nativePartitionInputMajorant M)) (max (16*M+1) 1))

theorem triangleNativePartitionOrderMajorant_agrees : triangleNativePartitionOrderMajorant = TypedTriangle.TowerBounds.triangleNativePartitionOrderMajorant := by
  funext M
  simp only [triangleNativePartitionOrderMajorant, TypedTriangle.TowerBounds.triangleNativePartitionOrderMajorant, layerComplementOrderMajorant_agrees, monitorFixedPartitionOrderMajorant_agrees, nativePartitionInputMajorant_agrees]

def triangleBankStep (M h : ℕ) : ℕ :=
  bankStep M h + triangleNativePartitionOrderMajorant M + 1

theorem triangleBankStep_agrees : triangleBankStep = TypedTriangle.TowerBounds.triangleBankStep := by
  funext M h
  simp only [triangleBankStep, TypedTriangle.TowerBounds.triangleBankStep, bankStep_agrees, triangleNativePartitionOrderMajorant_agrees]

def triangleBankStage (h : ℕ) : ℕ → ℕ → ℕ
  | 0,M => M
  | k+1,M => triangleBankStep (triangleBankStage h k M) h

theorem triangleBankStage_agrees : triangleBankStage = TypedTriangle.TowerBounds.triangleBankStage := by
  funext h k M
  induction k generalizing M with
  | zero => rfl
  | succ j ih => simp only [triangleBankStage, TypedTriangle.TowerBounds.triangleBankStage, triangleBankStep_agrees, ih]

def monitorLayerThresholdMajorant (M h : ℕ) : ℕ := triangleBankStage h 16 M

theorem monitorLayerThresholdMajorant_agrees : monitorLayerThresholdMajorant = TypedTriangle.TowerBounds.monitorLayerThresholdMajorant := by
  funext M h
  simp only [monitorLayerThresholdMajorant, TypedTriangle.TowerBounds.monitorLayerThresholdMajorant, triangleBankStage_agrees]

def monitorCleanLayerThresholdMajorant (M h : ℕ) : ℕ :=
  max (monitorLayerThresholdMajorant (3*M+1) h) (2*max 1 M*M)

theorem monitorCleanLayerThresholdMajorant_agrees : monitorCleanLayerThresholdMajorant = TypedTriangle.TowerBounds.monitorCleanLayerThresholdMajorant := by
  funext M h
  simp only [monitorCleanLayerThresholdMajorant, TypedTriangle.TowerBounds.monitorCleanLayerThresholdMajorant, monitorLayerThresholdMajorant_agrees]

def monitorOuterLayerOrderMajorant (M h : ℕ) : ℕ :=
  max 1 (max (monitorCleanLayerThresholdMajorant (outerLayerParameterScale M) h) (2*M))

theorem monitorOuterLayerOrderMajorant_agrees : monitorOuterLayerOrderMajorant = TypedTriangle.TowerBounds.monitorOuterLayerOrderMajorant := by
  funext M h
  simp only [monitorOuterLayerOrderMajorant, TypedTriangle.TowerBounds.monitorOuterLayerOrderMajorant, monitorCleanLayerThresholdMajorant_agrees, outerLayerParameterScale_agrees]

def rawStockBudgetMajorant (M : ℕ) : ℕ := max (referenceStockBudgetBound M) (M*8)

theorem rawStockBudgetMajorant_agrees : rawStockBudgetMajorant = TypedTriangle.TowerBounds.rawStockBudgetMajorant := by
  funext M
  simp only [rawStockBudgetMajorant, TypedTriangle.TowerBounds.rawStockBudgetMajorant, referenceStockBudgetBound_agrees]

def withdrawalStockMajorant (M : ℕ) : ℕ :=
  max (forkEpsilonMajorant (withdrawalKappaMajorant M)) (selectorStockMajorant M*4)

theorem withdrawalStockMajorant_agrees : withdrawalStockMajorant = TypedTriangle.TowerBounds.withdrawalStockMajorant := by
  funext M
  simp only [withdrawalStockMajorant, TypedTriangle.TowerBounds.withdrawalStockMajorant, forkEpsilonMajorant_agrees, selectorStockMajorant_agrees, withdrawalKappaMajorant_agrees]

def resourceTerminalMajorant (M : ℕ) : ℕ :=
  max (rawStockBudgetMajorant M) (max (withdrawalStockMajorant M) (M*M*16))

theorem resourceTerminalMajorant_agrees : resourceTerminalMajorant = TypedTriangle.TowerBounds.resourceTerminalMajorant := by
  funext M
  simp only [resourceTerminalMajorant, TypedTriangle.TowerBounds.resourceTerminalMajorant, rawStockBudgetMajorant_agrees, withdrawalStockMajorant_agrees]

def layerTerminalInputMajorant (M : ℕ) : ℕ := M+2*M+2*bankProtectionBound M M+1

theorem layerTerminalInputMajorant_agrees : layerTerminalInputMajorant = TypedTriangle.TowerBounds.layerTerminalInputMajorant := by
  funext M
  simp only [layerTerminalInputMajorant, TypedTriangle.TowerBounds.layerTerminalInputMajorant, bankProtectionBound_agrees]

def layerTerminalMajorant (M : ℕ) : ℕ :=
  max (resourceTerminalMajorant (layerTerminalInputMajorant M)) ((M+1)*M*64)

theorem layerTerminalMajorant_agrees : layerTerminalMajorant = TypedTriangle.TowerBounds.layerTerminalMajorant := by
  funext M
  simp only [layerTerminalMajorant, TypedTriangle.TowerBounds.layerTerminalMajorant, layerTerminalInputMajorant_agrees, resourceTerminalMajorant_agrees]

def outerLayerTerminalMajorant (M : ℕ) : ℕ := layerTerminalMajorant (outerLayerParameterScale M)

theorem outerLayerTerminalMajorant_agrees : outerLayerTerminalMajorant = TypedTriangle.TowerBounds.outerLayerTerminalMajorant := by
  funext M
  simp only [outerLayerTerminalMajorant, TypedTriangle.TowerBounds.outerLayerTerminalMajorant, layerTerminalMajorant_agrees, outerLayerParameterScale_agrees]

def triangleThresholdFinalMajorant (U h : ℕ) : ℕ :=
  U+outerInnerRootOrderBound U+monitorOuterLayerOrderMajorant U h+U*outerLayerTerminalMajorant U+1

theorem triangleThresholdFinalMajorant_agrees : triangleThresholdFinalMajorant = TypedTriangle.TowerBounds.triangleThresholdFinalMajorant := by
  funext U h
  simp only [triangleThresholdFinalMajorant, TypedTriangle.TowerBounds.triangleThresholdFinalMajorant, monitorOuterLayerOrderMajorant_agrees, outerInnerRootOrderBound_agrees, outerLayerTerminalMajorant_agrees]

def paperIIITriangleTowerHeight (K hOriginal qStat : ℕ) : ℕ :=
  let h := initialHingeOrder hOriginal
  let M := triangleThresholdInputMajorant K hOriginal qStat
  let A := thresholdAgendaMajorant M
  let R := thresholdLayerScale A h
  let T := thresholdTerminalScale R
  let U := thresholdReserveScale T h
  triangleThresholdFinalMajorant U h

theorem paperIIITriangleTowerHeight_agrees : paperIIITriangleTowerHeight = TypedTriangle.TowerBounds.paperIIITriangleTowerHeight := by
  funext K hOriginal qStat
  simp only [paperIIITriangleTowerHeight, TypedTriangle.TowerBounds.paperIIITriangleTowerHeight, initialHingeOrder_agrees, thresholdAgendaMajorant_agrees, thresholdLayerScale_agrees, thresholdReserveScale_agrees, thresholdTerminalScale_agrees, triangleThresholdFinalMajorant_agrees, triangleThresholdInputMajorant_agrees]

theorem height_agrees (K h q : ℕ) :
    paperIIITriangleTowerHeight K h q =
      TypedTriangle.TowerBounds.paperIIITriangleTowerHeight K h q := by
  exact congrFun (congrFun (congrFun paperIIITriangleTowerHeight_agrees K) h) q

set_option pp.fullNames true
#print axioms height_agrees
end TypedTriangle.PrintedHeight
