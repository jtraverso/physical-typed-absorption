module
public import RequestProject.TypedTriangle.ExplicitTriangleMonitorConcreteOuterLayer
public import RequestProject.TypedTriangle.ExplicitGlobalAssemblyParameters
public import RequestProject.TypedTriangle.ExplicitOuterInnerRawPreparedVortex
public import RequestProject.TypedTriangle.ExplicitUniformTerminalReserve
public import RequestProject.TypedTriangle.ExplicitCleanHinge
@[expose] public section
noncomputable section
namespace TypedTriangle.Vortex.Explicit
open ExplicitRaw

/-- A specified finite formula, independent of the host and of the label
constraint F. The numerical main assembly must certify its adequacy for T
from the concrete producers at the specified orders. -/
def paperIIITriangleThreshold (αOriginal C η : ℝ) (hOriginal qStat : ℕ) : ℕ :=
  let ζStat := η/4
  let α := min αOriginal (S07V49.hingeConstB αOriginal 1 hOriginal)/8
  let h := 2*hOriginal-3
  let ε := rawPreparationTolerance α C h
  let d := rawPreparationRank α h
  let T := rawPreparationTorsion α h
  let L := d+(d+1)*Nat.log 2 T
  let mInner := nativeInteriorCount (α/2) h
  let aInner := nativeDensity (α/2) h
  let mOuter := nativeInteriorCount (8*α) h
  let aOuter := nativeDensity (8*α) h
  let δOuter := nativeOuterAvoidBudget (8*α) h
  let εBank := monitorComplementBudget (2*C) (α/16) h ζStat
  let γStock := resourceStockBudget (α/16) (2*C)
  let ηBank := CatalogNative.Explicit.bankProtectionBudget (α/16) (α/32) h
  let ρ := futureDensity (α/8) C h
  let qInner := globalInnerRate α aInner aOuter εBank γStock ηBank ρ h mInner mOuter
  let ζ := assemblyStateCap α C εBank γStock ηBank aInner aOuter h mInner mOuter
  let β := assemblyRadius α C ε δOuter εBank γStock ηBank aInner aOuter h L mInner mOuter
  let Ninner := assemblyScheduleOrder α C ε δOuter εBank γStock ηBank aInner aOuter h L mInner mOuter
  let K := fun r => paidInverseCost (α/8) (β r) h
  let εRef := fun r => referenceLoad (α/8) C ζ h (β r)
  let γRef := fun r => referenceAvoid (α/8) C ζ h (β r)
  let nRef := fun r => referenceThreshold (α/8) C ζ h (β r)
  let nPaid := fun _ : ℕ => paidInverseOrder (α/8) h
  let nGeometry := ExplicitPaid.paidOrder (α/8) h
  let Minner := innerLayerOrder α C qInner aInner h mInner L K εRef γRef nRef nPaid nGeometry
  let MrawBudget := max 1 (scheduledProfileOrder C K εRef L)
  let Mrequired := max Minner MrawBudget
  let t := rawTerminalOrder α C qInner h Ninner Mrequired
  let tNat := ⌈t⌉₊
  let βFinite := fun r : Fin (L+1) => β r
  let qReserve := PreparedSupply.Explicit.uniformOuterRate (α/8) h tNat L βFinite
  let qOuter := min qReserve (εBank/4)
  let Nreserve := PreparedSupply.Explicit.absorberOrder (α/8) h
  let nAbs := PreparedSupply.Explicit.uniformReserveOrder (α/8) h tNat L βFinite
  let Nouter := max Nreserve nAbs
  let nRaw := outerInnerRootOrder α C qInner qOuter h Ninner Mrequired Nouter
  let θT := outerLayerTerminalBudget α C qOuter aOuter h mOuter L γRef
  let nOuter := monitorOuterLayerOrder α C qOuter aOuter ζStat h mOuter L qStat γRef nRef nPaid nGeometry
  let Kreserve := PreparedSupply.Explicit.reserveSize (α/8) h tNat
  max (cleanHingeOrder αOriginal hOriginal)
    (max nRaw (max nOuter ⌈(Kreserve:ℝ)/θT⌉₊))

end TypedTriangle.Vortex.Explicit
