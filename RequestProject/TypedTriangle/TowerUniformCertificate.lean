module
public import RequestProject.TypedTriangle.TowerGeometryPreparation
public import RequestProject.TypedTriangle.TowerNatMonitors
public import RequestProject.TypedTriangle.ExplicitPaidSmooth
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.TowerBounds
open ExplicitSample ExplicitCertificate NativeSmooth.Explicit Vortex.Explicit

def compHMajorant (M S : ℕ) : ℕ :=
  1+8*compL2Majorant M+5*compNMajorant M+32*(2*S+1)*compNMajorant M

def uniformCertMajorant (M : ℕ) : ℕ :=
  let S := compressionSampleMajorant M
  natEnvelope 6 (S+compHMajorant M S+compDMajorant M S)

theorem clamp_one_magnitude {M : ℕ} {x : ℝ} (hx : Magnitude M x) :
    Magnitude M (min x 1) := by
  have h1 : Magnitude M (1:ℝ) := Magnitude.one.mono (by have := hx.bound_pos; omega)
  simpa only [max_self] using hx.min h1

theorem compH_le_majorant {M s S : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hs : s ≤ S) : compH0 α s ≤ compHMajorant M S := by
  have hL := compL2_le_majorant hα
  have hN := compN_le_majorant hα
  unfold compH0 compL5 compHMajorant
  gcongr

theorem uniformCertCost_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) : uniformCertCost α h ≤ uniformCertMajorant M := by
  let S := compressionSampleMajorant M
  let Z := S+compHMajorant M S+compDMajorant M S
  have hs : compressionSampleSize α h ≤ S := compressionSampleSize_le_majorant hα hh
  have hH := compH_le_majorant (clamp_one_magnitude hα) hs
  have hD := compD_le_majorant (clamp_one_magnitude hα) hs
  have hsZ : S ≤ Z := by dsimp [Z]; omega
  have hHZ : compHMajorant M S ≤ Z := by dsimp [Z]; omega
  have hDZ : compDMajorant M S ≤ Z := by dsimp [Z]; omega
  exact compressionCertCost_le_envelope
    (hs.trans (hsZ.trans (le_natEnvelope 0 Z)))
    (hH.trans (hHZ.trans (le_natEnvelope 0 Z)))
    (hD.trans (hDZ.trans (le_natEnvelope 0 Z)))


#print axioms uniformCertCost_le_majorant
end TypedTriangle.TowerBounds
