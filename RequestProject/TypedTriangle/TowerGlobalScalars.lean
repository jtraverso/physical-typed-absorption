module
public import RequestProject.TypedTriangle.TowerGeometrySample
public import RequestProject.TypedTriangle.ExplicitGlobalAssemblyParameters
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.TowerBounds

def pathRatioMajorant (M k : ℕ) : ℕ := M*(k*M*2^M)
def hingeRatioMajorant (M k : ℕ) : ℕ := M*(k*compressionPowerMajorant M)
def uniformInnerRateMajorant (M : ℕ) : ℕ :=
  max 32 (max (M*4) (max (M*2) (max (M*16) (max (M*8)
    (max (hingeRatioMajorant M 64) (pathRatioMajorant M 64))))))
def adjustedBankWindowMajorant (M : ℕ) : ℕ := max M (pathRatioMajorant M 32)
def globalInnerInputMajorant (M : ℕ) : ℕ := max M (adjustedBankWindowMajorant M)
def globalInnerRateMajorant (M : ℕ) : ℕ := uniformInnerRateMajorant (globalInnerInputMajorant M)
def windowRouteRateMajorant (M : ℕ) : ℕ := M*M*(32*(M+1)*4^M)
def stateHoleCapMajorant (M : ℕ) : ℕ := max (windowRouteRateMajorant M*4) (M*M*128)
def preparationDebtMajorant (M : ℕ) : ℕ :=
  max M (max M (max (hingeRatioMajorant M 4) (8*max 1 (2*M))))
def globalDebtMajorant (M : ℕ) : ℕ :=
  max 8 (max (M*128) (max (pathRatioMajorant M 64)
    (max (pathRatioMajorant M 128) (preparationDebtMajorant M))))
def assemblyStateInputMajorant (M : ℕ) : ℕ := max M (globalInnerRateMajorant M)
def assemblyStateMajorant (M : ℕ) : ℕ := stateHoleCapMajorant (assemblyStateInputMajorant M)

theorem pathRatio_magnitude {M m : ℕ} {a : ℝ}
    (ha : Magnitude M a) (hm0 : 0 < m) (hm : m ≤ M) (k : ℕ) (hk : 1 ≤ k) :
    Magnitude (pathRatioMajorant M k) (a/((k:ℝ)*m*2^m)) := by
  have hp := ((Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) (le_refl 2)).pow m).mono
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hm)
  have hn := Magnitude.natCast (by omega : 1 ≤ m) hm
  exact ha.div (((Magnitude.natCast hk (le_refl k)).mul hn).mul hp)

theorem hingeRatio_magnitude {M h : ℕ} {a : ℝ}
    (ha : Magnitude M a) (hh : h ≤ M) (k : ℕ) (hk : 1 ≤ k) :
    Magnitude (hingeRatioMajorant M k) (a/((k:ℝ)*2^h.choose 2)) :=
  ha.div ((Magnitude.natCast hk (le_refl k)).mul (hingePower_magnitude hh))

theorem uniformInnerRate_magnitude {M h m : ℕ} {α a ε γ η ρ : ℝ}
    (hα : Magnitude M α) (ha : Magnitude M a) (hε : Magnitude M ε)
    (hγ : Magnitude M γ) (hη : Magnitude M η) (hρ : Magnitude M ρ)
    (hh : h ≤ M) (hm0 : 0 < m) (hm : m ≤ M) :
    Magnitude (uniformInnerRateMajorant M) (Vortex.Explicit.uniformInnerRate α a ε γ η ρ h m) := by
  have h32 := (Magnitude.natCast (by decide : 1 ≤ (32:ℕ)) (le_refl 32)).inv
  have h4 := hε.div (Magnitude.natCast (by decide : 1 ≤ (4:ℕ)) (le_refl 4))
  have h2 := hρ.div (Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) (le_refl 2))
  have h16 := hη.div (Magnitude.natCast (by decide : 1 ≤ (16:ℕ)) (le_refl 16))
  have h8 := hγ.div (Magnitude.natCast (by decide : 1 ≤ (8:ℕ)) (le_refl 8))
  have h := h32.min (h4.min (h2.min (h16.min (h8.min
    ((hingeRatio_magnitude hα hh 64 (by decide)).min (pathRatio_magnitude ha hm0 hm 64 (by decide)))))))
  simpa only [uniformInnerRateMajorant, Vortex.Explicit.uniformInnerRate, Nat.cast_ofNat] using h

theorem adjustedBankWindow_magnitude {M m : ℕ} {ε a : ℝ}
    (hε : Magnitude M ε) (ha : Magnitude M a) (hm0 : 0 < m) (hm : m ≤ M) :
    Magnitude (adjustedBankWindowMajorant M) (Vortex.Explicit.adjustedBankWindow ε a m) := by
  exact hε.min (pathRatio_magnitude ha hm0 hm 32 (by decide))

theorem globalInnerRate_magnitude {M h mI mO : ℕ} {α aI aO ε γ η ρ : ℝ}
    (hα : Magnitude M α) (haI : Magnitude M aI) (haO : Magnitude M aO)
    (hε : Magnitude M ε) (hγ : Magnitude M γ) (hη : Magnitude M η) (hρ : Magnitude M ρ)
    (hh : h ≤ M) (hmI0 : 0 < mI) (hmI : mI ≤ M) (hmO0 : 0 < mO) (hmO : mO ≤ M) :
    Magnitude (globalInnerRateMajorant M) (Vortex.Explicit.globalInnerRate α aI aO ε γ η ρ h mI mO) := by
  have hM : M ≤ globalInnerInputMajorant M := le_max_left _ _
  have he := (adjustedBankWindow_magnitude hε haO hmO0 hmO).mono
    (show adjustedBankWindowMajorant M ≤ globalInnerInputMajorant M from le_max_right _ _)
  exact uniformInnerRate_magnitude (hα.mono hM) (haI.mono hM) he (hγ.mono hM)
    (hη.mono hM) (hρ.mono hM) (hh.trans hM) hmI0 (hmI.trans hM)

theorem windowRouteRate_magnitude {M m : ℕ} {a q : ℝ}
    (ha : Magnitude M a) (hq : Magnitude M q) (hm : m ≤ M) :
    Magnitude (windowRouteRateMajorant M) (Vortex.windowRouteRate a q m) := by
  have h32 := Magnitude.natCast (by decide : 1 ≤ (32:ℕ)) (le_refl 32)
  have hn := Magnitude.natCast (by omega : 1 ≤ m+1) (Nat.add_le_add_right hm 1)
  have hp := ((Magnitude.natCast (by decide : 1 ≤ (4:ℕ)) (le_refl 4)).pow m).mono
    (Nat.pow_le_pow_right (by decide : 1 ≤ (4:ℕ)) hm)
  have h := (ha.mul hq).div ((h32.mul hn).mul hp)
  simpa only [windowRouteRateMajorant, Vortex.windowRouteRate, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat] using h

theorem stateHoleCap_magnitude {M m : ℕ} {α a q : ℝ}
    (hα : Magnitude M α) (ha : Magnitude M a) (hq : Magnitude M q) (hm : m ≤ M) :
    Magnitude (stateHoleCapMajorant M) (Vortex.Explicit.stateHoleCap α a q m) := by
  exact ((windowRouteRate_magnitude ha hq hm).div
      (Magnitude.natCast (by decide : 1 ≤ (4:ℕ)) (le_refl 4))).min
    ((hα.mul hq).div (Magnitude.natCast (by decide : 1 ≤ (128:ℕ)) (le_refl 128)))

theorem preparationDebt_magnitude {M h : ℕ} {α C ε δ : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hε : Magnitude M ε) (hδ : Magnitude M δ)
    (hh : h ≤ M) :
    Magnitude (preparationDebtMajorant M) (Vortex.Explicit.preparationDebtCap α C ε δ h) := by
  have h2 := Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) (le_refl 2)
  have h8 := Magnitude.natCast (by decide : 1 ≤ (8:ℕ)) (le_refl 8)
  have hlast := (h8.mul (Magnitude.one.max (h2.mul hC))).inv
  exact hδ.min (hε.min ((hingeRatio_magnitude hα hh 4 (by decide)).min hlast))

theorem globalDebt_magnitude {M h mI mO : ℕ} {α C ε δ aI aO : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hε : Magnitude M ε) (hδ : Magnitude M δ)
    (haI : Magnitude M aI) (haO : Magnitude M aO) (hh : h ≤ M)
    (hmI0 : 0 < mI) (hmI : mI ≤ M) (hmO0 : 0 < mO) (hmO : mO ≤ M) :
    Magnitude (globalDebtMajorant M) (Vortex.Explicit.globalDebtCap α C ε δ aI aO h mI mO) := by
  have h8 := (Magnitude.natCast (by decide : 1 ≤ (8:ℕ)) (le_refl 8)).inv
  have h128 := hα.div (Magnitude.natCast (by decide : 1 ≤ (128:ℕ)) (le_refl 128))
  have h := h8.min (h128.min ((pathRatio_magnitude haI hmI0 hmI 64 (by decide)).min
    ((pathRatio_magnitude haO hmO0 hmO 128 (by decide)).min (preparationDebt_magnitude hα hC hε hδ hh))))
  simpa only [globalDebtMajorant, Vortex.Explicit.globalDebtCap, Nat.cast_ofNat] using h

theorem assemblyStateCap_magnitude {M h mI mO : ℕ} {α C ε γ η aI aO : ℝ}
    (hα : Magnitude M α) (hε : Magnitude M ε) (hγ : Magnitude M γ) (hη : Magnitude M η)
    (haI : Magnitude M aI) (haO : Magnitude M aO)
    (hρ : Magnitude M (Vortex.Explicit.futureDensity (α/8) C h)) (hh : h ≤ M)
    (hmI0 : 0 < mI) (hmI : mI ≤ M) (hmO0 : 0 < mO) (hmO : mO ≤ M) :
    Magnitude (assemblyStateMajorant M) (Vortex.Explicit.assemblyStateCap α C ε γ η aI aO h mI mO) := by
  have hq := globalInnerRate_magnitude hα haI haO hε hγ hη hρ hh hmI0 hmI hmO0 hmO
  have hM : M ≤ assemblyStateInputMajorant M := le_max_left _ _
  exact stateHoleCap_magnitude (hα.mono hM) (haI.mono hM)
    (hq.mono (show globalInnerRateMajorant M ≤ assemblyStateInputMajorant M from le_max_right _ _))
    (hmI.trans hM)

#print axioms uniformInnerRate_magnitude
#print axioms globalInnerRate_magnitude
#print axioms windowRouteRate_magnitude
#print axioms stateHoleCap_magnitude
#print axioms preparationDebt_magnitude
#print axioms globalDebt_magnitude
#print axioms assemblyStateCap_magnitude
end TypedTriangle.TowerBounds
