module
public import RequestProject.TypedTriangle.TowerNatTerminal
public import RequestProject.TypedTriangle.TowerUniformCertificate
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TypedTriangle.TowerBounds

theorem reserveSizeBound_mono_t (K h : ℕ) {t T : ℕ} (ht : t ≤ T) :
    reserveSizeBound K h t ≤ reserveSizeBound K h T := by
  unfold reserveSizeBound supplySizeBound
  gcongr

theorem reserveRateBound_mono_t (M K h : ℕ) {t T : ℕ} (ht : t ≤ T) :
    reserveRateBound M K h t ≤ reserveRateBound M K h T := by
  unfold reserveRateBound reserveBudgetBound terminalBudgetBound placementDenBound supplySizeBound
  gcongr

theorem reserveOrderBound_mono_t (M K h : ℕ) {t T : ℕ} (ht : t ≤ T) :
    reserveOrderBound M K h t ≤ reserveOrderBound M K h T := by
  unfold reserveOrderBound supplyOrderBound deletionOrderBound deletionNumerator
    supplySupportBound terminalOrderBound placementOrderBound placementDenBound supplySizeBound
  gcongr

def terminalUniformRateMajorant (M h : ℕ) : ℕ := reserveRateBound M (uniformCertMajorant M) h M
def terminalUniformOrderMajorant (M h : ℕ) : ℕ := reserveOrderBound M (uniformCertMajorant M) h M
def terminalReserveSizeMajorant (M h : ℕ) : ℕ := reserveSizeBound (uniformCertMajorant M) h M

theorem terminalUniformRate_magnitude {M h t L : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) (ht : t ≤ M)
    (β : Fin (L+1) → ℝ) (hβ : ∀ r, Magnitude M (β r)) :
    Magnitude (terminalUniformRateMajorant M h)
      (PreparedSupply.Explicit.uniformOuterRate α h t L β) := by
  have hK : PreparedSupply.Explicit.absorberCost α h ≤ uniformCertMajorant M :=
    uniformCertCost_le_majorant hα hh
  exact (uniformReserveRate_magnitude hα h t L β hβ hK).mono
    (reserveRateBound_mono_t M (uniformCertMajorant M) h ht)

theorem terminalUniformOrder_le_majorant {M h t L : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) (ht : t ≤ M)
    (β : Fin (L+1) → ℝ) (hβ : ∀ r, Magnitude M (β r)) :
    PreparedSupply.Explicit.uniformReserveOrder α h t L β ≤ terminalUniformOrderMajorant M h := by
  have hK : PreparedSupply.Explicit.absorberCost α h ≤ uniformCertMajorant M :=
    uniformCertCost_le_majorant hα hh
  exact (uniformReserveOrder_le hα h t L β hβ hK).trans
    (reserveOrderBound_mono_t M (uniformCertMajorant M) h ht)

theorem terminalReserveSize_le_majorant {M h t : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) (ht : t ≤ M) :
    PreparedSupply.Explicit.reserveSize α h t ≤ terminalReserveSizeMajorant M h :=
  (reserveSize_le h t (uniformCertCost_le_majorant hα hh)).trans
    (reserveSizeBound_mono_t (uniformCertMajorant M) h ht)

#print axioms terminalUniformRate_magnitude
#print axioms terminalUniformOrder_le_majorant
#print axioms terminalReserveSize_le_majorant
end TypedTriangle.TowerBounds
