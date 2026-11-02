module
public import RequestProject.TypedTriangle.TowerBankCatalog
public import RequestProject.TypedTriangle.TowerBankBudgets
public import RequestProject.TypedTriangle.TowerUniformCertificate
public import RequestProject.TypedTriangle.ExplicitStructuredBank
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.TowerBounds

def boundedPieceSizeMajorant (M h k : ℕ) : ℕ := supplySizeBound (uniformCertMajorant M) h k
def boundedPieceOrderMajorant (M h k : ℕ) : ℕ :=
  max (compressionOrderMajorant M) (supplyOrderBound M (uniformCertMajorant M) h k)
def bankCellSizeMajorant (M h : ℕ) : ℕ :=
  boundedPieceSizeMajorant (M*2) h (4*bankRerouteMajorant M)+4*bankRerouteMajorant M
def bankCellOrderMajorant (M h : ℕ) : ℕ :=
  2*boundedPieceOrderMajorant (M*2) h (4*bankRerouteMajorant M)+40*bankRerouteMajorant M*M+1
def bankCopiesMajorant (M P : ℕ) : ℕ := 2*bankCatalogSizeMajorant M*P
def atomCoreOrderMajorant (M : ℕ) : ℕ := 2*(routeOrderMajorant (M*2)+(3*(M*2)+1))
def quadraticRateMajorant (M E B : ℕ) : ℕ := M*M*(32*(E*B+1))
def quadraticOrderMajorant (M E B : ℕ) : ℕ := max 1 (max (4*M) (max (2*M) (2*(B*E)*M)))
def nativeBankRateMajorant (M h P : ℕ) : ℕ :=
  quadraticRateMajorant (max (bankToleranceBound M h) (bankDeletionBound M h))
    (bankCellSizeMajorant M h) (bankCopiesMajorant M P)
def nativeBankOrderMajorant (M h P : ℕ) : ℕ :=
  max (catalogCompressionOrderMajorant M) (max (bankCellOrderMajorant M h)
    (max (atomCoreOrderMajorant M)
      (quadraticOrderMajorant (max (bankToleranceBound M h) (bankDeletionBound M h))
        (bankCellSizeMajorant M h) (bankCopiesMajorant M P))))
def preparedBankInputMajorant (M h : ℕ) : ℕ := max M (coreDeltaBound M h)
def preparedBankRateMajorant (M h P : ℕ) : ℕ := nativeBankRateMajorant (preparedBankInputMajorant M h) h P
def preparedBankOrderMajorant (M h P : ℕ) : ℕ :=
  max (nativeBankOrderMajorant (preparedBankInputMajorant M h) h P)
    (atomCoreOrderMajorant (preparedBankInputMajorant M h))

theorem preparedBankRateMajorant_mono_P (M h : ℕ) {P P' : ℕ} (hP : P ≤ P') :
    preparedBankRateMajorant M h P ≤ preparedBankRateMajorant M h P' := by
  unfold preparedBankRateMajorant nativeBankRateMajorant quadraticRateMajorant bankCopiesMajorant
  gcongr

theorem preparedBankOrderMajorant_mono_P (M h : ℕ) {P P' : ℕ} (hP : P ≤ P') :
    preparedBankOrderMajorant M h P ≤ preparedBankOrderMajorant M h P' := by
  unfold preparedBankOrderMajorant nativeBankOrderMajorant quadraticOrderMajorant bankCopiesMajorant
  gcongr

theorem boundedPieceSize_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) (k : ℕ) :
    CatalogNative.Explicit.boundedPieceSize α h k ≤ boundedPieceSizeMajorant M h k :=
  supplySize_le h k (uniformCertCost_le_majorant hα hh)

theorem boundedPieceOrder_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) (k : ℕ) :
    CatalogNative.Explicit.boundedPieceOrder α h k ≤ boundedPieceOrderMajorant M h k :=
  max_le_max (compressionOrder_le_majorant hα hh)
    (supplyOrder_le hα h k (uniformCertCost_le_majorant hα hh))

theorem boundedPieceSizeMajorant_mono_size (M h : ℕ) {k K : ℕ} (hk : k ≤ K) :
    boundedPieceSizeMajorant M h k ≤ boundedPieceSizeMajorant M h K := by
  unfold boundedPieceSizeMajorant supplySizeBound
  gcongr

theorem boundedPieceOrderMajorant_mono_size (M h : ℕ) {k K : ℕ} (hk : k ≤ K) :
    boundedPieceOrderMajorant M h k ≤ boundedPieceOrderMajorant M h K := by
  unfold boundedPieceOrderMajorant supplyOrderBound deletionOrderBound deletionNumerator supplySupportBound
  gcongr

private theorem ceil_nat_scale_div_le {M U U' : ℕ} {β : ℝ}
    (hβ : Magnitude M β) (hU : U ≤ U') (k : ℕ) :
    ⌈(k:ℝ)*U/β⌉₊ ≤ k*U'*M := by
  have hUr : (U:ℝ) ≤ U' := by exact_mod_cast hU
  have hnum : (k:ℝ)*U ≤ k*U' := mul_le_mul_of_nonneg_left hUr (Nat.cast_nonneg k)
  have hr : (k:ℝ)*U/β ≤ (k*U'*M:ℕ) := by
    calc (k:ℝ)*U/β = ((k:ℝ)*U)*(1/β) := by ring
      _ ≤ ((k:ℝ)*U')*M := mul_le_mul hnum hβ.inv_upper
        (one_div_nonneg.mpr hβ.pos.le) (mul_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg U'))
      _ = (k*U'*M:ℕ) := by push_cast; rfl
  exact Nat.ceil_le.mpr hr

theorem bankCellSize_le_majorant {M h : ℕ} {α β : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hh : h ≤ M) :
    CatalogNative.Explicit.bankCellSize α β h ≤ bankCellSizeMajorant M h := by
  have hU := (bankCatalog_bounds hα hβ hh).2.2
  have hs := boundedPieceSize_le_majorant (half_magnitude hα) (by omega : h ≤ M*2)
    (4*S07V42.Explicit.rerouteSize β
      (CatalogNative.Explicit.catalogDimension β h) (CatalogNative.Explicit.catalogCoefficient β h)
      (CatalogNative.Explicit.catalogColumn β h) (CatalogNative.Explicit.catalogDimension (α/2) h)
      (CatalogNative.Explicit.catalogCoefficient (α/2) h) (CatalogNative.Explicit.catalogColumn (α/2) h))
  exact Nat.add_le_add (hs.trans (boundedPieceSizeMajorant_mono_size _ _ (Nat.mul_le_mul_left 4 hU)))
    (Nat.mul_le_mul_left 4 hU)

theorem bankCellOrder_le_majorant {M h : ℕ} {α β : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hh : h ≤ M) :
    CatalogNative.Explicit.bankCellOrder α β h ≤ bankCellOrderMajorant M h := by
  let U := S07V42.Explicit.rerouteSize β
    (CatalogNative.Explicit.catalogDimension β h) (CatalogNative.Explicit.catalogCoefficient β h)
    (CatalogNative.Explicit.catalogColumn β h) (CatalogNative.Explicit.catalogDimension (α/2) h)
    (CatalogNative.Explicit.catalogCoefficient (α/2) h) (CatalogNative.Explicit.catalogColumn (α/2) h)
  have hU : U ≤ bankRerouteMajorant M := (bankCatalog_bounds hα hβ hh).2.2
  have hs := (boundedPieceOrder_le_majorant (half_magnitude hα) (by omega : h ≤ M*2) (4*U)).trans
    (boundedPieceOrderMajorant_mono_size _ _ (Nat.mul_le_mul_left 4 hU))
  have hc : ⌈40*(U:ℝ)/β⌉₊ ≤ 40*bankRerouteMajorant M*M := ceil_nat_scale_div_le hβ hU 40
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 2 hs) hc) 1

theorem bankCopies_le_majorant {M h : ℕ} {α β : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hh : h ≤ M) (P : ℕ) :
    CatalogNative.Explicit.bankCopies α β h P ≤ bankCopiesMajorant M P :=
  Nat.mul_le_mul_right P (Nat.mul_le_mul_left 2 (bankCatalog_bounds hα hβ hh).2.1)

theorem atomCoreOrder_le_majorant {M h : ℕ} {β : ℝ}
    (hβ : Magnitude M β) (hh : h ≤ M) : S07V42.coreN0 β h ≤ atomCoreOrderMajorant M := by
  have hr := routeOrder_le_majorant (half_magnitude hβ) (by omega : h ≤ M*2)
  have hn : S07V25.n1Of (β/2) ≤ 3*(M*2)+1 := by
    have h3 := Magnitude.natCast (by decide : 1 ≤ (3:ℕ)) (le_refl 3)
    exact Nat.add_le_add_right (h3.div (half_magnitude hβ)).ceil_le 1
  exact Nat.mul_le_mul_left 2 (Nat.add_le_add hr hn)

theorem quadraticRate_magnitude {M E B E' B' : ℕ} {ε δ : ℝ}
    (hε : Magnitude M ε) (hδ : Magnitude M δ) (hE : E ≤ E') (hB : B ≤ B') :
    Magnitude (quadraticRateMajorant M E' B') (CatalogNative.Explicit.quadraticBankRate ε δ E B) := by
  have hden : 32*(E*B+1) ≤ 32*(E'*B'+1) := by gcongr
  have h := (hε.mul hδ).div (Magnitude.natCast (by omega : 1 ≤ 32*(E*B+1)) hden)
  simpa only [quadraticRateMajorant, CatalogNative.Explicit.quadraticBankRate,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using h

theorem quadraticOrder_le_majorant {M E B E' B' : ℕ} {ε δ : ℝ}
    (hε : Magnitude M ε) (hδ : Magnitude M δ) (hE : E ≤ E') (hB : B ≤ B') :
    CatalogNative.Explicit.quadraticBankOrder ε δ E B ≤ quadraticOrderMajorant M E' B' := by
  have h4 := (Magnitude.natCast (by decide : 1 ≤ (4:ℕ)) (le_refl 4)).div hε
  have h2 := (Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) (le_refl 2)).div hδ
  have hc : ⌈2*(B*E:ℕ)/ε⌉₊ ≤ 2*(B'*E')*M :=
    ceil_nat_scale_div_le hε (Nat.mul_le_mul hB hE) 2
  exact max_le_max le_rfl (max_le_max h4.ceil_le (max_le_max h2.ceil_le hc))

theorem nativeBankRate_magnitude {M h : ℕ} {α β ε δ : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hε : Magnitude M ε) (hδ : Magnitude M δ)
    (hh : h ≤ M) (P : ℕ) :
    Magnitude (nativeBankRateMajorant M h P) (CatalogNative.Explicit.bankRoundRate α β ε δ h P) :=
  quadraticRate_magnitude ((bankTolerance_magnitude hα hβ hε h).mono (le_max_left _ _))
    ((bankDeletion_magnitude hα hβ hδ h).mono (le_max_right _ _))
    (bankCellSize_le_majorant hα hβ hh) (bankCopies_le_majorant hα hβ hh P)

theorem nativeBankOrder_le_majorant {M h : ℕ} {α β ε δ : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hε : Magnitude M ε) (hδ : Magnitude M δ)
    (hh : h ≤ M) (P : ℕ) :
    CatalogNative.Explicit.bankOrder α β ε δ h P ≤ nativeBankOrderMajorant M h P :=
  max_le_max (catalogCompressionOrder_le_majorant hα hβ hh)
    (max_le_max (bankCellOrder_le_majorant hα hβ hh) (max_le_max (atomCoreOrder_le_majorant hβ hh)
      (quadraticOrder_le_majorant ((bankTolerance_magnitude hα hβ hε h).mono (le_max_left _ _))
        ((bankDeletion_magnitude hα hβ hδ h).mono (le_max_right _ _))
        (bankCellSize_le_majorant hα hβ hh) (bankCopies_le_majorant hα hβ hh P))))

theorem preparedBankRate_magnitude {M h : ℕ} {α β ε δ : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hε : Magnitude M ε) (hδ : Magnitude M δ)
    (hh : h ≤ M) (P : ℕ) :
    Magnitude (preparedBankRateMajorant M h P) (Vortex.Explicit.preparedBankRoundRate α β ε δ h P) := by
  have hM : M ≤ preparedBankInputMajorant M h := le_max_left _ _
  exact nativeBankRate_magnitude (hα.mono hM) (hβ.mono hM) (hε.mono hM)
    (hδ.min (coreDelta_magnitude hβ h)) (hh.trans hM) P

theorem preparedBankOrder_le_majorant {M h : ℕ} {α β ε δ : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hε : Magnitude M ε) (hδ : Magnitude M δ)
    (hh : h ≤ M) (P : ℕ) :
    Vortex.Explicit.preparedBankOrder α β ε δ h P ≤ preparedBankOrderMajorant M h P := by
  have hM : M ≤ preparedBankInputMajorant M h := le_max_left _ _
  exact max_le_max (nativeBankOrder_le_majorant (hα.mono hM) (hβ.mono hM) (hε.mono hM)
    (hδ.min (coreDelta_magnitude hβ h)) (hh.trans hM) P)
    (atomCoreOrder_le_majorant (hβ.mono hM) (hh.trans hM))

#print axioms boundedPieceSize_le_majorant
#print axioms boundedPieceOrder_le_majorant
#print axioms preparedBankRateMajorant_mono_P
#print axioms preparedBankOrderMajorant_mono_P
#print axioms bankCellSize_le_majorant
#print axioms bankCellOrder_le_majorant
#print axioms atomCoreOrder_le_majorant
#print axioms nativeBankRate_magnitude
#print axioms nativeBankOrder_le_majorant
#print axioms preparedBankRate_magnitude
#print axioms preparedBankOrder_le_majorant
end TypedTriangle.TowerBounds
