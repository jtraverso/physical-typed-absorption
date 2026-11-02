module
public import RequestProject.TypedTriangle.TowerGeometryPreparation
public import RequestProject.TypedTriangle.ExplicitBankCore
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.TowerBounds

def catalogDimensionMajorant (M : ℕ) : ℕ := (compressionSampleMajorant M+1)^2
def catalogCoefficientMajorant (M : ℕ) : ℕ :=
  compDMajorant (compressionClipMajorant M) (compressionSampleMajorant M)
def catalogColumnMajorant (M : ℕ) : ℕ := 3*catalogCoefficientMajorant M
def atomRadiusMajorant (M : ℕ) : ℕ := 3*routeDMajorant (M*2)
def bankCatalogInputMajorant (M : ℕ) : ℕ :=
  atomRadiusMajorant M+catalogDimensionMajorant M+catalogCoefficientMajorant M+
    catalogColumnMajorant M+catalogDimensionMajorant (M*2)+
    catalogCoefficientMajorant (M*2)+catalogColumnMajorant (M*2)
def bankRadiusMajorant (M : ℕ) : ℕ := natEnvelope 5 (bankCatalogInputMajorant M)
def bankCatalogSizeMajorant (M : ℕ) : ℕ := natEnvelope 8 (bankCatalogInputMajorant M)
def bankRerouteMajorant (M : ℕ) : ℕ := natEnvelope 9 (bankCatalogInputMajorant M)
def catalogCompressionOrderMajorant (M : ℕ) : ℕ :=
  max (compressionOrderMajorant M) (2*compressionOrderMajorant (M*2))

theorem half_magnitude {M : ℕ} {α : ℝ} (hα : Magnitude M α) :
    Magnitude (M*2) (α/2) :=
  hα.div (Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) le_rfl)

theorem catalogDimension_le_majorant {M h : ℕ} {β : ℝ}
    (hβ : Magnitude M β) (hh : h ≤ M) :
    CatalogNative.Explicit.catalogDimension β h ≤ catalogDimensionMajorant M :=
  Nat.pow_le_pow_left (Nat.add_le_add_right (compressionSampleSize_le_majorant hβ hh) 1) 2

theorem catalogCoefficient_le_majorant {M h : ℕ} {β : ℝ}
    (hβ : Magnitude M β) (hh : h ≤ M) :
    CatalogNative.Explicit.catalogCoefficient β h ≤ catalogCoefficientMajorant M :=
  compD_le_majorant (clipped_magnitude hβ) (compressionSampleSize_le_majorant hβ hh)

theorem catalogColumn_le_majorant {M h : ℕ} {β : ℝ}
    (hβ : Magnitude M β) (hh : h ≤ M) :
    CatalogNative.Explicit.catalogColumn β h ≤ catalogColumnMajorant M :=
  Nat.mul_le_mul_left 3 (catalogCoefficient_le_majorant hβ hh)

theorem atomRadius_le_majorant {M : ℕ} {β : ℝ} (hβ : Magnitude M β) :
    S07V42.atomR β ≤ atomRadiusMajorant M :=
  Nat.mul_le_mul_left 3 (routeD_le_majorant (half_magnitude hβ))

theorem bankCatalog_bounds {M h : ℕ} {α β : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hh : h ≤ M) :
    CatalogNative.Explicit.bankCatalogRadius α β h ≤ bankRadiusMajorant M ∧
    CatalogNative.Explicit.bankCatalogSize α β h ≤ bankCatalogSizeMajorant M ∧
    S07V42.Explicit.rerouteSize β
      (CatalogNative.Explicit.catalogDimension β h)
      (CatalogNative.Explicit.catalogCoefficient β h)
      (CatalogNative.Explicit.catalogColumn β h)
      (CatalogNative.Explicit.catalogDimension (α/2) h)
      (CatalogNative.Explicit.catalogCoefficient (α/2) h)
      (CatalogNative.Explicit.catalogColumn (α/2) h) ≤ bankRerouteMajorant M := by
  have hh' : h ≤ M*2 := by omega
  have ha := atomRadius_le_majorant hβ
  have hd := catalogDimension_le_majorant hβ hh
  have hc := catalogCoefficient_le_majorant hβ hh
  have hE := catalogColumn_le_majorant hβ hh
  have hd' := catalogDimension_le_majorant (half_magnitude hα) hh'
  have hc' := catalogCoefficient_le_majorant (half_magnitude hα) hh'
  have hE' := catalogColumn_le_majorant (half_magnitude hα) hh'
  have h0 := le_natEnvelope 0 (bankCatalogInputMajorant M)
  have ha0 := ha.trans (show atomRadiusMajorant M ≤ bankCatalogInputMajorant M by unfold bankCatalogInputMajorant; omega)
  have hd0 := hd.trans (show catalogDimensionMajorant M ≤ bankCatalogInputMajorant M by unfold bankCatalogInputMajorant; omega)
  have hc0 := hc.trans (show catalogCoefficientMajorant M ≤ bankCatalogInputMajorant M by unfold bankCatalogInputMajorant; omega)
  have hE0 := hE.trans (show catalogColumnMajorant M ≤ bankCatalogInputMajorant M by unfold bankCatalogInputMajorant; omega)
  have hd0' := hd'.trans (show catalogDimensionMajorant (M*2) ≤ bankCatalogInputMajorant M by unfold bankCatalogInputMajorant; omega)
  have hc0' := hc'.trans (show catalogCoefficientMajorant (M*2) ≤ bankCatalogInputMajorant M by unfold bankCatalogInputMajorant; omega)
  have hE0' := hE'.trans (show catalogColumnMajorant (M*2) ≤ bankCatalogInputMajorant M by unfold bankCatalogInputMajorant; omega)
  obtain ⟨_,hr,hu,hs⟩ := catalogue_le_envelope (ha0.trans h0) (hd0.trans h0)
    (hc0.trans h0) (hE0.trans h0) (hd0'.trans h0) (hc0'.trans h0) (hE0'.trans h0)
  exact ⟨hr,hs,hu⟩

theorem catalogCompressionOrder_le_majorant {M h : ℕ} {α β : ℝ}
    (hα : Magnitude M α) (hβ : Magnitude M β) (hh : h ≤ M) :
    CatalogNative.Explicit.catalogCompressionOrder α β h ≤ catalogCompressionOrderMajorant M :=
  max_le_max (compressionOrder_le_majorant hβ hh)
    (Nat.mul_le_mul_left 2 (compressionOrder_le_majorant (half_magnitude hα) (by omega)))

#print axioms catalogDimension_le_majorant
#print axioms catalogCoefficient_le_majorant
#print axioms catalogColumn_le_majorant
#print axioms atomRadius_le_majorant
#print axioms bankCatalog_bounds
#print axioms catalogCompressionOrder_le_majorant
end TypedTriangle.TowerBounds
