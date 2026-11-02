module
public import RequestProject.TypedTriangle.ExplicitNativeUniformCert
public import RequestProject.TypedTriangle.GroupingExplicitBound
public import RequestProject.TypedTriangle.VortexPreparedSmooth
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.NativeSmooth.Explicit
open Incidence RoutingConstants ComponentRows ActiveCover Grouping Dispersal S10V22
open ExplicitSample ExplicitCertificate

def sampleSize (α : ℝ) (h : ℕ) : ℕ := compressionSampleSize (α / 2) h
def sampleD (α : ℝ) (h : ℕ) : ℕ := compD0 (min (α / 2) 1) (sampleSize α h)
def sampleDimension (α : ℝ) (h : ℕ) : ℕ := (sampleSize α h + 1) ^ 2
def groupingRadius (α : ℝ) (h : ℕ) : ℕ := 3 * sampleD α h
def groupingToken (α : ℝ) (h : ℕ) : ℕ := sampleD α h * (3 * routeD (α / 2))
def certificateDemand (α : ℝ) (h : ℕ) : ℕ :=
  3 * routeD (α / 2) * explicitGroupBound (sampleDimension α h) (groupingToken α h) (groupingRadius α h)
def certificateCost (α : ℝ) (h : ℕ) : ℕ :=
  uniformCertCost (α / 4) h * certificateDemand α h
def preparedOrder (α : ℝ) (h : ℕ) : ℕ := compressionOrder (α / 4) h
def congestionOrder (α : ℝ) (h : ℕ) : ℕ :=
  max (preparedOrder α h) (max (compressionOrder (α / 2) h) (routeN0 (α / 2) h))
def congestionCost (α β : ℝ) (h : ℕ) : ℝ :=
  certificateCost α h * (4 * routeD (α / 2) + 3 +
    32 * routeD (α / 2) / routeδ (α / 2) h + 12 * certificateCost α h / β +
    2 * routeD (α / 2) + 2) + 1
def inverseCost (α β : ℝ) (h : ℕ) : ℝ := coeff α h (congestionCost α β h)
def inverseOrder (α : ℝ) (h : ℕ) : ℕ :=
  max (congestionOrder α h) ⌈S10V23.Proc.nZero α h⌉₊

theorem congestionCost_pos {α β : ℝ} (h : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    0 < congestionCost α β h := by
  have hδ : 0 < routeδ (α / 2) h := routeδ_pos (by positivity) h
  unfold congestionCost
  positivity

/-- Specified compression, certificate cost and grouping majorant on the
    same prepared host; no existential numerical parameter is consumed. -/
theorem congestion_on_prepared_host_explicit (α β : ℝ) (h : ℕ)
    (hα : 0 < α) (hβ : 0 < β)
    {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (hn : congestionOrder α h ≤ Fintype.card V)
    (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (Pc : Dispersal.PreparedCore H.G H.lab F (α / 4) h (preparedOrder α h) β)
    (x : Sym2 V → ℤ) (hx : x ∈ lattice H F) :
    ∃ cert : Finset V → ℤ, Dispersal.IsCert H.G H.lab F cert x ∧
      (Dispersal.l1T cert : ℝ) ≤ congestionCost α β h * ActiveCover.norm1 H.G x ∧
      ∀ v, (Dispersal.vload cert v : ℝ) ≤ congestionCost α β h *
        (ActiveCover.dabs H.G x v + ActiveCover.norm1 H.G x / Fintype.card V + 1) := by
  let γ : ℝ := α / 2
  let D := routeD γ
  let δ := routeδ γ h
  let d := sampleDimension α h
  let R := groupingRadius α h
  let B := groupingToken α h
  let K := certificateCost α h
  have hU : Dispersal.UniformCertOn.{0} F (α / 4) h (preparedOrder α h)
      (3 * D * groupBound d B R) K := by
    intro W _ G lab h3 h4 horder y hy hk
    apply native_uniformCertOn_of_H3H4_explicit (α / 4) h (certificateDemand α h)
      (by positivity) F W G lab h3 h4 horder y hy
    have hcap : 3 * D * groupBound d B R ≤ certificateDemand α h :=
      Nat.mul_le_mul_left (3 * D) (groupBound_le_explicit d B R)
    exact hk.trans (by exact_mod_cast hcap)
  have hnCmp : compressionOrder γ h ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnRoute : routeN0 γ h ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  obtain ⟨cmp⟩ := compression_of_H3H4_explicit γ h (by positivity) H F hnCmp
    (commonNbrCond_mono hH3 (by dsimp [γ]; linarith))
    (hingeCond_mono hH4 (by dsimp [γ]; linarith))
  obtain ⟨coord, emb, hrec, hbox, hcoord⟩ := native_compression_coordinates H F cmp (3 * D)
  have hlow : ∀ j : Row V, IsActiveRow H.G H.lab F j → γ * Fintype.card V ≤ j.2.card := by
    rintro ⟨a, J⟩ hJ
    exact active_component_card_ge (commonNbrCond_mono hH3 (by dsimp [γ]; linarith)) hJ
  have hdel : ∀ Z : Finset V, (Z.card : ℝ) ≤ δ * Fintype.card V → DeletionHyp H.G H.lab F Z := by
    intro Z hZ
    exact routing_deletion_of_H3H4 (by dsimp [γ]; positivity)
      (commonNbrCond_mono hH3 (by dsimp [γ]; linarith))
      (hingeCond_mono hH4 (by dsimp [γ]; linarith)) hnRoute Z hZ
  obtain ⟨cert, hc, hnrm, hload⟩ := Composition.prepared_core_composed_certificate_uniform δ d R B
    hU Pc hβ (routeδ_pos (by dsimp [γ]; positivity) h) (compConst_mul_routeδ_le γ h)
    (lt_of_lt_of_le (routeN0_pos γ h) hnRoute)
    (ComponentCount.hrows_of_lower H.G H.lab F (by dsimp [γ]; positivity) hlow)
    (ComponentCount.hdeg_of_lower H.G H.lab F (by dsimp [γ]; positivity) hlow)
    hdel (one_le_routeD γ) (routeD_spec γ) (triBd H F) (triBd_mem_lattice H F)
    (cmp.C₀.comp (nativeLocalProfile H F)) (cmp.P.comp (nativeLocalProfile H F))
    (native_compression_decomp H F cmp) coord emb hrec hbox hcoord x hx
  have hKL : (K : ℝ) * (4 * D + 3 + 32 * D / δ + 12 * K / β + 2 * D + 2) ≤
      congestionCost α β h := by dsimp [congestionCost, K, D, δ, γ]; linarith
  refine ⟨cert, hc, hnrm.trans ?_, fun v => (hload v).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hKL
      (by exact_mod_cast Composition.norm1_nonneg (G := H.G) x)
  · apply mul_le_mul_of_nonneg_right hKL
    have hd : (0 : ℝ) ≤ ActiveCover.dabs H.G x v := by
      exact_mod_cast Composition.dabs_nonneg (G := H.G) x v
    have hx0 : (0 : ℝ) ≤ ActiveCover.norm1 H.G x := by
      exact_mod_cast Composition.norm1_nonneg (G := H.G) x
    positivity

theorem inverseCost_pos {α β : ℝ} (h : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    0 < inverseCost α β h := coeff_pos h hα (congestionCost_pos h hα hβ).le

theorem smooth_on_prepared_host_explicit (α β : ℝ) (h : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hh : 6 ≤ h)
    {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (hn : inverseOrder α h ≤ Fintype.card V)
    (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (Pc : Dispersal.PreparedCore H.G H.lab F (α / 4) h (preparedOrder α h) β) :
    Smooth H F (inverseCost α β h) := by
  let L := congestionCost α β h
  have hL : 0 < L := congestionCost_pos h hα hβ
  have hnNative : congestionOrder α h ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnKernel : ⌈S10V23.Proc.nZero α h⌉₊ ≤ Fintype.card V := (le_max_right _ _).trans hn
  have hnK : S10V23.Proc.nZero α h ≤ (Fintype.card V : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnKernel)
  letI : DecidableEq V := Classical.decEq V
  have hp : IntCertProvider (triMat (allowedTri H.G H.lab F))
      (triTw (allowedTri H.G H.lab F)) edgeEw L (Fintype.card V : ℝ) :=
    NativeReal.provider_of_native (V := V) (I := I) (G := H.G) (lab := H.lab) (F := F) (K := L)
      (congestion_on_prepared_host_explicit α β h hα hβ H F hnNative hH3 hH4 Pc)
  intro x hx xmax hxmax0 hxmax
  obtain ⟨w, hw, hb⟩ := S10V23.smooth_inverse_H3H4 hH3 hH4 hα hh hnK hL.le hp hx hxmax
  exact supported_certificate H F (div_nonneg
    (mul_nonneg (inverseCost_pos h hα hβ).le hxmax0) (Nat.cast_nonneg _)) w hw hb

theorem exact_seed_on_prepared_child_explicit (α β C : ℝ) (h : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hh : 6 ≤ h) (hC : 1 ≤ C)
    {V I : Type} [Fintype V] (J : Host V I) (F : Set (Multiset I))
    (hn : inverseOrder α h ≤ Fintype.card V)
    (h3 : CommonNbrCond J F α) (h4 : HingeCond J F α h)
    (Pc : Dispersal.PreparedCore J.G J.lab F (α / 4) h (preparedOrder α h) β)
    (hPhys : IsPhysical J F (edges J)) (μ : Finset V → ℝ) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (hμsupp : ∀ T, μ T ≠ 0 → IsAllowed J F T)
    (hμ : ∀ T, IsAllowed J F T →
      (1 / (2 * C)) / Fintype.card V ≤ μ T ∧ μ T ≤ (2 * C) / Fintype.card V)
    (hload : ∀ e ∈ edges J, |bdry J F μ e - 1| ≤ ξ)
    (hbudget : inverseCost α β h * ξ ≤ 1 / (4 * C)) :
    ∃ ψ : Finset V → ℝ, IsDiffuseSeed J F (4 * C) ψ := by
  exact Vortex.exact_seed_on_fixed_host_of_smooth J F C (inverseCost α β h) ξ
    hC hξ (smooth_on_prepared_host_explicit α β h hα hβ hh
      J F hn h3 h4 Pc) hPhys μ hμsupp hμ hload hbudget

#print axioms congestion_on_prepared_host_explicit
#print axioms smooth_on_prepared_host_explicit
#print axioms exact_seed_on_prepared_child_explicit
end TypedTriangle.NativeSmooth.Explicit
