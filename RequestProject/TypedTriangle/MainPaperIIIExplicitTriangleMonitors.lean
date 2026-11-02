module
public import RequestProject.TypedTriangle.ExplicitPaperIIITriangleThreshold
public import RequestProject.TypedTriangle.ExplicitTriangleMonitorConcreteOuterLayer
public import RequestProject.TypedTriangle.ExplicitConcreteLayers
public import RequestProject.TypedTriangle.ExplicitRawScalarCertificates
public import RequestProject.TypedTriangle.VortexPrescribedRawPathsAmbientAssembly
public import RequestProject.TypedTriangle.TriangleMonitorCompletionCount
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex.Explicit
open IntrinsicRawPathsPreparedVortex CorePaid ExplicitRaw

private theorem embedded_disjoint {X Y : Type} (ι : X ↪ Y)
    {E E' : Finset (Sym2 X)} (hDis : Disjoint E E') :
    Disjoint (embeddedEdges ι E) (embeddedEdges ι E') := by
  apply disjoint_left.mpr
  intro f hf hf'
  obtain ⟨e,he,hef⟩ := mem_image.mp hf
  obtain ⟨e',he',hef'⟩ := mem_image.mp hf'
  have hEq : e = e' := Sym2.map.injective ι.injective (hef.trans hef'.symm)
  exact disjoint_left.mp hDis he (hEq ▸ he')

/-- The original H1--H4 imply T at the specified finite threshold. Every
number in that threshold precedes the host, seed and tests and is given by a finite formula. -/
theorem main_theorem_T_with_triangle_monitors_at_explicit_order {I : Type} (F : Set (Multiset I))
    (αOriginal C η : ℝ) (hOriginal qStat : ℕ)
    (hαOriginal : 0 < αOriginal) (hC : 1 ≤ C) (hhOriginal : 6 ≤ hOriginal) (hη : 0 < η) :
    ∀ {X : Type} [Fintype X] (H : Host X I) (μ : Finset X → ℝ),
      paperIIITriangleThreshold αOriginal C η hOriginal qStat ≤ Fintype.card X →
      IsDiffuseSeed H F C μ →
      IsPhysical H F (edges H) → CommonNbrCond H F αOriginal →
      HingeCond H F αOriginal hOriginal →
      ∀ (ν : Type) [Fintype ν] (w : ν → Finset X → ℝ),
      (Fintype.card ν:ℝ) ≤ (Fintype.card X:ℝ)^qStat →
      (∀ k Q, IsAllowed H F Q → |w k Q| ≤ 1) →
      ∃ D : Finset (Finset X), IsDecomposition H F (edges H) D ∧
        ∀ k, |(∑ Q ∈ D, w k Q)-(∑ Q ∈ allowed H F, μ Q*w k Q)| ≤ η*(Fintype.card X:ℝ)^2 := by
  let ζStat := η/4
  have hζStat : 0 < ζStat := by dsimp [ζStat]; positivity
  let α := min αOriginal (S07V49.hingeConstB αOriginal 1 hOriginal)/8
  let h := 2*hOriginal-3
  have hHinge : 0 < S07V49.hingeConstB αOriginal 1 hOriginal :=
    S07V49.hingeConstB_pos hαOriginal (by norm_num) (by omega)
  have hα : 0 < α := by dsimp [α]; positivity
  have hh : 6 ≤ h := by dsimp [h]; omega
  have hCpos : 0 < C := by linarith only [hC]
  have h2C : 1 ≤ 2*C := by linarith only [hC]
  let ε := rawPreparationTolerance α C h
  let d := rawPreparationRank α h
  let T := rawPreparationTorsion α h
  let L := d+(d+1)*Nat.log 2 T
  let mInner := nativeInteriorCount (α/2) h
  let aInner := nativeDensity (α/2) h
  let mOuter := nativeInteriorCount (8*α) h
  let aOuter := nativeDensity (8*α) h
  let δOuter := nativeOuterAvoidBudget (8*α) h
  have hε : 0 < ε := by
    have hp := preparationTolerance_pos (by positivity : 0 < α/4) h
    exact lt_min hp (lt_min (by positivity) (by positivity))
  obtain ⟨hmInner,haInner,_,hOddInner,hLenInner⟩ := nativePathScalars_spec (α/2) h (by positivity)
  obtain ⟨hmOuter,haOuter,_,hOddOuter,hLenOuter⟩ := nativePathScalars_spec (8*α) h (by positivity)
  have hδOuter := nativeOuterAvoidBudget_pos (8*α) h (by positivity)
  let εBank := monitorComplementBudget (2*C) (α/16) h ζStat
  let γStock := resourceStockBudget (α/16) (2*C)
  let ηBank := CatalogNative.Explicit.bankProtectionBudget (α/16) (α/32) h
  have hεBank : 0 < εBank := monitorComplementBudget_pos h h2C (by positivity) hζStat
  have haStock : 0 < 1/(2*C) := by positivity
  have habStock : 1/(2*C) ≤ 2*C := by
    apply (div_le_iff₀ (by positivity : 0 < 2*C)).mpr
    nlinarith only [hC]
  have hγStock : 0 < γStock :=
    (BasalIncidence.Explicit.raw_stock_windows_pos (1/(2*C)) (2*C) (α/16) h
      haStock habStock (by positivity)).2.2
  have hηBank : 0 < ηBank := CatalogNative.Explicit.bankProtectionBudget_pos h (by positivity) (by positivity)
  let ρ := futureDensity (α/8) C h
  let qInner := globalInnerRate α aInner aOuter εBank γStock ηBank ρ h mInner mOuter
  let ζ := assemblyStateCap α C εBank γStock ηBank aInner aOuter h mInner mOuter
  let B := globalDebtCap α C ε δOuter aInner aOuter h mInner mOuter
  let β := assemblyRadius α C ε δOuter εBank γStock ηBank aInner aOuter h L mInner mOuter
  let Ninner := assemblyScheduleOrder α C ε δOuter εBank γStock ηBank aInner aOuter h L mInner mOuter
  obtain ⟨hρ,hqInner,hqInner32,hqBank,hqρ,hqη,hqStock,hqα,
    hqInnerPaths,hqOuterPaths,hζ,hζRoute,hζPool,hB,hB8,hBα,hBInnerPaths,hBOuterPaths,
    hBPreparation,hβ,hβCap,hTotal,_⟩ :=
    global_assembly_parameters_explicit F α C ε δOuter εBank γStock ηBank aInner aOuter
      h L mInner mOuter hα hC hh hε hδOuter hεBank hγStock hηBank haInner haOuter hmInner hmOuter
  let schedule := concreteInnerSchedule F (α/8) C ε ζ (2*B) h L
    (by positivity) hC hh hε hζ (by positivity)
  let Minner := innerLayerOrder α C qInner aInner h mInner L
    schedule.K schedule.εRef schedule.γRef schedule.nRef schedule.nPaid schedule.nGeometry
  let Mouter := max 1 (scheduledProfileOrder C schedule.K schedule.εRef L)
  let Mrequired := max Minner Mouter
  let M := rawMinimumOrder α qInner h Ninner Mrequired
  let t := rawTerminalOrder α C qInner h Ninner Mrequired
  have hMrequired : max Minner Mouter ≤ M := rawMinimumOrder_required α qInner h Ninner Mrequired
  have hPrepareCap := hTotal.trans hBPreparation
  have hPreparation : (∑ j ∈ range (L+1),β j) ≤ min δOuter ε :=
    le_min (hPrepareCap.trans (min_le_left _ _))
      (hPrepareCap.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hInnerBank : 4*qInner ≤ complementBudget (2*C) (α/16) h :=
    hqBank.trans (monitorComplementBudget_le_complement (2*C) (α/16) h ζStat)
  have hMakeLayers := concrete_inner_local_layers_explicit F α C h d T mInner aInner
    hα hC hh hmInner haInner hOddInner hLenInner
    ρ qInner ζ B hρ hqInner hqInner32 hInnerBank hqρ hqη hqStock hqα hqInnerPaths
    hζ hζRoute hζPool hB.le hB8 hBα hBInnerPaths β Ninner hβ hTotal schedule
  have hqOuterPaths' : qInner*mOuter*(2:ℝ)^mOuter ≤ (aOuter/2)/64 := by
    convert hqOuterPaths using 1 <;> ring
  have hBOuterPaths' : B*mOuter*(2:ℝ)^mOuter ≤ (aOuter/2)/64 := by
    convert hBOuterPaths using 1 <;> ring
  let tNat := ⌈t⌉₊
  let βFinite := fun r : Fin (L+1) => β r
  let qReserve := PreparedSupply.Explicit.uniformOuterRate (α/8) h tNat L βFinite
  have hqReserve : 0 < qReserve := PreparedSupply.Explicit.uniformOuterRate_pos (α/8) h tNat L βFinite
    (by positivity) (fun r => (hβCap r (Nat.le_of_lt_succ r.isLt)).1)
  have hqReserve32 : qReserve ≤ 1/32 := PreparedSupply.Explicit.uniformOuterRate_small (α/8) h tNat L βFinite
  let K := PreparedSupply.Explicit.reserveSize (α/8) h tNat
  let Nreserve := PreparedSupply.Explicit.absorberOrder (α/8) h
  let nAbs := PreparedSupply.Explicit.uniformReserveOrder (α/8) h tNat L βFinite
  let qOuter := min qReserve (εBank/4)
  have hqOuter : 0 < qOuter := lt_min hqReserve (by positivity)
  have hqOuter32 : qOuter ≤ 1/32 := (min_le_left _ _).trans hqReserve32
  have hqOuterBank : 4*qOuter ≤ εBank := by
    have hs : qOuter ≤ εBank/4 := min_le_right _ _
    linarith only [hs]
  let θT := outerLayerTerminalBudget α C qOuter aOuter h mOuter L schedule.γRef
  have hθT : 0 < θT := outerLayerTerminalBudget_pos α C qOuter aOuter h mOuter L schedule.γRef
    hα hC hqOuter haOuter schedule.γRef_pos
  let nOuter := monitorOuterLayerOrder α C qOuter aOuter ζStat h mOuter L qStat
    schedule.γRef schedule.nRef schedule.nPaid schedule.nGeometry
  have hMakeOuter {X : Type} [Fintype X] := concrete_outer_paid_layer_with_triangle_monitors_explicit F α C ζStat h d T mOuter qStat aOuter
    hα hC hh hmOuter haOuter hOddOuter hLenOuter hζStat
    ρ qInner ζ B hρ hqInner hqInner32 hqρ hqη hqStock hqα hqOuterPaths' hζ
    hB.le hB8 hBα hBOuterPaths' β Ninner hβ hTotal schedule
    qOuter hqOuter hqOuter32 hqOuterBank (X:=X)
  let Nouter := max Nreserve nAbs
  let nRaw := outerInnerRootOrder α C qInner qOuter h Ninner Mrequired Nouter
  have hMakeRaw {V : Type} [Fintype V] := outer_inner_raw_prepared_vortex_explicit F α C h hα ((by decide : 1 ≤ 6).trans hh) hCpos
    qInner hqInner hqInner32 β hβ hPreparation Ninner Mrequired qOuter hqOuter hqOuter32 Nouter (V:=V)
  have hReserve {V J : Type} [Fintype V] := PreparedSupply.Explicit.uniform_terminal_absorber_explicit
    (α/8) h tNat L βFinite (by positivity)
    (fun r => (hβCap r (Nat.le_of_lt_succ r.isLt)).1) (V:=V) (I:=J)
  let nClean := cleanHingeOrder αOriginal hOriginal
  let n₀ := max nClean (max nRaw (max nOuter ⌈(K:ℝ)/θT⌉₊))
  intro X _ H μ hn hSeed hH2 hH3 hH4 ν _ w hν hw
  change n₀ ≤ Fintype.card X at hn
  have hnClean : nClean ≤ Fintype.card X := (le_max_left _ _).trans hn
  have hnRaw : nRaw ≤ Fintype.card X :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hnOuter : nOuter ≤ Fintype.card X :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hn
  have hnReserve : ⌈(K:ℝ)/θT⌉₊ ≤ Fintype.card X :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hn
  have hOriginalDensity : 8*α ≤ αOriginal := by
    dsimp [α]
    linarith only [min_le_left αOriginal (S07V49.hingeConstB αOriginal 1 hOriginal)]
  have hHingeDensity : 8*α ≤ S07V49.hingeConstB αOriginal 1 hOriginal := by
    dsimp [α]
    linarith only [min_le_right αOriginal (S07V49.hingeConstB αOriginal 1 hOriginal)]
  have h3 : CommonNbrCond H F (8*α) := commonNbrCond_mono hH3 hOriginalDensity
  have hClean : CleanHingeCond H F (8*α) h :=
    (clean_hinge_of_H3H4_explicit αOriginal hOriginal hαOriginal hhOriginal H F hnClean hH3 hH4).mono hHingeDensity
  obtain ⟨node,hNode⟩ := hMakeRaw H hnRaw h3 hClean μ hSeed
  letI : DecidableEq (Survivors node.trim) := Classical.decEq _
  obtain ⟨W,hWmin,hShrink,hWlo,hWhi,hWrelativeLo,hWrelativeHi,hNext,hPools,hPaths,hRoutes,
    chain,hMetadata⟩ := hNode
  letI : DecidableEq (Survivors (univ \ W)) := Classical.decEq _
  let HAbs := restrictedHost H node.trim
  let ιOut := survivingVertexEmbedding node.trim
  let ιAbs := nextPreparedEmbedding W chain.head.trim
  let Uterminal := chain.terminalWindow.map ιAbs
  have hUcard : Uterminal.card ≤ tNat := by
    have hs : (Uterminal.card:ℝ) ≤ t := by
      dsimp only [Uterminal]
      rw [card_map,chain.card_terminalWindow]
      exact chain.terminalOrder_bounds.2
    exact_mod_cast hs.trans (Nat.le_ceil t)
  have hPrepared : Dispersal.PreparedCore HAbs.G HAbs.lab F (α/8) h Nouter (β node.index) := by
    simpa only [show (α/4)/2 = α/8 by ring] using node.prepared
  have hAbsOrder : Nouter ≤ Fintype.card (Survivors node.trim) := by
    have hEmpty := hPrepared.order ∅ (by
      simp only [card_empty,Nat.cast_zero]
      exact mul_nonneg (hβ node.index) (Nat.cast_nonneg _))
    have hSize : Fintype.card (Dispersal.Surv (∅ : Finset (Survivors node.trim))) ≤
        Fintype.card (Survivors node.trim) :=
      Fintype.card_le_of_injective (fun v => v.val) Subtype.val_injective
    simp only [← Nat.card_eq_fintype_card] at hEmpty hSize ⊢
    exact hEmpty.trans hSize
  have hPreparedReserve := preparedCore_lower_order HAbs F (α/8) (β node.index) h
    Nouter Nreserve hPrepared (le_max_left _ _)
  let r : Fin (L+1) := ⟨node.index,Nat.lt_succ_of_le node.index_le⟩
  obtain ⟨RAbs,hRAvoid,hRCard,hRDeg,hRBasal,hAbsorb⟩ :=
    hReserve HAbs F ((le_max_right _ _).trans hAbsOrder) r hPreparedReserve W Uterminal
      (hWhi.le.trans (by gcongr; exact min_le_left _ _)) hUcard
  let R := embeddedEdges ιOut RAbs
  have hRBasalOrig : Basal H F R :=
    basal_embedding HAbs H F ιOut (fun _ _ hv => hv) (fun _ => rfl) hRBasal
  obtain ⟨DR,hDR⟩ := hRBasalOrig
  have hRAvoidOrig : Disjoint R (triEdges (liftVertexSet node.trim W)) := by
    change Disjoint (embeddedEdges ιOut RAbs) (triEdges (W.map ιOut))
    rw [triEdges_embedding]
    exact embedded_disjoint ιOut hRAvoid
  have hRDegOrig : ∀v, SparseEdge.degIn R v ≤ K := by
    intro v
    calc
      SparseEdge.degIn R v ≤ R.card := Finset.card_filter_le _ _
      _ ≤ RAbs.card := Finset.card_image_le
      _ ≤ K := hRCard
  have hRCap : (K:ℝ) ≤ θT*Fintype.card X := by
    have hnCeil : (⌈(K:ℝ)/θT⌉₊:ℝ) ≤ Fintype.card X := by exact_mod_cast hnReserve
    have hs := (Nat.le_ceil ((K:ℝ)/θT)).trans hnCeil
    have hp := (div_le_iff₀ hθT).mp hs
    exact hp.trans_eq (mul_comm (Fintype.card X : ℝ) θT)
  obtain ⟨P₀,hData,state,Pouter,hPouter,hP₀Outer,hRestOuter,hOuterDisjoint,hReservedDisjoint,hOuterPartition⟩ :=
    hMakeOuter H μ hnOuter hSeed hH2 h3 hClean
      ((le_max_right _ _).trans hMrequired) node W hWrelativeLo hWrelativeHi hPools hPaths
      chain hMetadata R DR K (basal_subset_edges ⟨DR,hDR⟩) hDR hRAvoidOrig hRDegOrig hRCap ν w hν hw
  have hLayers := hMakeLayers M ((le_max_left _ _).trans hMrequired) chain hMetadata
  have hAdjAbs : ∀u v, state.host.G.Adj u v → HAbs.G.Adj (ιAbs u) (ιAbs v) := by
    intro u v huv
    exact state.graph_le huv
  have hLabAbs : ∀u, state.host.lab u = HAbs.lab (ιAbs u) := by
    intro u
    exact congrFun state.labels u
  have hAdjOrig : ∀u v, state.host.G.Adj u v → H.G.Adj (ιOut (ιAbs u)) (ιOut (ιAbs v)) :=
    fun u v huv => hAdjAbs u v huv
  have hLabOrig : ∀u, state.host.lab u = H.lab (ιOut (ιAbs u)) := hLabAbs
  obtain ⟨P,Lres,hP₀P,hRest,hDis,hPartition,hRL,hPhysical,hSupport,hLower,hUpper⟩ :=
    raw_paths_reserved_assembly_preserving_outer_cover chain (2*C) (α/16) ζ hLayers state
      H HAbs ιAbs ιOut hAdjOrig hLabOrig hAdjAbs hLabAbs Pouter RAbs
      (P₀.biUnion triEdges) hP₀Outer hRestOuter
      hOuterPartition hOuterDisjoint hReservedDisjoint
  have hSupportSet : support Lres ⊆ Uterminal := by
    intro v hv
    obtain ⟨_,e,he,hv⟩ := mem_filter.mp hv
    exact hSupport e he v hv
  have hAbsorbed : Basal HAbs F (RAbs ∪ Lres) := hAbsorb Lres hPhysical hSupportSet
  obtain ⟨hP₀,hSparse,hQuota⟩ := hData
  obtain ⟨D,hD,hP₀D⟩ := decomposition_of_reserved_absorption_preserving H HAbs F ιOut
    (fun _ _ huv => huv) (fun _ => rfl) P (P₀.biUnion triEdges) RAbs Lres P₀
      hP₀.isDecomposition hP₀P hRest hDis hPartition hAbsorbed
  refine ⟨D,hD,?_⟩
  intro k
  have hs := TriangleMonitors.completed_statistic_error hD hP₀D (2*ζStat) hSparse
    (w k) (hw k) (∑ Q ∈ allowed H F, μ Q*w k Q) (2*ζStat) (hQuota k)
  apply hs.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  dsimp only [ζStat]
  linarith only [hη]

#print axioms main_theorem_T_with_triangle_monitors_at_explicit_order
end TypedTriangle.Vortex.Explicit
