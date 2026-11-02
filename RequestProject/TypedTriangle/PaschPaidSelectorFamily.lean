module
public import RequestProject.TypedTriangle.VortexWithdrawalCoreIncidence
public import RequestProject.TypedTriangle.PaschSelectorUniverse
@[expose] public section
open Finset Classical
noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CorePaid
open CorePayment PreparedSupply SelSimul SelBridge SelTyped S07V26
variable {V I : Type*} [Fintype V]

/-- The actual paid-selector constructor retaining its simultaneous-family witness.
The input hypotheses are identical to the original constructor. -/
theorem selector_paid_layer_host_with_family {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {t : ℕ} (ht : Odd t) (ht3 : 3 ≤ t)
    {ε α : ℝ} (hε : 0 < ε) {W : Finset V}
    (hroute : S07V27.RouteProp G lab F t ε W)
    (X B0 : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B0.Adj]
    (Z : Finset V) (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v')
    (hZW : Disjoint Z W) (hXG : X ≤ G)
    (hH2 : IsPhysical (⟨G,lab⟩ : Host V I) F (edges (⟨G,lab⟩ : Host V I)))
    (hCore : CommonNbrCond (restrictedHost (⟨G,lab⟩ : Host V I) Z) F α)
    {A q r b p : ℕ} (hA : 200*(t-1)+8 ≤ A) (hq : 0 < q) (hp : 0 < p)
    (hX : ∀ v, X.degree v ≤ r) (hB : ∀ v, B0.degree v ≤ b)
    (hBud : r+b+A*r*Fintype.card V/q+(A+1)*r+10*r+(t-1)*(200*r) ≤ ⌊ε*Fintype.card V⌋₊)
    (hρ : ((b+61*r+60*q+60:ℕ):ℝ) ≤ ε*Fintype.card V)
    (hPay : ((Fintype.card V*(61*r+60*q)/p +
      2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) <
        α*Fintype.card (Survivors Z)) :
    ∃ (σ : V → LocalSel V) (C : Finset (Sym2 V)),
      SimulFamily G lab F X B0 Z (S07V27.rootAdm G lab F X) A q σ ∧
      Disjoint (fuelU Z σ ∪ C) (X.edgeFinset ∪ B0.edgeFinset) ∧
      Basal (⟨G,lab⟩ : Host V I) F (fuelU Z σ ∪ C) ∧
      Basal (⟨G,lab⟩ : Host V I) F (SelSimul.residual X Z σ ∅ ∪ C) ∧
      (∀ e ∈ fuelU Z σ ∪ C, ∃ v ∈ e, v ∉ Z) ∧
      (∀ v, edeg (fuelU Z σ ∪ C) v ≤ max (A*r) (60*r+61*q)+2*(61*r+60*q+p)) ∧
      ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset → IsPhysical (⟨G,lab⟩ : Host V I) F L →
        (fuelU Z σ ∪ C) ∪ L = packEdges (packing X Z σ L) ∪ (SelSimul.residual X Z σ L ∪ C) ∧
        Disjoint (packEdges (packing X Z σ L)) (SelSimul.residual X Z σ L ∪ C) ∧
        Basal (⟨G,lab⟩ : Host V I) F (packEdges (packing X Z σ L)) ∧
        (∀ f ∈ SelSimul.residual X Z σ L ∪ C, ∀ v ∈ f, v ∉ Z) ∧
        (∀ v, edeg (SelSimul.residual X Z σ L ∪ C) v ≤ 3*(61*r+60*q)+2*p) ∧
        IsPhysical (⟨G,lab⟩ : Host V I) F (SelSimul.residual X Z σ L ∪ C) := by
  have hcov : S07V26.EdgeCovered G lab F := S07V26.H2Phys.edgeCovered hH2
  have hlink : ∀ v ∈ Z, ∀ u, X.Adj v u → ∃ y, (ComponentRows.link G lab F v).Adj u y :=
    fun v _ u hu => S07V27.link_of_edgeCovered hcov hXG hu
  have hAvail : ∀ v ∈ Z, S07V27.CoreAvail G lab F v (X.neighborFinset v)
      (S07V27.rootAdm G lab F X v) A (r+b+A*r*Fintype.card V/q) (b+61*r+60*q) W := by
    intro v hv
    exact S07V27.coreAvail_root ht ht3 hε hroute X v (hlink v hv) hA (hX v) hBud hρ
  obtain ⟨σ,hFam,hAux⟩ := S07V27.schedule_core G lab F X B0 Z W hZW
    (S07V27.rootAdm G lab F X) hAvail hq hX hB le_rfl le_rfl
  have hAdm0 : ∀ v ∈ Z, S07V27.rootAdm G lab F X v ∅ :=
    fun v _ => S07V27.rootAdm_empty G lab F X v
  have hadm0 : ∀ v ∈ Z, S07V27.rootAdm G lab F X v (demand X ∅ v) := by
    simpa [SelSimul.demand] using hAdm0
  have hKd := (hFam.layer_partition hZ hX (empty_subset _) hadm0).2.2.2.2.2.2
  have hKcard := card_le_order_mul_degree (SelSimul.residual X Z σ ∅) hKd
  have hPay' : (((SelSimul.residual X Z σ ∅).card/p +
      2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) <
        α*Fintype.card (Survivors Z) := by
    have hn := Nat.add_le_add_right (Nat.div_le_div_right (c := p) hKcard)
      (2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p))
    have hR : (((SelSimul.residual X Z σ ∅).card/p +
        2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) ≤
        ((Fintype.card V*(61*r+60*q)/p +
        2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) := by exact_mod_cast hn
    exact hR.trans_lt hPay
  obtain ⟨C,hC,hAvoid,hBas,hEmp,hCZ,hCd,hModes⟩ := paid_core_family hFam hCore hp hZ hX hB hAdm0 hPay'
  have hIncidence : ∀ e ∈ fuelU Z σ ∪ C, ∃ v ∈ e, v ∉ Z := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact fuelU_meets_complement Z σ (hFam.outside_Z hZ) e he
    · induction e using Sym2.ind with
      | _ u v => exact ⟨u, by simp, hCZ _ he u (by simp)⟩
  refine ⟨σ,C,hFam,hAvoid,hBas,hEmp,hIncidence,?_,?_⟩
  · intro v
    exact (edeg_union_le _ _ v).trans
      (Nat.add_le_add (hFam.fuelU_edeg_le hZ hX v) (hCd v))
  · intro L hL hphys
    obtain ⟨heq,hd,hP,hYZ,hYd,hYP⟩ := hModes L hL
      (fun v _ => SelectorEntry.rootAdm_of_physical X hL hphys v)
    exact ⟨heq,hd,hP,hYZ,hYd,hYP hphys⟩

end TypedTriangle.CorePaid

#print axioms TypedTriangle.CorePaid.selector_paid_layer_host_with_family
