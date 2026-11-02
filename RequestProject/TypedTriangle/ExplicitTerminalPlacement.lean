module
public import RequestProject.S07V31.TerminalAbsorber
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
universe u v w
namespace S07V28
open TypedTriangle.SparseEdge
theorem simultaneous_absorbers_explicit (k s : ℕ) {β : ℝ} (hβ : 0 < β) :
    let ε := plEps k s β
    let K := plK s β
    let n₀ := plN0 s β
    let q := plQ s β
    ∀ {V : Type u} [Fintype V] {I : Type v} {ι : Type w} [Fintype ι]
      (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
      (P : ι → Finset (Sym2 V)) (B : Finset (Sym2 V)) (r b : ℕ),
      n₀ ≤ Fintype.card V →
      (r : ℝ) ≤ ε * Fintype.card V → (b : ℝ) ≤ ε * Fintype.card V →
      (∀ i, (support (P i)).card ≤ k) → (∀ v, rootInc P v ≤ r) → (∀ v, degIn B v ≤ b) →
      (∀ i, P i ≠ ∅ → RobustAbsorberSupply G lab F (P i) s
        ⌊β * Fintype.card V⌋₊ ⌊β * Fintype.card V⌋₊) →
      ∃ A : ι → Finset (Sym2 V),
        (∀ i, P i = ∅ → A i = ∅) ∧
        (∀ i, IsAbsorber G lab F (P i) (A i)) ∧
        (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
        (∀ i, Disjoint (A i) B) ∧
        (∀ i j, Disjoint (A i) (P j)) ∧
        (∀ i, (A i).card ≤ s) ∧
        (∀ v, auxCount P A v ≤ q r) ∧
        (∀ v, degIn (univ.biUnion A) v ≤ K * (r + 1)) := by
  dsimp only
  intro V _ I ι _ G lab F P B r b hn hr hb hk hinc hB hsup
  obtain ⟨A, h1, h2, h3, h4, h5, h6, h7, h8⟩ := greedy_placement G lab F P B k r b s
      ⌊β * Fintype.card V⌋₊ ⌊β * Fintype.card V⌋₊ (plQ s β r) hk hinc hB hsup
      (plWindow_D k s r b _ hβ hn hr hb) (plWindow_sigma s r _ hβ)
  exact ⟨A, h1, h2, h3, h4, h5, h6, h7, fun v => (h8 v).trans (plQ_deg_le s r β)⟩

end S07V28
namespace S07V31
open TypedTriangle.SparseEdge S07V28
def terminalBudget (t s : ℕ) (β : ℝ) : ℝ := plEps t s β / 2
def terminalOrder (t s : ℕ) (β : ℝ) : ℕ :=
  plN0 s β + ⌈2 * ((2 : ℝ) ^ (t * t) + t) / plEps t s β⌉₊
theorem terminalBudget_pos (t s : ℕ) {β : ℝ} (hβ : 0 < β) :
    0 < terminalBudget t s β := half_pos (plEps_pos t s hβ)

theorem universal_terminal_absorber_explicit (t s : ℕ) {β : ℝ} (hβ : 0 < β) :
    let ε := terminalBudget t s β
    let n₀ := terminalOrder t s β
    ∀ {V : Type u} [Fintype V] {I : Type v}
      (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
      (U : Finset V) (B : Finset (Sym2 V)) (b : ℕ),
      n₀ ≤ Fintype.card V → U.card ≤ t →
      (∀ v, degIn B v ≤ b) → (b : ℝ) ≤ ε * Fintype.card V →
      TerminalSupply G lab F U s ⌊β * Fintype.card V⌋₊ ⌊β * Fintype.card V⌋₊ →
      ∃ R : Finset (Sym2 V),
        Disjoint R B ∧ Disjoint R (triEdges U) ∧
        R.card ≤ s * 2 ^ (t * t) ∧ (∀ v, degIn R v ≤ s * 2 ^ (t * t)) ∧
        (∃ D, IsDecomposition G lab F R D) ∧
        ∀ L : Finset (Sym2 V), ind L ∈ lattice G lab F → support L ⊆ U →
          ∃ D, IsDecomposition G lab F (R ∪ L) D := by
  dsimp only
  let ε' := plEps t s β
  have hε' := plEps_pos t s hβ
  intro V _ I G lab F U B b hn hU hB hb hsup
  set n := Fintype.card V with hndef
  change (b : ℝ) ≤ ε' / 2 * (n : ℝ) at hb
  let ι := {P // P ∈ physSubsets G lab F U}
  let P : ι → Finset (Sym2 V) := fun i => i.1
  have hcardι : Fintype.card ι ≤ 2 ^ (t * t) := by
    simp only [ι, Fintype.card_coe]
    exact card_physSubsets_le G lab F hU
  have hlarge : 2 * ((2 : ℝ) ^ (t * t) + t) ≤ ε' * n := by
    have h1 : 2 * ((2 : ℝ) ^ (t * t) + t) / ε' ≤ n := by
      have := Nat.le_ceil (2 * ((2 : ℝ) ^ (t * t) + t) / ε')
      have h2 : ((⌈2 * ((2 : ℝ) ^ (t * t) + t) / ε'⌉₊ : ℕ) : ℝ) ≤ n := by
        exact_mod_cast (Nat.le_add_left _ _).trans hn
      linarith
    rw [div_le_iff₀ hε'] at h1; linarith
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hpow0 : (0 : ℝ) ≤ (2 : ℝ) ^ (t * t) := by positivity
  have hr : ((2 ^ (t * t) : ℕ) : ℝ) ≤ ε' * n := by push_cast; linarith
  have hb' : ((b + t : ℕ) : ℝ) ≤ ε' * n := by push_cast; linarith
  have hk : ∀ i, (support (P i)).card ≤ t := fun i =>
    (card_le_card ((support_mono (mem_physSubsets.1 i.2).1).trans
      (support_triEdges_subset U))).trans hU
  have hinc : ∀ v, rootInc P v ≤ 2 ^ (t * t) := fun v =>
    (card_filter_le _ _).trans (by rw [card_univ]; exact hcardι)
  have hB' : ∀ v, degIn (B ∪ triEdges U) v ≤ b + t := fun v =>
    (degIn_union_le _ _ v).trans (Nat.add_le_add (hB v) ((degIn_triEdges_le U v).trans hU))
  have hsup' : ∀ i, P i ≠ ∅ → RobustAbsorberSupply G lab F (P i) s ⌊β * n⌋₊ ⌊β * n⌋₊ :=
    fun i hi => hsup i.1 i.2 hi
  obtain ⟨A, -, habs, hdisj, hAB, hAP, hcard, -, -⟩ :=
    simultaneous_absorbers_explicit t s hβ G lab F P (B ∪ triEdges U) (2 ^ (t * t)) (b + t)
      ((Nat.le_add_right _ _).trans hn) hr hb' hk hinc hB' hsup'
  have hRcard : (univ.biUnion A).card ≤ s * 2 ^ (t * t) := by
    refine card_biUnion_le.trans ((sum_le_card_nsmul _ _ s (fun i _ => hcard i)).trans ?_)
    rw [smul_eq_mul, card_univ, mul_comm]
    exact Nat.mul_le_mul_left s hcardι
  have hglue : ∀ L, L ∈ physSubsets G lab F U →
      ∃ D, IsDecomposition G lab F (univ.biUnion A ∪ L) D := fun L hL =>
    mode_gluing P A habs hdisj ⟨L, hL⟩ (fun j => hAP j ⟨L, hL⟩)
  refine ⟨univ.biUnion A, ?_, ?_, hRcard, fun v => (degIn_le_card _ v).trans hRcard, ?_, ?_⟩
  · exact (disjoint_biUnion_left _ _ _).2 fun i _ => (hAB i).mono_right subset_union_left
  · exact (disjoint_biUnion_left _ _ _).2 fun i _ => (hAB i).mono_right subset_union_right
  · simpa using hglue ∅ (empty_mem_physSubsets G lab F U)
  · intro L hL hLU
    exact hglue L (mem_physSubsets.2 ⟨subset_triEdges_of_physical hL hLU, hL⟩)
#print axioms universal_terminal_absorber_explicit
end S07V31
