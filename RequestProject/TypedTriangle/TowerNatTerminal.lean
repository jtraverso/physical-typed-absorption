module
public import RequestProject.TypedTriangle.TowerMagnitude
public import RequestProject.TypedTriangle.ExplicitUniformTerminalReserve
@[expose] public section
open Finset
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.TowerBounds

def placementDenBound (M k s : ℕ) : ℕ := 2*(1+k+s+2*s*s*(M+1))
def placementOrderBound (M s : ℕ) : ℕ := 2*s*M+1
def terminalBudgetBound (M t s : ℕ) : ℕ := 2*(M*placementDenBound M t s)
def terminalOrderBound (M t s : ℕ) : ℕ :=
  placementOrderBound M s+2*(2^(t*t)+t)*(M*placementDenBound M t s)

theorem placementM_le {M : ℕ} {β : ℝ} (hβ : Magnitude M β) : S07V28.plM β ≤ M+1 :=
  Nat.add_le_add_right hβ.inv.ceil_le 1

theorem placementK_le {M : ℕ} {β : ℝ} (hβ : Magnitude M β) (s : ℕ) :
    S07V28.plK s β ≤ s*(1+2*s*(M+1))+1 := by
  unfold S07V28.plK
  gcongr
  exact placementM_le hβ

theorem placementQ_le {M : ℕ} {β : ℝ} (hβ : Magnitude M β) (s r : ℕ) :
    S07V28.plQ s β r ≤ 2*s*(M+1)*r+1 := by
  unfold S07V28.plQ
  gcongr
  exact placementM_le hβ

theorem placementEps_magnitude {M : ℕ} {β : ℝ} (hβ : Magnitude M β)
    (k s S : ℕ) (hs : s ≤ S) :
    Magnitude (M*placementDenBound M k S) (S07V28.plEps k s β) := by
  let den : ℕ := 2*(1+k+s+2*s*s*S07V28.plM β)
  have hden : 1 ≤ den := by
    have hp : 0 < den := by dsimp [den]; positivity
    omega
  have hbound : den ≤ placementDenBound M k S := by
    dsimp [den, placementDenBound]
    gcongr
    exact placementM_le hβ
  have hn := Magnitude.natCast hden hbound
  simpa [S07V28.plEps, den] using hβ.div hn

theorem placementOrder_le {M : ℕ} {β : ℝ} (hβ : Magnitude M β)
    (s S : ℕ) (hs : s ≤ S) : S07V28.plN0 s β ≤ placementOrderBound M S := by
  have hsR : (s:ℝ) ≤ S := by exact_mod_cast hs
  have hu : 2*(s:ℝ)/β ≤ ((2*S*M:ℕ):ℝ) := by
    calc
      2*(s:ℝ)/β = (2*(s:ℝ))*(1/β) := by ring
      _ ≤ (2*(S:ℝ))*(M:ℝ) := mul_le_mul
        (mul_le_mul_of_nonneg_left hsR (by norm_num)) hβ.inv_upper
        (div_nonneg (by norm_num) hβ.pos.le) (by positivity)
      _ = ((2*S*M:ℕ):ℝ) := by push_cast; ring
  exact Nat.add_le_add_right (Nat.ceil_le.mpr hu) 1

theorem terminalBudget_magnitude {M : ℕ} {β : ℝ} (hβ : Magnitude M β)
    (t s S : ℕ) (hs : s ≤ S) :
    Magnitude (terminalBudgetBound M t S) (S07V31.terminalBudget t s β) := by
  have h := (placementEps_magnitude hβ t s S hs).div
    (Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) (le_refl 2))
  simpa only [terminalBudgetBound, S07V31.terminalBudget, Nat.cast_ofNat, Nat.mul_comm] using h

theorem terminalOrder_le {M : ℕ} {β : ℝ} (hβ : Magnitude M β)
    (t s S : ℕ) (hs : s ≤ S) :
    S07V31.terminalOrder t s β ≤ terminalOrderBound M t S := by
  let N : ℕ := 2*(2^(t*t)+t)
  have hN : 1 ≤ N := by
    have hp : 0 < N := by dsimp [N]; positivity
    omega
  have hn := (Magnitude.natCast hN (le_refl N)).div (placementEps_magnitude hβ t s S hs)
  have hc : ⌈2*((2:ℝ)^(t*t)+t)/S07V28.plEps t s β⌉₊ ≤ N*(M*placementDenBound M t S) := by
    simpa only [N, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using hn.ceil_le
  exact Nat.add_le_add (placementOrder_le hβ s S hs) hc

def supplyBudgetBound (M h : ℕ) : ℕ := max (max M 2) (M*(40*2^(h.choose 2)))
def deletionNumerator (U h : ℕ) : ℕ := 8*((U+3)+(U+1+h)*2^(h.choose 2))
def deletionOrderBound (M U h N : ℕ) : ℕ := deletionNumerator U h*M+1+2*N

theorem supplyBudget_magnitude {M : ℕ} {α β : ℝ} (hα : Magnitude M α) (hβ : Magnitude M β)
    (h : ℕ) : Magnitude (supplyBudgetBound M h) (PreparedSupply.Explicit.supplyBudget α β h) := by
  have htwo := Magnitude.natCast (by decide : 1 ≤ (2:ℕ)) (le_refl 2)
  have hhalf := Magnitude.one.div htwo
  have hforty := Magnitude.natCast (by decide : 1 ≤ (40:ℕ)) (le_refl 40)
  have hr := hα.div (hforty.mul (htwo.pow (h.choose 2)))
  have hmin := (hβ.min hhalf).min hr
  simpa only [supplyBudgetBound, PreparedSupply.Explicit.supplyBudget, S07V30.delta, S07V30.capC,
    Nat.cast_ofNat] using hmin

theorem deletionOrder_le {M : ℕ} {α : ℝ} (hα : Magnitude M α)
    (U U' h N : ℕ) (hU : U ≤ U') :
    S07V30.n0 α U h N ≤ deletionOrderBound M U' h N := by
  have hn : 1 ≤ deletionNumerator U h := by
    have hp : 0 < deletionNumerator U h := by unfold deletionNumerator; positivity
    omega
  have hbound : deletionNumerator U h ≤ deletionNumerator U' h := by
    unfold deletionNumerator
    gcongr
  have hnum := (Magnitude.natCast hn hbound).div hα
  have hc : ⌈8*((U:ℝ)+3+((U:ℝ)+1+h)*(2:ℝ)^(h.choose 2))/α⌉₊ ≤ deletionNumerator U' h*M := by
    simpa only [deletionNumerator, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hnum.ceil_le
  exact Nat.add_le_add_right (Nat.add_le_add_right hc 1) (2*N)

def supplySizeBound (K h k : ℕ) : ℕ := K*k*(4*(2*h-2).choose 2+6)
def supplySupportBound (K h k : ℕ) : ℕ :=
  2*k+3*(K*k)+K*k*(2*h-2)+3*(K*k)*(2*h-3)
def supplyOrderBound (M K h k : ℕ) : ℕ := deletionOrderBound M (supplySupportBound K h k) h 0

theorem supplySize_le {α : ℝ} {K : ℕ} (h k : ℕ)
    (hK : PreparedSupply.Explicit.absorberCost α h ≤ K) :
    PreparedSupply.Explicit.supplySize α h k ≤ supplySizeBound K h k := by
  unfold PreparedSupply.Explicit.supplySize supplySizeBound
  gcongr

theorem supplySupport_le {α : ℝ} {K : ℕ} (h k : ℕ)
    (hK : PreparedSupply.Explicit.absorberCost α h ≤ K) :
    PreparedSupply.Explicit.supplySupport α h k ≤ supplySupportBound K h k := by
  unfold PreparedSupply.Explicit.supplySupport supplySupportBound
  dsimp only
  gcongr

theorem supplyOrder_le {M K : ℕ} {α : ℝ} (hα : Magnitude M α) (h k : ℕ)
    (hK : PreparedSupply.Explicit.absorberCost α h ≤ K) :
    PreparedSupply.Explicit.supplyOrder α h k ≤ supplyOrderBound M K h k :=
  deletionOrder_le hα _ _ h 0 (supplySupport_le h k hK)

def reserveSizeBound (K h t : ℕ) : ℕ := supplySizeBound K h (t*t)*2^(t*t)
def reserveBudgetBound (M K h t : ℕ) : ℕ :=
  terminalBudgetBound (supplyBudgetBound M h) t (supplySizeBound K h (t*t))
def reserveOrderBound (M K h t : ℕ) : ℕ :=
  max (supplyOrderBound M K h (t*t))
    (terminalOrderBound (supplyBudgetBound M h) t (supplySizeBound K h (t*t)))
def reserveRateBound (M K h t : ℕ) : ℕ := max 64 (reserveBudgetBound M K h t*4)

theorem reserveSize_le {α : ℝ} {K : ℕ} (h t : ℕ)
    (hK : PreparedSupply.Explicit.absorberCost α h ≤ K) :
    PreparedSupply.Explicit.reserveSize α h t ≤ reserveSizeBound K h t :=
  Nat.mul_le_mul_right _ (supplySize_le h (t*t) hK)

theorem reserveBudget_magnitude {M K : ℕ} {α β : ℝ} (hα : Magnitude M α) (hβ : Magnitude M β)
    (h t : ℕ) (hK : PreparedSupply.Explicit.absorberCost α h ≤ K) :
    Magnitude (reserveBudgetBound M K h t) (PreparedSupply.Explicit.reserveBudget α β h t) :=
  terminalBudget_magnitude (supplyBudget_magnitude hα hβ h) t _ _ (supplySize_le h (t*t) hK)

theorem reserveOrder_le {M K : ℕ} {α β : ℝ} (hα : Magnitude M α) (hβ : Magnitude M β)
    (h t : ℕ) (hK : PreparedSupply.Explicit.absorberCost α h ≤ K) :
    PreparedSupply.Explicit.reserveOrder α β h t ≤ reserveOrderBound M K h t :=
  max_le_max (supplyOrder_le hα h (t*t) hK)
    (terminalOrder_le (supplyBudget_magnitude hα hβ h) t _ _ (supplySize_le h (t*t) hK))

theorem reserveRate_magnitude {M K : ℕ} {α β : ℝ} (hα : Magnitude M α) (hβ : Magnitude M β)
    (h t : ℕ) (hK : PreparedSupply.Explicit.absorberCost α h ≤ K) :
    Magnitude (reserveRateBound M K h t) (PreparedSupply.Explicit.outerRate α β h t) := by
  have h64 := Magnitude.natCast (by decide : 1 ≤ (64:ℕ)) (le_refl 64)
  have h4 := Magnitude.natCast (by decide : 1 ≤ (4:ℕ)) (le_refl 4)
  have hr := (reserveBudget_magnitude hα hβ h t hK).div h4
  simpa only [PreparedSupply.Explicit.outerRate, reserveRateBound, Nat.cast_ofNat] using h64.inv.min hr

private theorem finset_inf_magnitude {ι : Type} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (M : ℕ) (hf : ∀ i ∈ s, Magnitude M (f i)) :
    Magnitude M (s.inf' hs f) := by
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf' hs f
  simpa only [heq] using hf i hi

theorem uniformReserveRate_magnitude {M K : ℕ} {α : ℝ} (hα : Magnitude M α)
    (h t L : ℕ) (β : Fin (L+1) → ℝ) (hβ : ∀ r, Magnitude M (β r))
    (hK : PreparedSupply.Explicit.absorberCost α h ≤ K) :
    Magnitude (reserveRateBound M K h t) (PreparedSupply.Explicit.uniformOuterRate α h t L β) := by
  apply finset_inf_magnitude
  intro r _
  exact reserveRate_magnitude hα (hβ r) h t hK

theorem uniformReserveOrder_le {M K : ℕ} {α : ℝ} (hα : Magnitude M α)
    (h t L : ℕ) (β : Fin (L+1) → ℝ) (hβ : ∀ r, Magnitude M (β r))
    (hK : PreparedSupply.Explicit.absorberCost α h ≤ K) :
    PreparedSupply.Explicit.uniformReserveOrder α h t L β ≤ reserveOrderBound M K h t := by
  apply Finset.sup_le
  intro r _
  exact reserveOrder_le hα (hβ r) h t hK

#print axioms placementEps_magnitude
#print axioms placementOrder_le
#print axioms terminalBudget_magnitude
#print axioms terminalOrder_le
#print axioms supplyBudget_magnitude
#print axioms deletionOrder_le
#print axioms supplySize_le
#print axioms supplyOrder_le
#print axioms reserveBudget_magnitude
#print axioms reserveOrder_le
#print axioms uniformReserveRate_magnitude
#print axioms uniformReserveOrder_le
end TypedTriangle.TowerBounds
