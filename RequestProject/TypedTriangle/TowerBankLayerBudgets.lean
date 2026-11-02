module
public import RequestProject.TypedTriangle.TowerBankResources
public import RequestProject.TypedTriangle.TowerBankBudgets
public import RequestProject.TypedTriangle.ExplicitConcreteLayerParameters
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.TowerBounds
open Vortex Vortex.Explicit

def layerTerminalInputMajorant (M : ℕ) : ℕ := M+2*M+2*bankProtectionBound M M+1
def layerTerminalMajorant (M : ℕ) : ℕ :=
  max (resourceTerminalMajorant (layerTerminalInputMajorant M)) ((M+1)*M*64)
def windowRouteMajorant (M : ℕ) : ℕ := M*M*(32*(M+1)*4^M)
def outerLayerParameterScale (M : ℕ) : ℕ :=
  M+M*16+2*M+M*32+M*4+windowRouteMajorant (2*M)*4+(M+1)+1
def outerLayerTerminalMajorant (M : ℕ) : ℕ := layerTerminalMajorant (outerLayerParameterScale M)

theorem bankProtectionBound_mono_h {M h H : ℕ} (hh : h ≤ H) :
    bankProtectionBound M h ≤ bankProtectionBound M H := by
  have hc := Nat.choose_le_choose 2 hh
  unfold bankProtectionBound cellDegreeBudgetBound supplyBudgetBound
  gcongr

theorem layerTerminal_magnitude {M h t : ℕ} {α C β γ q αPool εRoute : ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hβ : Magnitude M β)
    (hγ : Magnitude M γ) (hq : Magnitude M q) (hPool : Magnitude M αPool)
    (hRoute : Magnitude M εRoute) (hh : h ≤ M) (ht : t ≤ M) :
    Magnitude (layerTerminalMajorant M) (layerTerminalBudget α C β γ q αPool εRoute h t) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h64 : Magnitude 64 (64:ℝ) := Magnitude.natCast (by decide) le_rfl
  let U := layerTerminalInputMajorant M
  have hu : M ≤ U := by dsimp [U,layerTerminalInputMajorant]; omega
  have hBank : Magnitude (bankProtectionBound M M) (CatalogNative.Explicit.bankProtectionBudget α β h) :=
    (bankProtection_magnitude hα hβ h).mono (bankProtectionBound_mono_h hh)
  have hη : Magnitude U (CatalogNative.Explicit.bankProtectionBudget α β h/2) :=
    (hBank.div h2).mono (by dsimp [U,layerTerminalInputMajorant]; omega)
  have hq2 : Magnitude U (q/2) := (hq.div h2).mono (by dsimp [U,layerTerminalInputMajorant]; omega)
  exact (resourceTerminal_magnitude (hα.mono hu) (hC.mono hu) (hPool.mono hu) hq2
    (hRoute.mono hu) hη (hh.trans hu) (ht.trans hu)).min
    (((clipped_magnitude hγ).mul hq).div h64)

theorem windowRoute_magnitude {M m : ℕ} {a q : ℝ}
    (ha : Magnitude M a) (hq : Magnitude M q) (hm : m ≤ M) :
    Magnitude (windowRouteMajorant M) (windowRouteRate a q m) := by
  have h32 : Magnitude 32 (32:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hn : Magnitude (M+1) ((m+1:ℕ):ℝ) := Magnitude.natCast (by omega) (by omega)
  have hp : Magnitude (4^M) ((4:ℝ)^m) := (h4.pow m).mono (Nat.pow_le_pow_right (by decide) hm)
  simpa only [windowRouteRate,windowRouteMajorant,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using
    (ha.mul hq).div ((h32.mul hn).mul hp)

private theorem finite_inf_magnitude {ι : Type} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (M : ℕ) (hf : ∀ i ∈ s, Magnitude M (f i)) :
    Magnitude M (s.inf' hs f) := by
  obtain ⟨i,hi,heq⟩ := Finset.exists_mem_eq_inf' hs f
  simpa only [heq] using hf i hi

theorem outerLayerTerminal_magnitude {M h m L : ℕ} {α C q a : ℝ} {γRef : ℕ → ℝ}
    (hα : Magnitude M α) (hC : Magnitude M C) (hq : Magnitude M q) (ha : Magnitude M a)
    (hγ : ∀ j ≤ L, Magnitude M (γRef j)) (hh : h ≤ M) (hm : m ≤ M) :
    Magnitude (outerLayerTerminalMajorant M) (outerLayerTerminalBudget α C q a h m L γRef) := by
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h16 : Magnitude 16 (16:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h32 : Magnitude 32 (32:ℝ) := Magnitude.natCast (by decide) le_rfl
  let U := outerLayerParameterScale M
  have hu : M ≤ U := by dsimp [U,outerLayerParameterScale]; omega
  have ha2 : Magnitude (2*M) (a/2) := by simpa only [Nat.mul_comm] using ha.div h2
  have hroute := (windowRoute_magnitude ha2 (hq.mono (by omega : M ≤ 2*M)) (by omega : m ≤ 2*M)).div h4
  apply finite_inf_magnitude
  intro j _
  exact layerTerminal_magnitude
    ((hα.div h16).mono (by dsimp [U,outerLayerParameterScale]; omega))
    ((h2.mul hC).mono (by dsimp [U,outerLayerParameterScale]; omega))
    ((hα.div h32).mono (by dsimp [U,outerLayerParameterScale]; omega))
    ((hγ j (Nat.le_of_lt_succ j.isLt)).mono hu) (hq.mono hu)
    ((hα.div h4).mono (by dsimp [U,outerLayerParameterScale]; omega))
    (hroute.mono (by dsimp [U,outerLayerParameterScale]; omega))
    (hh.trans hu) (by dsimp [U,outerLayerParameterScale]; omega)

#print axioms layerTerminal_magnitude
#print axioms outerLayerTerminal_magnitude
end TypedTriangle.TowerBounds
