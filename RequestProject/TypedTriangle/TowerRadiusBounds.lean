module
public import RequestProject.TypedTriangle.TowerMagnitude
public import RequestProject.TypedTriangle.ExplicitGlobalRadiusSchedule
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TypedTriangle.TowerBounds
open Vortex.Explicit

def radiusNextCap (K : ℕ) : ℕ := max (K*2) (K*(16*K*(K+1)))*2
def radiusInputCap (K : ℕ) : ℕ := K+radiusNextCap K+1
def radiusMajorant (F : ℕ → ℕ) (M : ℕ) : ℕ → ℕ
  | 0 => M+F M
  | r+1 => let U := radiusInputCap (radiusMajorant F M r); U+F U

theorem radiusMajorant_base_le (F : ℕ → ℕ) (M r : ℕ) : M ≤ radiusMajorant F M r := by
  induction r with
  | zero => exact Nat.le_add_right _ _
  | succ r ih =>
      change M ≤ radiusInputCap (radiusMajorant F M r)+F _
      unfold radiusInputCap
      omega

theorem radiusMajorant_mono (F : ℕ → ℕ) (M : ℕ) {r s : ℕ} (hrs : r ≤ s) :
    radiusMajorant F M r ≤ radiusMajorant F M s := by
  induction s, hrs using Nat.le_induction with
  | base => exact le_rfl
  | succ s hrs ih =>
      change _ ≤ radiusInputCap (radiusMajorant F M s)+F _
      unfold radiusInputCap
      omega

theorem radiusState_magnitudes {F : ℕ → ℕ} {M L : ℕ} {ε : ℝ → ℝ} {b top : ℝ}
    (hb : Magnitude M b) (htop : Magnitude M top) (hL : L ≤ M)
    (hε : ∀ K, M ≤ K → ∀ x, Magnitude K x → Magnitude (F K) (ε x)) (r : ℕ) :
    Magnitude (radiusMajorant F M r) (radiusState ε b L top r).1 ∧
    Magnitude (radiusMajorant F M r) (radiusState ε b L top r).2 := by
  induction r with
  | zero =>
      exact ⟨htop.mono (Nat.le_add_right _ _),
        (hε M le_rfl top htop).mono (Nat.le_add_left _ _)⟩
  | succ r ih =>
      let K := radiusMajorant F M r
      let U := radiusInputCap K
      have hMK : M ≤ K := radiusMajorant_base_le F M r
      have hKU : K ≤ U := by dsimp [U,radiusInputCap]; omega
      have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
      have h16 : Magnitude 16 (16:ℝ) := Magnitude.natCast (by decide) le_rfl
      have hL1 : Magnitude (K+1) (L+1:ℝ) := by
        simpa only [Nat.cast_add,Nat.cast_one] using
          Magnitude.natCast (by omega : 1 ≤ L+1) (by omega : L+1 ≤ K+1)
      have hden : Magnitude (16*K*(K+1)) (16*b*(L+1)) :=
        (h16.mul (hb.mono hMK)).mul hL1
      have hn : Magnitude (radiusNextCap K)
          (min ((radiusState ε b L top r).1/2)
            ((radiusState ε b L top r).2/(16*b*(L+1)))/2) :=
        ((ih.1.div h2).min (ih.2.div hden)).div h2
      have hnU := hn.mono (by dsimp [U,radiusInputCap]; omega : radiusNextCap K ≤ U)
      have he := hε U (hMK.trans hKU) _ hnU
      change Magnitude (U+F U) _ ∧ Magnitude (U+F U) _
      exact ⟨hnU.mono (Nat.le_add_right _ _),
        (ih.2.min he).mono (by omega : max K (F U) ≤ U+F U)⟩

theorem radiusSequence_magnitude {F : ℕ → ℕ} {M L R : ℕ} {ε : ℝ → ℝ} {b top : ℝ}
    (hb : Magnitude M b) (htop : Magnitude M top) (hL : L ≤ M) (hLR : L ≤ R)
    (hε : ∀ K, M ≤ K → ∀ x, Magnitude K x → Magnitude (F K) (ε x)) (j : ℕ) :
    Magnitude (radiusMajorant F M R) (radiusSequence ε b L top j) := by
  exact ((radiusState_magnitudes hb htop hL hε (L-j)).1).mono
    (radiusMajorant_mono F M (Nat.sub_le _ _ |>.trans hLR))

#print axioms radiusState_magnitudes
#print axioms radiusSequence_magnitude
end TypedTriangle.TowerBounds
