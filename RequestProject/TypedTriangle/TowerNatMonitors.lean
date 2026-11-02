module
public import RequestProject.TypedTriangle.TowerNatAlgebra
public import RequestProject.TypedTriangle.ExplicitBankCore
public import RequestProject.TypedTriangle.ExplicitMonitorCore
public import RequestProject.TypedTriangle.ExplicitBoundedFunctionalExtension
public import RequestProject.TypedTriangle.ExplicitG1ZSplice
public import RequestProject.S07V46.Capacity
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.TowerBounds

theorem envelope_lift {x k l M : ℕ} (hx : x ≤ natEnvelope k M) (hkl : k ≤ l) :
    x ≤ natEnvelope l M := hx.trans (natEnvelope_mono_depth M hkl)

theorem one_le_envelope (k M : ℕ) : 1 ≤ natEnvelope k M :=
  (by decide : (1:ℕ) ≤ 2).trans (two_le_natEnvelope k M)

theorem add_le_envelope {a b k M : ℕ} (ha : a ≤ natEnvelope k M) (hb : b ≤ natEnvelope k M) :
    a+b ≤ natEnvelope (k+1) M := add_le_natStep ha hb

theorem mul_le_envelope {a b k M : ℕ} (ha : a ≤ natEnvelope k M) (hb : b ≤ natEnvelope k M) :
    a*b ≤ natEnvelope (k+1) M := mul_le_natStep ha hb

theorem pow_le_envelope {a b k M : ℕ} (ha : a ≤ natEnvelope k M) (hb : b ≤ natEnvelope k M) :
    a^b ≤ natEnvelope (k+1) M := pow_le_natStep ha hb

theorem factorial_le_envelope {a k M : ℕ} (ha : a ≤ natEnvelope k M) :
    a.factorial ≤ natEnvelope (k+1) M := factorial_le_natStep ha

theorem kernel_le_envelope {d R k M : ℕ} (hd : d ≤ natEnvelope k M) (hR : R ≤ natEnvelope k M) :
    GroupingExplicit.kernelBound d R ≤ natEnvelope (k+1) M := kernel_le_natStep hd hR

theorem solver_le_envelope {d K k M : ℕ} (hd : d ≤ natEnvelope k M) (hK : K ≤ natEnvelope k M) :
    S07V41.Explicit.solverBound d K ≤ natEnvelope (k+1) M := solver_le_natStep hd hK

theorem box_le_envelope {d R k M : ℕ} (hd : d ≤ natEnvelope k M) (hR : R ≤ natEnvelope k M) :
    (2*R+1)^d ≤ natEnvelope (k+3) M := by
  have h1 := mul_le_envelope (two_le_natEnvelope k M) hR
  have h2 := add_le_envelope h1 (one_le_envelope (k+1) M)
  exact pow_le_envelope h2 (envelope_lift hd (by omega))

theorem torsionRadius_mono {d D R S : ℕ} (hd : d ≤ D) (hR : R ≤ S) :
    QuotientBox.explicitTorsionRadius d R ≤ QuotientBox.explicitTorsionRadius D S := by
  have hbase : 2*R+1 ≤ 2*S+1 := by omega
  have hp : (2*R+1)^d ≤ (2*S+1)^D :=
    (Nat.pow_le_pow_left hbase d).trans (Nat.pow_le_pow_right (by omega) hd)
  exact Nat.mul_le_mul hR hp

theorem torsionBound_mono {d D R S : ℕ} (hd : d ≤ D) (hR : R ≤ S) :
    QuotientBox.explicitTorsionBound d R ≤ QuotientBox.explicitTorsionBound D S := by
  have hrad := torsionRadius_mono hd hR
  have hb : 2*QuotientBox.explicitTorsionRadius d R+1 ≤
      2*QuotientBox.explicitTorsionRadius D S+1 := by omega
  exact (Nat.pow_le_pow_left hb d).trans (Nat.pow_le_pow_right (by omega) hd)

theorem torsionBound_le_envelope {d R k M : ℕ}
    (hd : d ≤ natEnvelope k M) (hR : R ≤ natEnvelope k M) :
    QuotientBox.explicitTorsionBound d R ≤ natEnvelope (k+7) M := by
  have hb := box_le_envelope hd hR
  have hr := mul_le_envelope (envelope_lift hR (by omega : k ≤ k+3)) hb
  have h2 := mul_le_envelope (two_le_natEnvelope (k+4) M) hr
  have h1 := add_le_envelope h2 (one_le_envelope (k+5) M)
  exact pow_le_envelope h1 (envelope_lift hd (by omega))

theorem torsionBound_le_algebraBound {d R M : ℕ} (hd : d ≤ M) (hR : R ≤ M) :
    QuotientBox.explicitTorsionBound d R ≤ natAlgebraBound M :=
  (torsionBound_le_envelope (hd.trans (le_natEnvelope 0 M))
    (hR.trans (le_natEnvelope 0 M))).trans (natEnvelope_le_algebraBound (by decide))

theorem presentation_le_envelope {m d E k M : ℕ}
    (hm : m ≤ natEnvelope k M) (hd : d ≤ natEnvelope k M) (hE : E ≤ natEnvelope k M) :
    S07V37.Explicit.presLBound d E ≤ natEnvelope (k+1) M ∧
    S07V37.Explicit.presKBound m d E ≤ natEnvelope (k+4) M := by
  have hL := kernel_le_envelope hd hE
  refine ⟨hL, ?_⟩
  simpa only [S07V37.Explicit.presKBound, S07V37.Explicit.presLBound, Nat.add_assoc] using
    (box_le_envelope (envelope_lift hm (by omega : k ≤ k+1)) hL)

theorem relativeKernel_le_envelope {d d' cJ cG R E k M : ℕ}
    (hd : d ≤ natEnvelope k M) (hd' : d' ≤ natEnvelope k M)
    (hcJ : cJ ≤ natEnvelope k M) (hcG : cG ≤ natEnvelope k M)
    (hR : R ≤ natEnvelope k M) (hE : E ≤ natEnvelope k M) :
    S07V37.Explicit.relKBound d d' cJ cG R E ≤ natEnvelope (k+3) M ∧
    S07V37.Explicit.relNBound d d' cJ cG R E ≤ natEnvelope (k+7) M := by
  have hcGR := mul_le_envelope hcG hR
  have harg : max (cG*R) E ≤ natEnvelope (k+1) M :=
    max_le hcGR (envelope_lift hE (by omega))
  have hL := kernel_le_envelope (envelope_lift hd' (by omega : k ≤ k+1)) harg
  have hK := mul_le_envelope hL (envelope_lift hR (by omega : k ≤ k+2))
  refine ⟨hK, ?_⟩
  have hcJR := mul_le_envelope hcJ hR
  have hbox : (2*(cJ*R)+1)^d ≤ natEnvelope (k+4) M := by
    simpa only [Nat.add_assoc] using
      (box_le_envelope (envelope_lift hd (by omega : k ≤ k+1)) hcJR)
  have hp : (2*GroupingExplicit.kernelBound d' (max (cG*R) E)+1)^((2*(cJ*R)+1)^d) ≤
      natEnvelope (k+7) M := by
    simpa only [Nat.add_assoc] using
      (box_le_envelope hbox (envelope_lift hL (by omega : k+2 ≤ k+4)))
  classical
  simpa only [S07V37.Explicit.relNBound, S07V37.Explicit.presKBound,
    S07V37.Explicit.presLBound, Fintype.card_coe, QuotientBox.card_box] using hp

theorem representative_le_envelope {d R r k M : ℕ}
    (hd : d ≤ natEnvelope k M) (hR : R ≤ natEnvelope k M) (hr : r ≤ natEnvelope k M) :
    S07V42.Explicit.representativeBound d R r ≤ natEnvelope (k+4) M := by
  have hk := kernel_le_envelope hd (max_le (one_le_envelope k M) hR)
  have h1 := mul_le_envelope hk (envelope_lift hd (by omega : k ≤ k+1))
  have h2 := mul_le_envelope h1 (envelope_lift hR (by omega : k ≤ k+2))
  exact mul_le_envelope h2 (envelope_lift hr (by omega))

theorem catalogue_le_envelope {β : ℝ} {d c E d' c' E' k M : ℕ}
    (ha : S07V42.atomR β ≤ natEnvelope k M)
    (hd : d ≤ natEnvelope k M) (hc : c ≤ natEnvelope k M) (hE : E ≤ natEnvelope k M)
    (hd' : d' ≤ natEnvelope k M) (hc' : c' ≤ natEnvelope k M) (hE' : E' ≤ natEnvelope k M) :
    S07V42.Explicit.genKBound β d c d' c' E' ≤ natEnvelope (k+4) M ∧
    S07V42.Explicit.catRadius β d c E d' c' E' ≤ natEnvelope (k+5) M ∧
    S07V42.Explicit.rerouteSize β d c E d' c' E' ≤ natEnvelope (k+9) M ∧
    (2*S07V42.Explicit.catRadius β d c E d' c' E'+1)^d ≤ natEnvelope (k+8) M := by
  have hdd := add_le_envelope hd hd'
  have hg : S07V42.Explicit.genKBound β d c d' c' E' ≤ natEnvelope (k+4) M := by
    simpa only [S07V42.Explicit.genKBound, Nat.add_assoc] using
      (relativeKernel_le_envelope hdd (envelope_lift hd' (by omega : k ≤ k+1))
        (envelope_lift (max_le hc hc') (by omega : k ≤ k+1))
        (envelope_lift hc' (by omega : k ≤ k+1))
        (envelope_lift ha (by omega : k ≤ k+1))
        (envelope_lift hE' (by omega : k ≤ k+1))).1
  have hcg := mul_le_envelope (envelope_lift hc (by omega : k ≤ k+4)) hg
  have hrad : S07V42.Explicit.catRadius β d c E d' c' E' ≤ natEnvelope (k+5) M :=
    max_le (envelope_lift hE (by omega)) hcg
  have hrer : S07V42.Explicit.rerouteSize β d c E d' c' E' ≤ natEnvelope (k+9) M := by
    simpa only [S07V42.Explicit.rerouteSize, Nat.add_assoc] using
      (representative_le_envelope (envelope_lift hd (by omega : k ≤ k+5)) hrad
        (envelope_lift hg (by omega : k+4 ≤ k+5)))
  have hsize : (2*S07V42.Explicit.catRadius β d c E d' c' E'+1)^d ≤ natEnvelope (k+8) M := by
    simpa only [Nat.add_assoc] using (box_le_envelope (envelope_lift hd (by omega : k ≤ k+5)) hrad)
  exact ⟨hg, hrad, hrer, hsize⟩

theorem monitor_envelope_bounds {d R k M : ℕ}
    (hd : d ≤ natEnvelope k M) (hR : R ≤ natEnvelope k M) :
    S07V34.Explicit.boxSize d R ≤ natEnvelope (k+3) M ∧
    S07V34.Explicit.dualBound d R ≤ natEnvelope (k+4) M ∧
    S07V34.Explicit.monitorDimension d R ≤ natEnvelope (k+7) M ∧
    S07V34.Explicit.monitorMagnitude d R ≤ natEnvelope (k+9) M ∧
    S07V34.Explicit.relationBound d R ≤ natEnvelope (k+10) M ∧
    S07V34.Explicit.relationCount d R ≤ natEnvelope (k+13) M ∧
    S07V34.Explicit.paymentExponent d R ≤ natEnvelope (k+13) M ∧
    S07V34.Explicit.paymentCost d R ≤ natEnvelope (k+16) M := by
  have hb : S07V34.Explicit.boxSize d R ≤ natEnvelope (k+3) M := box_le_envelope hd hR
  have hdual : S07V34.Explicit.dualBound d R ≤ natEnvelope (k+4) M :=
    kernel_le_envelope hb (envelope_lift hR (by omega))
  have hdim : S07V34.Explicit.monitorDimension d R ≤ natEnvelope (k+7) M := by
    simpa only [S07V34.Explicit.monitorDimension, Nat.add_assoc] using
      (box_le_envelope (envelope_lift hd (by omega : k ≤ k+4)) hdual)
  have hp := mul_le_envelope hdim (envelope_lift hdual (by omega : k+4 ≤ k+7))
  have hp' := mul_le_envelope hp (envelope_lift hR (by omega : k ≤ k+8))
  have hmag : S07V34.Explicit.monitorMagnitude d R ≤ natEnvelope (k+9) M :=
    max_le (one_le_envelope (k+9) M) hp'
  have hrel : S07V34.Explicit.relationBound d R ≤ natEnvelope (k+10) M :=
    kernel_le_envelope (envelope_lift hdim (by omega)) hmag
  have hcount : S07V34.Explicit.relationCount d R ≤ natEnvelope (k+13) M := by
    simpa only [S07V34.Explicit.relationCount, S07V34.Explicit.boxSize, Nat.add_assoc] using
      (box_le_envelope (envelope_lift hb (by omega : k+3 ≤ k+10)) hrel)
  have hRrel := mul_le_envelope (envelope_lift hR (by omega : k ≤ k+10)) hrel
  have harg : max (R*S07V34.Explicit.relationBound d R) R ≤ natEnvelope (k+11) M :=
    max_le hRrel (envelope_lift hR (by omega))
  have hker := kernel_le_envelope (envelope_lift hd (by omega : k ≤ k+11)) harg
  have hexp : S07V34.Explicit.paymentExponent d R ≤ natEnvelope (k+13) M :=
    factorial_le_envelope hker
  have hc1 := mul_le_envelope hcount (envelope_lift hrel (by omega : k+10 ≤ k+13))
  have hc2 := mul_le_envelope hc1 (envelope_lift hexp (by omega : k+13 ≤ k+14))
  have hcost : S07V34.Explicit.paymentCost d R ≤ natEnvelope (k+16) M :=
    add_le_envelope (envelope_lift hrel (by omega)) hc2
  exact ⟨hb, hdual, hdim, hmag, hrel, hcount, hexp, hcost⟩

theorem monitorCost_le_algebraBound {d R M : ℕ} (hd : d ≤ M) (hR : R ≤ M) :
    S07V34.Explicit.paymentCost d R ≤ natAlgebraBound M :=
  (monitor_envelope_bounds (hd.trans (le_natEnvelope 0 M))
    (hR.trans (le_natEnvelope 0 M))).2.2.2.2.2.2.2.trans (natEnvelope_le_algebraBound (by decide))

theorem gammaL_le_envelope {A B L k M : ℕ}
    (hA : A ≤ natEnvelope k M) (hB : B ≤ natEnvelope k M) (hL : L ≤ natEnvelope k M) :
    S07V46.gammaL A B L ≤ natEnvelope (k+4) M := by
  have hp := mul_le_envelope hA hB
  have hs := add_le_envelope (one_le_envelope (k+1) M) hp
  have hpow := pow_le_envelope hs (envelope_lift hL (by omega : k ≤ k+2))
  have hLp := add_le_envelope hL (one_le_envelope k M)
  have hm := mul_le_envelope (envelope_lift hA (by omega : k ≤ k+1)) hLp
  exact mul_le_envelope (envelope_lift hm (by omega)) hpow

def natExtensionCost (d D E R : ℕ) : ℕ := d*natSolver d (D*R+E)*R*D

theorem natExtensionCost_mono {d d' D D' E E' R R' : ℕ}
    (hd : d ≤ d') (hD : D ≤ D') (hE : E ≤ E') (hR : R ≤ R') :
    natExtensionCost d D E R ≤ natExtensionCost d' D' E' R' := by
  have hs := natSolver_mono hd (Nat.add_le_add (Nat.mul_le_mul hD hR) hE)
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hd hs) hR) hD

theorem extensionCost_eq_nat (d D E R : ℕ) :
    S07V41.Explicit.extensionCost d D E R = (natExtensionCost d D E R : ℝ) := by
  unfold S07V41.Explicit.extensionCost S07V41.Explicit.solverCost natExtensionCost
  simp only [natSolver_eq, Nat.cast_mul]
  have h : ((D:ℤ)*R+E).toNat = D*R+E := by omega
  rw [h]

theorem extensionCost_le_envelope {d D E R k M : ℕ}
    (hd : d ≤ natEnvelope k M) (hD : D ≤ natEnvelope k M)
    (hE : E ≤ natEnvelope k M) (hR : R ≤ natEnvelope k M) :
    natExtensionCost d D E R ≤ natEnvelope (k+6) M := by
  have hp := mul_le_envelope hD hR
  have ha := add_le_envelope hp (envelope_lift hE (by omega : k ≤ k+1))
  have hs := solver_le_envelope (envelope_lift hd (by omega : k ≤ k+2)) ha
  rw [← natSolver_eq] at hs
  have h1 := mul_le_envelope (envelope_lift hd (by omega : k ≤ k+3)) hs
  have h2 := mul_le_envelope h1 (envelope_lift hR (by omega : k ≤ k+4))
  exact mul_le_envelope h2 (envelope_lift hD (by omega))

theorem compressionCertCost_le_envelope {s H D k M : ℕ}
    (hs : s ≤ natEnvelope k M) (hH : H ≤ natEnvelope k M) (hD : D ≤ natEnvelope k M) :
    ExplicitCertificate.compressionCertCost s H D ≤ natEnvelope (k+6) M := by
  have hs1 := add_le_envelope hs (one_le_envelope k M)
  have hdim := pow_le_envelope hs1 (two_le_natEnvelope (k+1) M)
  have h3D : 3*D ≤ natEnvelope (k+2) M := by
    convert add_le_envelope (envelope_lift hD (by omega : k ≤ k+1)) (add_le_envelope hD hD) using 1 <;> ring
  have hker := kernel_le_envelope hdim (max_le (one_le_envelope (k+2) M) h3D)
  have h3H : 3*H ≤ natEnvelope (k+2) M := by
    convert add_le_envelope (envelope_lift hH (by omega : k ≤ k+1)) (add_le_envelope hH hH) using 1 <;> ring
  have hcoef := add_le_envelope (one_le_envelope (k+2) M) h3H
  have hp := mul_le_envelope hcoef hker
  have hp' := mul_le_envelope hp (envelope_lift hD (by omega : k ≤ k+4))
  exact add_le_envelope (envelope_lift hH (by omega)) hp'

#print axioms torsionBound_mono
#print axioms torsionBound_le_algebraBound
#print axioms presentation_le_envelope
#print axioms relativeKernel_le_envelope
#print axioms representative_le_envelope
#print axioms catalogue_le_envelope
#print axioms monitor_envelope_bounds
#print axioms monitorCost_le_algebraBound
#print axioms gammaL_le_envelope
#print axioms natExtensionCost_mono
#print axioms extensionCost_eq_nat
#print axioms extensionCost_le_envelope
#print axioms compressionCertCost_le_envelope
end TypedTriangle.TowerBounds
