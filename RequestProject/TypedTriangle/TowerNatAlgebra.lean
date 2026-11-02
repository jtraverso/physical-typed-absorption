module
public import RequestProject.TypedTriangle.GroupingClosedBound
public import RequestProject.TypedTriangle.ExplicitBoundedSolver
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.TowerBounds

/-- Pure natural recursors; no real parameters, ceilings or chosen constants. -/
def natKernel : ℕ → ℕ → ℕ
  | 0, _ => 1
  | d+1, R => (2*R+1)*natKernel d (R*(2*R+1))

def natSolver : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d+1, K => (1+2*(d+1)*(max 1 K)^2)*(natSolver d (2*(max 1 K)^2)+1)

theorem natKernel_eq (d R : ℕ) : natKernel d R = GroupingExplicit.kernelBound d R := by
  induction d generalizing R with
  | zero => rfl
  | succ d ih => simp only [natKernel, GroupingExplicit.kernelBound, ih]

theorem natSolver_eq (d K : ℕ) : natSolver d K = S07V41.Explicit.solverBound d K := by
  induction d generalizing K with
  | zero => rfl
  | succ d ih => simp only [natSolver, S07V41.Explicit.solverBound, ih]

theorem natKernel_mono_radius (d : ℕ) : Monotone (natKernel d) := by
  induction d with
  | zero => intro a b hab; exact le_rfl
  | succ d ih =>
      intro a b hab
      have hc : 2*a+1 ≤ 2*b+1 := by omega
      exact Nat.mul_le_mul hc (ih (Nat.mul_le_mul hab hc))

theorem natKernel_le_succ (d R : ℕ) : natKernel d R ≤ natKernel (d+1) R := by
  have hc : 1 ≤ 2*R+1 := by omega
  have hr : R ≤ R*(2*R+1) := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left R hc
  calc
    natKernel d R ≤ natKernel d (R*(2*R+1)) := natKernel_mono_radius d hr
    _ ≤ (2*R+1)*natKernel d (R*(2*R+1)) := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (natKernel d (R*(2*R+1))) hc

theorem natKernel_mono_dimension (R : ℕ) : Monotone (fun d => natKernel d R) :=
  monotone_nat_of_le_succ (fun d => natKernel_le_succ d R)

theorem natKernel_mono {d D R S : ℕ} (hd : d ≤ D) (hR : R ≤ S) :
    natKernel d R ≤ natKernel D S :=
  (natKernel_mono_radius d hR).trans (natKernel_mono_dimension S hd)

theorem natSolver_mono_radius (d : ℕ) : Monotone (natSolver d) := by
  induction d with
  | zero => intro a b hab; exact le_rfl
  | succ d ih =>
      intro a b hab
      have hm : max 1 a ≤ max 1 b := max_le_max_left 1 hab
      have hs := Nat.pow_le_pow_left hm 2
      have hc : 1+2*(d+1)*(max 1 a)^2 ≤ 1+2*(d+1)*(max 1 b)^2 :=
        Nat.add_le_add_left (Nat.mul_le_mul_left (2*(d+1)) hs) 1
      have hi := ih (Nat.mul_le_mul_left 2 hs)
      exact Nat.mul_le_mul hc (Nat.add_le_add_right hi 1)

theorem natSolver_le_succ (d K : ℕ) : natSolver d K ≤ natSolver (d+1) K := by
  have hk : K ≤ max 1 K := le_max_right _ _
  have hk1 : 1 ≤ max 1 K := le_max_left _ _
  have hs : max 1 K ≤ (max 1 K)^2 := by
    simpa only [Nat.mul_one, pow_two] using Nat.mul_le_mul_left (max 1 K) hk1
  have hr : K ≤ 2*(max 1 K)^2 := by omega
  have hc : 1 ≤ 1+2*(d+1)*(max 1 K)^2 := by omega
  calc
    natSolver d K ≤ natSolver d (2*(max 1 K)^2)+1 :=
      (natSolver_mono_radius d hr).trans (Nat.le_succ _)
    _ ≤ (1+2*(d+1)*(max 1 K)^2)*(natSolver d (2*(max 1 K)^2)+1) := by
      simpa only [Nat.one_mul] using
        Nat.mul_le_mul_right (natSolver d (2*(max 1 K)^2)+1) hc

theorem natSolver_mono_dimension (K : ℕ) : Monotone (fun d => natSolver d K) :=
  monotone_nat_of_le_succ (fun d => natSolver_le_succ d K)

theorem natSolver_mono {d D K L : ℕ} (hd : d ≤ D) (hK : K ≤ L) :
    natSolver d K ≤ natSolver D L :=
  (natSolver_mono_radius d hK).trans (natSolver_mono_dimension L hd)

theorem natFactorial_mono : Monotone Nat.factorial := by
  apply monotone_nat_of_le_succ
  intro n
  rw [Nat.factorial_succ]
  simpa only [Nat.one_mul] using
    Nat.mul_le_mul_right n.factorial (show 1 ≤ n+1 by omega)

/-- One level pays an arithmetic operation or either algebraic recursor. -/
def natStep (M : ℕ) : ℕ :=
  (M+1)+(M+1)^2+(M+1)^(M+1)+(M+1).factorial+natKernel M M+natSolver M M

theorem natStep_covers (M : ℕ) :
    M+1 ≤ natStep M ∧ (M+1)^2 ≤ natStep M ∧
    (M+1)^(M+1) ≤ natStep M ∧ (M+1).factorial ≤ natStep M ∧
    natKernel M M ≤ natStep M ∧ natSolver M M ≤ natStep M := by
  unfold natStep
  omega

theorem natStep_self (M : ℕ) : M ≤ natStep M := (Nat.le_succ M).trans (natStep_covers M).1

theorem natStep_mono : Monotone natStep := by
  intro M N h
  have h1 : M+1 ≤ N+1 := Nat.succ_le_succ h
  have h2 := Nat.pow_le_pow_left h1 2
  have hp : (M+1)^(M+1) ≤ (N+1)^(N+1) :=
    (Nat.pow_le_pow_left h1 (M+1)).trans (Nat.pow_le_pow_right (by omega) h1)
  have hf := natFactorial_mono h1
  have hk := natKernel_mono h h
  have hs := natSolver_mono h h
  unfold natStep
  omega

theorem add_le_natStep {a b M : ℕ} (ha : a ≤ M) (hb : b ≤ M) : a+b ≤ natStep M := by
  have h : a+b ≤ (M+1)^2 := by nlinarith
  exact h.trans (natStep_covers M).2.1

theorem mul_le_natStep {a b M : ℕ} (ha : a ≤ M) (hb : b ≤ M) : a*b ≤ natStep M := by
  have h : M*M ≤ (M+1)^2 := by nlinarith
  exact (Nat.mul_le_mul ha hb).trans (h.trans (natStep_covers M).2.1)

theorem pow_le_natStep {a b M : ℕ} (ha : a ≤ M) (hb : b ≤ M) : a^b ≤ natStep M := by
  have h1 : a ≤ M+1 := ha.trans (Nat.le_succ _)
  have h2 : b ≤ M+1 := hb.trans (Nat.le_succ _)
  exact ((Nat.pow_le_pow_left h1 b).trans
    (Nat.pow_le_pow_right (by omega) h2)).trans (natStep_covers M).2.2.1

theorem factorial_le_natStep {a M : ℕ} (ha : a ≤ M) : a.factorial ≤ natStep M :=
  (natFactorial_mono (ha.trans (Nat.le_succ _))).trans (natStep_covers M).2.2.2.1

theorem kernel_le_natStep {d R M : ℕ} (hd : d ≤ M) (hR : R ≤ M) :
    GroupingExplicit.kernelBound d R ≤ natStep M := by
  rw [← natKernel_eq]
  exact (natKernel_mono hd hR).trans (natStep_covers M).2.2.2.2.1

theorem solver_le_natStep {d K M : ℕ} (hd : d ≤ M) (hK : K ≤ M) :
    S07V41.Explicit.solverBound d K ≤ natStep M := by
  rw [← natSolver_eq]
  exact (natSolver_mono hd hK).trans (natStep_covers M).2.2.2.2.2

def natEnvelope : ℕ → ℕ → ℕ
  | 0, M => M+2
  | k+1, M => natStep (natEnvelope k M)

theorem natEnvelope_mono_input (k : ℕ) : Monotone (natEnvelope k) := by
  induction k with
  | zero => intro M N h; exact Nat.add_le_add_right h 2
  | succ k ih => intro M N h; exact natStep_mono (ih h)

theorem natEnvelope_mono_depth (M : ℕ) : Monotone (fun k => natEnvelope k M) :=
  monotone_nat_of_le_succ (fun k => natStep_self (natEnvelope k M))

theorem le_natEnvelope (k M : ℕ) : M ≤ natEnvelope k M :=
  (Nat.le_add_right M 2).trans (natEnvelope_mono_depth M (Nat.zero_le k))

theorem two_le_natEnvelope (k M : ℕ) : 2 ≤ natEnvelope k M :=
  (Nat.le_add_left 2 M).trans (natEnvelope_mono_depth M (Nat.zero_le k))

/-- Enough uniform algebraic levels for presentations, catalogues and monitors. -/
def natAlgebraBound (M : ℕ) : ℕ := natEnvelope 24 M

theorem natAlgebraBound_mono : Monotone natAlgebraBound := natEnvelope_mono_input 24

theorem natEnvelope_le_algebraBound {k M : ℕ} (hk : k ≤ 24) :
    natEnvelope k M ≤ natAlgebraBound M := natEnvelope_mono_depth M hk

#eval natKernel 2 1
#eval natSolver 2 1
#eval natStep 1
#print axioms natKernel_mono
#print axioms natSolver_mono
#print axioms natStep_mono
#print axioms kernel_le_natStep
#print axioms solver_le_natStep
#print axioms natAlgebraBound_mono
end TypedTriangle.TowerBounds
