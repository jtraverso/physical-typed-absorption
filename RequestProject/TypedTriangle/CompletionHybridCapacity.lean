module
public import RequestProject.TypedTriangle.CompletionHybridDischarging
@[expose] public section
open Finset
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Completion.HybridCapacity

/-- Spend the proportional rule first, then use the remaining fraction on Q. -/
def fill {B R : Type} (P Q : B → R → ℝ) (slack : B → ℝ) (b : B) (r : R) : ℝ :=
  P b r+slack b*Q b r

theorem fill_dominates {B R : Type} (P Q : B → R → ℝ) (slack : B → ℝ)
    (hS : ∀ b,0 ≤ slack b) (hQ : ∀ b r,0 ≤ Q b r) :
    ∀ b r,P b r ≤ fill P Q slack b r := by
  intro b r
  exact le_add_of_nonneg_right (mul_nonneg (hS b) (hQ b r))

theorem fill_sender_budget {B R : Type} (receivers : Finset R)
    (P Q : B → R → ℝ) (slack capacity : B → ℝ)
    (hS : ∀ b,0 ≤ slack b)
    (hP : ∀ b,∑ r ∈ receivers,P b r=(1-slack b)*capacity b)
    (hQ : ∀ b,∑ r ∈ receivers,Q b r ≤ capacity b) :
    ∀ b,∑ r ∈ receivers,fill P Q slack b r ≤ capacity b := by
  intro b
  simp only [fill,sum_add_distrib,←mul_sum,hP]
  have hh := mul_le_mul_of_nonneg_left (hQ b) (hS b)
  nlinarith only [hh]

theorem fill_receiver_lower {B R : Type} (senders : Finset B)
    (P Q : B → R → ℝ) (slack : B → ℝ) (r : R) (p q s : ℝ)
    (hP : p ≤ ∑ b ∈ senders,P b r) (hQ : q ≤ ∑ b ∈ senders,Q b r)
    (hQr : ∀ b,0 ≤ Q b r) (hS : ∀ b,s ≤ slack b) (hs : 0 ≤ s) :
    p+s*q ≤ ∑ b ∈ senders,fill P Q slack b r := by
  have hsum : s*(∑ b ∈ senders,Q b r) ≤ ∑ b ∈ senders,slack b*Q b r := by
    rw [mul_sum]
    exact sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hS b) (hQr b)
  have hq := mul_le_mul_of_nonneg_left hQ hs
  simp only [fill,sum_add_distrib]
  linarith

/-- Exact slack identity for a proportional sender with two positive red degrees.
N counts quasi-negative triangles; missing counts red neighbours not completed.
The last term records the sum of their triangle-weight surpluses. -/
theorem proportional_slack_identity (c a b dv dw n nv nw missingV missingW deficitSum : ℝ)
    (hSplit : a*dv+b*dw=1)
    (hV : dv=n+nv+missingV) (hW : dw=n+nw+missingW) :
    c-((a+b)*deficitSum+a*c*nv+b*c*nw)=
      c*(a*missingV+b*missingW)+(a+b)*(n*c-deficitSum) := by
  have hc := congrArg (fun z : ℝ => c*z) hSplit
  rw [hV,hW] at hc
  nlinarith only [hc]

/-- Multiplying a full-capacity P ray by its former usage fraction and filling
with Q is exactly the safe fill rule. -/
theorem normalized_fill_identity (p q usage : ℝ) (h : usage ≠ 0) :
    usage*(p/usage)+(1-usage)*q=p+(1-usage)*q := by
  rw [mul_div_cancel₀ p h]

/-- Every old mixture is dominated by a full-capacity mixture when P uses
the fraction usage of its sender capacity. -/
theorem full_ray_domination (p q usage theta : ℝ)
    (hUsage : 0 ≤ usage ∧ usage ≤ 1) (hTheta : 0 ≤ theta ∧ theta ≤ 1)
    (hq : 0 ≤ q) :
    0 ≤ theta*usage ∧ theta*usage ≤ 1 ∧
      theta*(usage*p)+(1-theta)*q ≤
        (theta*usage)*p+(1-theta*usage)*q := by
  refine ⟨mul_nonneg hTheta.1 hUsage.1,?_,?_⟩
  · calc
      theta*usage ≤ 1*usage := mul_le_mul_of_nonneg_right hTheta.2 hUsage.1
      _ ≤ 1 := by simpa using hUsage.2
  · have hh := mul_nonneg (mul_nonneg hTheta.1 (sub_nonneg.mpr hUsage.2)) hq
    nlinarith only [hh]

theorem box_support (s t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) : t*s ≤ max 0 s := by
  by_cases hs : 0 ≤ s
  · rw [max_eq_right hs]
    nlinarith only [ht.2,hs]
  · rw [max_eq_left (le_of_not_ge hs)]
    exact mul_nonpos_of_nonneg_of_nonpos ht.1 (le_of_not_ge hs)

theorem box_support_attained (s : ℝ) :
    ∃ t : ℝ,0 ≤ t ∧ t ≤ 1 ∧ t*s=max 0 s := by
  by_cases hs : 0 ≤ s
  · exact ⟨1,by norm_num,le_refl _,by rw [one_mul,max_eq_right hs]⟩
  · exact ⟨0,le_refl _,by norm_num,by rw [zero_mul,max_eq_left (le_of_not_ge hs)]⟩

/-- Exact weighted-receiver upper bound for sender-dependent mixing.
It certifies infeasibility when its right side is below the target. -/
theorem adaptive_dual_upper {B R : Type} (senders : Finset B) (receivers : Finset R)
    (P Q : B → R → ℝ) (θ : B → ℝ) (alpha : R → ℝ) (target : ℝ)
    (hθ : ∀ b,0 ≤ θ b ∧ θ b ≤ 1) (hA : ∀ r,0 ≤ alpha r)
    (hSum : ∑ r ∈ receivers,alpha r=1)
    (hCover : ∀ r ∈ receivers,target ≤ ∑ b ∈ senders,Hybrid.mix θ P Q b r) :
    target ≤ (∑ r ∈ receivers,alpha r*(∑ b ∈ senders,Q b r))+
      ∑ b ∈ senders,max 0 (∑ r ∈ receivers,alpha r*(P b r-Q b r)) := by
  have htarget : target ≤ ∑ r ∈ receivers,alpha r*
      (∑ b ∈ senders,Hybrid.mix θ P Q b r) := by
    calc
      target = ∑ r ∈ receivers,alpha r*target := by rw [←sum_mul,hSum,one_mul]
      _ ≤ _ := sum_le_sum fun r hr => mul_le_mul_of_nonneg_left (hCover r hr) (hA r)
  have hid : (∑ r ∈ receivers,alpha r*(∑ b ∈ senders,Hybrid.mix θ P Q b r))=
      (∑ r ∈ receivers,alpha r*(∑ b ∈ senders,Q b r))+
        ∑ b ∈ senders,θ b*(∑ r ∈ receivers,alpha r*(P b r-Q b r)) := by
    simp only [mul_sum]
    rw [sum_comm (s:=senders)]
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro r _
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro b _
    unfold Hybrid.mix
    ring
  rw [hid] at htarget
  have hb := sum_le_sum (s:=senders) fun b _ =>
    box_support (∑ r ∈ receivers,alpha r*(P b r-Q b r)) (θ b) (hθ b)
  linarith

end TypedTriangle.Completion.HybridCapacity
