module
public import RequestProject.TypedTriangle.CompletionHybridCapacity
public import RequestProject.TypedTriangle.CompletionScalarStability
@[expose] public section
open Finset
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Completion.HybridUniversal

def weighted {B R : Type} (receivers : Finset R) (alpha : R → ℝ)
    (P : B → R → ℝ) (b : B) : ℝ := ∑ r ∈ receivers,alpha r*P b r

def score {B R : Type} (senders : Finset B) (receivers : Finset R)
    (alpha : R → ℝ) (N Q : B → R → ℝ) : ℝ :=
  ∑ b ∈ senders,max (weighted receivers alpha N b) (weighted receivers alpha Q b)

theorem max_gain_identity (p q : ℝ) : max p q=p+max 0 (q-p) := by
  by_cases h : p ≤ q
  · rw [max_eq_right h,max_eq_right (sub_nonneg.mpr h)]
    ring
  · have hh : q ≤ p := le_of_not_ge h
    rw [max_eq_left hh,max_eq_left (sub_nonpos.mpr hh),add_zero]

/-- Exact reduction. The missing graph theorem concerns these two gains;
this identity does not assume or prove they cover every deficit. -/
theorem dual_gain_identity {B R : Type} (senders : Finset B) (receivers : Finset R)
    (alpha : R → ℝ) (P N Q : B → R → ℝ) :
    score senders receivers alpha N Q=
      (∑ b ∈ senders,weighted receivers alpha P b)+
      (∑ b ∈ senders,(weighted receivers alpha N b-weighted receivers alpha P b))+
      ∑ b ∈ senders,max 0 (weighted receivers alpha Q b-weighted receivers alpha N b) := by
  unfold score
  calc
    _ = ∑ b ∈ senders,(weighted receivers alpha P b+
        (weighted receivers alpha N b-weighted receivers alpha P b)+
        max 0 (weighted receivers alpha Q b-weighted receivers alpha N b)) := by
      apply sum_congr rfl
      intro b _
      rw [max_gain_identity]
      ring
    _ = _ := by rw [sum_add_distrib,sum_add_distrib]

theorem dual_ge_base {B R : Type} (senders : Finset B) (receivers : Finset R)
    (alpha : R → ℝ) (P N Q : B → R → ℝ)
    (hA : ∀ r ∈ receivers,0 ≤ alpha r)
    (hDom : ∀ b ∈ senders,∀ r ∈ receivers,P b r ≤ N b r) :
    (∑ r ∈ receivers,alpha r*(∑ b ∈ senders,P b r)) ≤
      score senders receivers alpha N Q := by
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_le_sum
  intro b hb
  exact (sum_le_sum fun r hr =>
    mul_le_mul_of_nonneg_left (hDom b hb r hr) (hA r hr)).trans (le_max_left _ _)

theorem receiver_lower_to_dual {B R : Type} (senders : Finset B) (receivers : Finset R)
    (alpha : R → ℝ) (P N Q : B → R → ℝ) (t : ℝ)
    (hA : ∀ r ∈ receivers,0 ≤ alpha r)
    (hSum : ∑ r ∈ receivers,alpha r=1)
    (hDom : ∀ b ∈ senders,∀ r ∈ receivers,P b r ≤ N b r)
    (hReceipt : ∀ r ∈ receivers,t ≤ ∑ b ∈ senders,P b r) :
    t ≤ score senders receivers alpha N Q := by
  calc
    t = ∑ r ∈ receivers,alpha r*t := by rw [←sum_mul,hSum,one_mul]
    _ ≤ ∑ r ∈ receivers,alpha r*(∑ b ∈ senders,P b r) :=
      sum_le_sum fun r hr => mul_le_mul_of_nonneg_left (hReceipt r hr) (hA r hr)
    _ ≤ _ := dual_ge_base senders receivers alpha P N Q hA hDom

/-- The existing scalar certificate transports universally to a value below
one at d=0.232. Its original certificate is an explicit theorem input. -/
theorem scalar_lower_at_0232 (f m : ℝ → ℝ)
    (hInput : ScalarInput certifiedDefect certifiedSurplus f m)
    (hPlateau : ∀ x,0 < x → x ≤ (29/125 : ℝ) → f x=1/2)
    (hTail : ∀ x,1-(29/125 : ℝ) < x → x < 1 → f x=0) :
    ∀ x y,Admissible x y → (28992529/29000000 : ℝ) ≤
      scalarBound (29/125) f m x y := by
  apply scalar_certificate_transport certifiedDefect (29/125) certifiedSurplus
    (28992529/29000000) f m
    (by norm_num [certifiedDefect]) (by norm_num [certifiedDefect]) (by norm_num)
    hInput hPlateau hTail
  · norm_num
  · norm_num [certifiedDefect,certifiedSurplus]

theorem exact_remaining_gap :
    (1 : ℝ)-(28992529/29000000)=7471/29000000 ∧
      (28992529/29000000 : ℝ) < 1 := by norm_num

/-- The graph receiver estimate (Proposition 4.3) is an explicit input.
The conclusion is deliberately below one; this does not close the target. -/
theorem dual_lower_0232_from_receiver_estimate {B R : Type}
    (senders : Finset B) (receivers : Finset R) (alpha : R → ℝ)
    (P N Q : B → R → ℝ) (f m : ℝ → ℝ) (x y : R → ℝ)
    (hInput : ScalarInput certifiedDefect certifiedSurplus f m)
    (hPlateau : ∀ z,0 < z → z ≤ (29/125 : ℝ) → f z=1/2)
    (hTail : ∀ z,1-(29/125 : ℝ) < z → z < 1 → f z=0)
    (hA : ∀ r ∈ receivers,0 ≤ alpha r) (hSum : ∑ r ∈ receivers,alpha r=1)
    (hDom : ∀ b ∈ senders,∀ r ∈ receivers,P b r ≤ N b r)
    (hDegrees : ∀ r ∈ receivers,Admissible (x r) (y r))
    (hReceiver : ∀ r ∈ receivers,scalarBound (29/125) f m (x r) (y r) ≤
      ∑ b ∈ senders,P b r) :
    (28992529/29000000 : ℝ) ≤ score senders receivers alpha N Q := by
  apply receiver_lower_to_dual senders receivers alpha P N Q
    (28992529/29000000) hA hSum hDom
  intro r hr
  exact (scalar_lower_at_0232 f m hInput hPlateau hTail (x r) (y r)
    (hDegrees r hr)).trans (hReceiver r hr)

/-- Scalar consequence of the uniform-splitting receiver count. This closes
the subclass with red-degree spread at most 0.036n; it is not asserted for
the original nonuniform rule or for arbitrary degree spread. -/
theorem uniform_degree_range_bound (xlo xhi : ℝ)
    (hPos : 0 < xhi)
    (hSpread : xhi-xlo ≤ (9/250 : ℝ)) :
    1 ≤ ((1-2*(29/125 : ℝ))+2*max (xlo-29/125) 0)/(2*xhi) := by
  apply (le_div_iff₀ (by positivity : 0 < 2*xhi)).mpr
  by_cases h : (29/125 : ℝ) ≤ xlo
  · rw [max_eq_left (sub_nonneg.mpr h)]
    linarith
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
    linarith

/-- Original f-proportional discharging becomes uniform when ALL red
degrees coincide. The receiver-count bound then has surplus 0.072 at 0.232. -/
theorem regular_red_degree_bound (x : ℝ) (hx : 0 < x) (hxHalf : x ≤ 1/2) :
    (134/125 : ℝ) ≤ ((1-2*(29/125 : ℝ))+2*max (x-29/125) 0)/(2*x) := by
  apply (le_div_iff₀ (by positivity : 0 < 2*x)).mpr
  by_cases h : (29/125 : ℝ) ≤ x
  · rw [max_eq_left (sub_nonneg.mpr h)]
    linarith
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
    linarith

/-- Any failing dual has very little mass on receivers whose proportional
receipt is >=1.01. No conclusion that such a dual exists is asserted. -/
theorem concentration_of_failing_dual (good bad average dual : ℝ)
    (hMass : good+bad=1) (hLower :
      (101/100 : ℝ)*good+(28992529/29000000)*bad ≤ average)
    (hDual : average ≤ dual) (hFail : dual < 1) :
    good < (7471/297471 : ℝ) ∧ (290000/297471 : ℝ) < bad := by
  constructor <;> nlinarith only [hMass,hLower,hDual,hFail]

end TypedTriangle.Completion.HybridUniversal
