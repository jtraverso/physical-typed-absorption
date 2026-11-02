module
public import RequestProject.TypedTriangle.Defs
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TypedTriangle.Completion

/-- The sufficient global-envelope bound; `m a` is the lower envelope
of `(1-f z)/a + f z/z` in the mathematical argument. -/
def scalarBound (d : ℝ) (f m : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (m y-f x/x)*max (x-d) 0 + (m x-f x/x)*max (y-d) 0 + f x/x*(1-2*d)

def Admissible (x y : ℝ) : Prop := 0 < y ∧ y ≤ x ∧ x < 1 ∧ x+y ≤ 1

/-- Every hypothesis is explicit. The certificate and envelope facts are
inputs, not new global axioms and not a claim that the Python certificate
has already been replayed by Lean. -/
structure ScalarInput (d s : ℝ) (f m : ℝ → ℝ) : Prop where
  certificate : ∀ x y, Admissible x y → s ≤ scalarBound d f m x y
  envelope_lower : ∀ a, 0 < a → a ≤ 1 → 1/(2*a) ≤ m a
  envelope_upper : ∀ a, 0 < a → a ≤ 1 → m a ≤ 1/a
  envelope_antitone : ∀ a b, 0 < a → a ≤ b → b ≤ 1 → m b ≤ m a

theorem scalarBound_interior (d : ℝ) (f m : ℝ → ℝ) (x y : ℝ)
    (hx : d ≤ x) (hy : d ≤ y) :
    scalarBound d f m x y = (x-d)*m y+(y-d)*m x+f x/x*(1-x-y) := by
  unfold scalarBound
  rw [max_eq_left (sub_nonneg.mpr hx),max_eq_left (sub_nonneg.mpr hy)]
  ring

/-- A certified surplus can be spent on increasing the defect constant.
This theorem proves the continuous-domain transport, including both
positive-part boundaries; it is not merely an arithmetic check at knots. -/
theorem scalar_certificate_transport (d₀ d s t : ℝ) (f m : ℝ → ℝ)
    (hd₀ : 0 < d₀) (hdd : d₀ ≤ d) (hd : d < 1/4)
    (hInput : ScalarInput d₀ s f m)
    (hPlateau : ∀ x, 0 < x → x ≤ d → f x=1/2)
    (hTail : ∀ x, 1-d < x → x < 1 → f x=0)
    (hNear : t ≤ (1-2*d)/(2*d))
    (hBudget : t+2*(d-d₀)/d ≤ s) :
    ∀ x y, Admissible x y → t ≤ scalarBound d f m x y := by
  have hdpos : 0 < d := lt_of_lt_of_le hd₀ hdd
  have hdOne : d ≤ 1 := by linarith
  have hInt : ∀ x y, Admissible x y → d ≤ y → t ≤ scalarBound d f m x y := by
    intro x y hxy hyd
    obtain ⟨hy,hYX,hx,hSum⟩ := hxy
    have hxd : d ≤ x := hyd.trans hYX
    have hOld := hInput.certificate x y ⟨hy,hYX,hx,hSum⟩
    have hmx : m x ≤ 1/d := (hInput.envelope_upper x (hdpos.trans_le hxd) hx.le).trans
      (one_div_le_one_div_of_le hdpos hxd)
    have hmy : m y ≤ 1/d := (hInput.envelope_upper y hy (by linarith)).trans
      (one_div_le_one_div_of_le hdpos hyd)
    rw [scalarBound_interior d₀ f m x y (hdd.trans hxd) (hdd.trans hyd)] at hOld
    rw [scalarBound_interior d f m x y hxd hyd]
    have hCost : (d-d₀)*(m x+m y) ≤ 2*(d-d₀)/d := by
      have hm : m x+m y ≤ 2/d := by
        calc
          m x+m y ≤ 1/d+1/d := add_le_add hmx hmy
          _ = 2/d := by ring
      have hh := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hdd)
      convert hh using 1 <;> ring
    nlinarith
  intro x y hxy
  obtain ⟨hy,hYX,hx,hSum⟩ := hxy
  have hxpos : 0 < x := hy.trans_le hYX
  by_cases hxd : x ≤ d
  · have hf := hPlateau x hxpos hxd
    have hsmall : scalarBound d f m x y=(1-2*d)/(2*x) := by
      unfold scalarBound
      rw [max_eq_right (sub_nonpos.mpr hxd),max_eq_right (sub_nonpos.mpr (hYX.trans hxd)),hf]
      ring
    rw [hsmall]
    apply hNear.trans
    apply div_le_div_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hdx : d < x := lt_of_not_ge hxd
  by_cases hyd : d ≤ y
  · exact hInt x y ⟨hy,hYX,hx,hSum⟩ hyd
  have hyd' : y ≤ d := le_of_lt (lt_of_not_ge hyd)
  by_cases hxcap : x ≤ 1-d
  · have hClamp := hInt x d ⟨hdpos,hdx.le,hx,by linarith⟩ le_rfl
    have hmm := hInput.envelope_antitone y d hy hyd' hdOne
    have hCompare : scalarBound d f m x d ≤ scalarBound d f m x y := by
      unfold scalarBound
      rw [max_eq_left (sub_nonneg.mpr hdx.le),max_eq_right (sub_nonpos.mpr hyd')]
      simp only [sub_self,max_self,mul_zero,add_zero]
      have hh := mul_le_mul_of_nonneg_right hmm (sub_nonneg.mpr hdx.le)
      nlinarith
    exact hClamp.trans hCompare
  · have hLarge : 1-d < x := lt_of_not_ge hxcap
    have hf := hTail x hLarge hx
    have hmy := hInput.envelope_lower y hy (by linarith)
    have hLoad : scalarBound d f m x y=(x-d)*m y := by
      unfold scalarBound
      rw [hf,max_eq_left (sub_nonneg.mpr hdx.le),max_eq_right (sub_nonpos.mpr hyd')]
      simp [mul_comm]
    rw [hLoad]
    have hLower : (1-2*d)/(2*d) ≤ (x-d)*m y := by
      have hmul := mul_le_mul_of_nonneg_left hmy (sub_nonneg.mpr hdx.le)
      have hFraction : (1-2*d)/(2*d) ≤ (x-d)/(2*y) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith
      have hRearrange : (x-d)/(2*y)=(x-d)*(1/(2*y)) := by ring
      rw [hRearrange] at hFraction
      exact hFraction.trans hmul
    exact hNear.trans hLower

def certifiedDefect : ℝ := 23197/100000
def improvedDefect : ℝ := 2319701/10000000
def improvedDensity : ℝ := 2319691/10000000
def certifiedSurplus : ℝ := 1000001/1000000
def improvedSurplus : ℝ := 100000001/100000000

/-- Exact numerical budget, checked by the ordinary Lean kernel. -/
theorem incremental_budget :
    improvedSurplus+2*(improvedDefect-certifiedDefect)/improvedDefect ≤ certifiedSurplus ∧
    improvedSurplus ≤ (1-2*improvedDefect)/(2*improvedDefect) ∧
    improvedDefect-improvedDensity=1/1000000 ∧
    (1159/5000 : ℝ) < improvedDensity := by
  norm_num [improvedSurplus,improvedDefect,certifiedDefect,certifiedSurplus,improvedDensity]

theorem incremental_scalar_certificate (f m : ℝ → ℝ)
    (hInput : ScalarInput certifiedDefect certifiedSurplus f m)
    (hPlateau : ∀ x, 0 < x → x ≤ improvedDefect → f x=1/2)
    (hTail : ∀ x, 1-improvedDefect < x → x < 1 → f x=0) :
    ∀ x y, Admissible x y → improvedSurplus ≤ scalarBound improvedDefect f m x y := by
  apply scalar_certificate_transport certifiedDefect improvedDefect certifiedSurplus
    improvedSurplus f m (by norm_num [certifiedDefect])
    (by norm_num [certifiedDefect,improvedDefect]) (by norm_num [improvedDefect])
    hInput hPlateau hTail incremental_budget.2.1 incremental_budget.1

#print axioms scalar_certificate_transport
#print axioms incremental_scalar_certificate
#print axioms incremental_budget
end TypedTriangle.Completion
