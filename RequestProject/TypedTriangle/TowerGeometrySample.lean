module
public import RequestProject.TypedTriangle.TowerMagnitude
public import RequestProject.TypedTriangle.ExplicitUniformCompression
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TypedTriangle.TowerBounds
open ExplicitSample

/-- Natural envelopes of the explicit sample indices. No real-valued
parameter occurs in any of these definitions. -/
def sampleLcMajorant (M : ℕ) : ℕ := 30*M+1
def sampleAMajorant (M : ℕ) : ℕ := 3*M*(27*M^3+1+M)+M
def sampleTMajorant (M : ℕ) : ℕ := 6*sampleAMajorant M*M+1
def sampleJMajorant (M : ℕ) : ℕ :=
  max (4*M) (max (12*(sampleLcMajorant M+1)*M)
    (6*(sampleLcMajorant M+1)*(sampleTMajorant M+1)*M))+1
def sampleEtaMajorant (M : ℕ) : ℕ := 2^sampleJMajorant M
def sampleLMajorant (M : ℕ) : ℕ := 2*M*sampleEtaMajorant M+1
def sampleQMajorant (M : ℕ) : ℕ :=
  9*sampleLMajorant M*M*sampleEtaMajorant M*M+1+M
def sampleBMajorant (M : ℕ) : ℕ :=
  sampleLcMajorant M*(sampleJMajorant M+sampleTMajorant M)

theorem sampleLc_le_majorant {M : ℕ} {c : ℝ} (hc : Magnitude M c) :
    sampleLc c ≤ sampleLcMajorant M := by
  have h : 30/c ≤ ((30*M:ℕ):ℝ) := by
    push_cast
    calc 30/c = 30*(1/c) := by ring
      _ ≤ 30*M := mul_le_mul_of_nonneg_left hc.inv_upper (by norm_num)
  exact (Nat.ceil_le.mpr h).trans (Nat.le_succ _)

theorem sampleA_le_majorant {M q m0 : ℕ} {κ ε : ℝ}
    (hκ : Magnitude M κ) (hε : Magnitude M ε) (hq : q ≤ M) (hm : m0 ≤ M) :
    sampleA κ ε q m0 ≤ (sampleAMajorant M:ℝ) := by
  have hk0 := hκ.pos
  have he0 := hε.pos
  have hqR : (q:ℝ) ≤ M := Nat.cast_le.mpr hq
  have hmR : (m0:ℝ) ≤ M := Nat.cast_le.mpr hm
  calc
    sampleA κ ε q m0 = 3*(1/κ)*(27*(1/κ)^2*(1/ε)+1+m0)+q := by
      unfold sampleA
      field_simp
      <;> ring
    _ ≤ 3*(M:ℝ)*(27*(M:ℝ)^2*M+1+M)+M := by
      gcongr <;> first | exact hκ.inv_upper | exact hε.inv_upper | exact hmR | exact hqR
    _ = (sampleAMajorant M:ℝ) := by
      simp only [sampleAMajorant,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring

theorem sampleT_le_majorant {M q m0 : ℕ} {κ ε : ℝ}
    (hκ : Magnitude M κ) (hε : Magnitude M ε) (hq : q ≤ M) (hm : m0 ≤ M) :
    sampleT κ ε q m0 ≤ sampleTMajorant M := by
  have hk0 := hκ.pos
  have he0 := hε.pos
  have hA := sampleA_le_majorant hκ hε hq hm
  have hA0 : 0 ≤ sampleA κ ε q m0 := by unfold sampleA; positivity
  have hr : 6*sampleA κ ε q m0/ε ≤ ((6*sampleAMajorant M*M:ℕ):ℝ) := by
    push_cast
    rw [div_eq_mul_inv]
    calc 6*sampleA κ ε q m0*ε⁻¹ ≤ 6*sampleAMajorant M*(M:ℝ) := by
           gcongr <;> first | exact hA | simpa only [one_div] using hε.inv_upper
         _ = _ := by ring
  exact (Nat.ceil_le.mpr hr).trans (Nat.le_succ _)

theorem sampleJ_le_majorant {M q m0 : ℕ} {c κ ε : ℝ}
    (hc : Magnitude M c) (hκ : Magnitude M κ) (hε : Magnitude M ε)
    (hq : q ≤ M) (hm : m0 ≤ M) :
    sampleJ c κ ε q m0 ≤ sampleJMajorant M := by
  have hc0 := hc.pos
  have he0 := hε.pos
  have hLc : (sampleLc c:ℝ) ≤ sampleLcMajorant M := Nat.cast_le.mpr (sampleLc_le_majorant hc)
  have hT : (sampleT κ ε q m0:ℝ) ≤ sampleTMajorant M :=
    Nat.cast_le.mpr (sampleT_le_majorant hκ hε hq hm)
  have h1 : 4/c ≤ ((4*M:ℕ):ℝ) := by
    push_cast
    calc 4/c = 4*(1/c) := by ring
      _ ≤ 4*M := mul_le_mul_of_nonneg_left hc.inv_upper (by norm_num)
  have h2 : 12*(sampleLc c+1:ℝ)/ε ≤ ((12*(sampleLcMajorant M+1)*M:ℕ):ℝ) := by
    push_cast
    rw [div_eq_mul_inv]
    gcongr <;> first | exact hLc | exact hT | simpa only [one_div] using hε.inv_upper
  have h3 : 6*(sampleLc c+1:ℝ)*(sampleT κ ε q m0+1:ℝ)/ε ≤
      ((6*(sampleLcMajorant M+1)*(sampleTMajorant M+1)*M:ℕ):ℝ) := by
    push_cast
    rw [div_eq_mul_inv]
    gcongr <;> first | exact hLc | exact hT | simpa only [one_div] using hε.inv_upper
  have hr := max_le_max h1 (max_le_max h2 h3)
  have hn : ⌈max (4/c) (max (12*(sampleLc c+1:ℝ)/ε)
      (6*(sampleLc c+1:ℝ)*(sampleT κ ε q m0+1:ℝ)/ε))⌉₊ ≤
      max (4*M) (max (12*(sampleLcMajorant M+1)*M)
        (6*(sampleLcMajorant M+1)*(sampleTMajorant M+1)*M)) :=
    Nat.ceil_le.mpr (by simpa only [Nat.cast_max] using hr)
  exact hn.trans (Nat.le_succ _)

theorem sampleEta_magnitude {M q m0 : ℕ} {c κ ε : ℝ}
    (hc : Magnitude M c) (hκ : Magnitude M κ) (hε : Magnitude M ε)
    (hq : q ≤ M) (hm : m0 ≤ M) :
    Magnitude (sampleEtaMajorant M) (sampleEta c κ ε q m0) := by
  have hJ := sampleJ_le_majorant hc hκ hε hq hm
  refine ⟨by unfold sampleEta; positivity,?_,?_⟩
  · have hu : sampleEta c κ ε q m0 ≤ 1 := by
      unfold sampleEta
      exact pow_le_one₀ (by norm_num) (by norm_num)
    exact hu.trans (by exact_mod_cast Nat.one_le_two_pow : (1:ℝ) ≤ sampleEtaMajorant M)
  · have hEq : 1/sampleEta c κ ε q m0 = (2:ℝ)^sampleJ c κ ε q m0 := by
      simp only [sampleEta,one_div,inv_pow,inv_inv]
    rw [hEq]
    exact (pow_le_pow_right₀ (by norm_num) hJ).trans_eq
      (by simp only [sampleEtaMajorant,Nat.cast_pow,Nat.cast_ofNat])

theorem sampleL_le_majorant {M q m0 : ℕ} {c κ ε : ℝ}
    (hc : Magnitude M c) (hκ : Magnitude M κ) (hε : Magnitude M ε)
    (hq : q ≤ M) (hm : m0 ≤ M) :
    sampleL c κ ε q m0 ≤ sampleLMajorant M := by
  have hk0 := hκ.pos
  have hη := sampleEta_magnitude hc hκ hε hq hm
  have hη0 := hη.pos
  have hr : 2/(κ*sampleEta c κ ε q m0) ≤ ((2*M*sampleEtaMajorant M:ℕ):ℝ) := by
    push_cast
    calc 2/(κ*sampleEta c κ ε q m0) = 2*(1/κ)*(1/sampleEta c κ ε q m0) := by field_simp <;> ring
      _ ≤ 2*M*sampleEtaMajorant M := by gcongr <;> first | exact hκ.inv_upper | exact hη.inv_upper
  exact (Nat.ceil_le.mpr hr).trans (Nat.le_succ _)

theorem sampleQ_le_majorant {M q m0 : ℕ} {c κ ε : ℝ}
    (hc : Magnitude M c) (hκ : Magnitude M κ) (hε : Magnitude M ε)
    (hq : q ≤ M) (hm : m0 ≤ M) :
    sampleQ c κ ε q m0 ≤ sampleQMajorant M := by
  have hk0 := hκ.pos
  have he0 := hε.pos
  have hη := sampleEta_magnitude hc hκ hε hq hm
  have hη0 := hη.pos
  have hL : (sampleL c κ ε q m0:ℝ) ≤ sampleLMajorant M :=
    Nat.cast_le.mpr (sampleL_le_majorant hc hκ hε hq hm)
  have hr : 9*sampleL c κ ε q m0/(κ*sampleEta c κ ε q m0*ε) ≤
      ((9*sampleLMajorant M*M*sampleEtaMajorant M*M:ℕ):ℝ) := by
    push_cast
    calc 9*sampleL c κ ε q m0/(κ*sampleEta c κ ε q m0*ε) =
        9*sampleL c κ ε q m0*(1/κ)*(1/sampleEta c κ ε q m0)*(1/ε) := by field_simp <;> ring
      _ ≤ 9*sampleLMajorant M*M*sampleEtaMajorant M*M := by
        gcongr <;> first | exact hL | exact hκ.inv_upper | exact hη.inv_upper | exact hε.inv_upper
  exact (Nat.add_le_add (Nat.ceil_le.mpr hr) hm).trans (by unfold sampleQMajorant; omega)

theorem sampleB_le_majorant {M q m0 : ℕ} {c κ ε : ℝ}
    (hc : Magnitude M c) (hκ : Magnitude M κ) (hε : Magnitude M ε)
    (hq : q ≤ M) (hm : m0 ≤ M) :
    sampleB c κ ε q m0 ≤ sampleBMajorant M :=
  Nat.mul_le_mul (sampleLc_le_majorant hc)
    (Nat.add_le_add (sampleJ_le_majorant hc hκ hε hq hm) (sampleT_le_majorant hκ hε hq hm))

/-- One natural scale paying all arguments of the compression sampler. -/
def compressionClipMajorant (M : ℕ) : ℕ := M+1
def compressionPowerMajorant (M : ℕ) : ℕ := 2^(M^2)
def compressionThetaMajorant (M : ℕ) : ℕ := compressionClipMajorant M*(64*compressionPowerMajorant M)
def compressionKappaMajorant (M : ℕ) : ℕ :=
  max ((compressionClipMajorant M*2)*4)
    (((compressionThetaMajorant M*4)*(compressionThetaMajorant M*2))*16)
def compressionPrecisionMajorant (M : ℕ) : ℕ :=
  (compressionClipMajorant M*compressionThetaMajorant M)*16
def compressionInitialMajorant (M : ℕ) : ℕ :=
  32*(compressionClipMajorant M*compressionThetaMajorant M^2)
def compressionInputMajorant (M : ℕ) : ℕ :=
  2*compressionClipMajorant M+compressionKappaMajorant M+
    compressionPrecisionMajorant M+compressionInitialMajorant M+1

def compressionSampleMajorant (M : ℕ) : ℕ :=
  sampleLMajorant (compressionInputMajorant M)*sampleQMajorant (compressionInputMajorant M)+
    sampleBMajorant (compressionInputMajorant M)

def compressionOrderMajorant (M : ℕ) : ℕ :=
  4*compressionClipMajorant M+4*M*compressionPowerMajorant M*compressionClipMajorant M+1

theorem clipped_magnitude {M : ℕ} {α : ℝ} (hα : Magnitude M α) :
    Magnitude (compressionClipMajorant M) (min α 1) :=
  (hα.min Magnitude.one).mono (by unfold compressionClipMajorant; omega)

theorem hingePower_magnitude {M h : ℕ} (hh : h ≤ M) :
    Magnitude (compressionPowerMajorant M) ((2:ℝ)^h.choose 2) := by
  have he : h.choose 2 ≤ M^2 :=
    (Nat.choose_le_pow h 2).trans (Nat.pow_le_pow_left hh 2)
  have hn : 2^h.choose 2 ≤ compressionPowerMajorant M :=
    Nat.pow_le_pow_right (by decide) he
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using
    (Magnitude.natCast (Nat.one_le_two_pow) hn)

theorem compressionSampleSize_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    compressionSampleSize α h ≤ compressionSampleMajorant M := by
  let a := min α 1
  let θ := a/(64*(2:ℝ)^h.choose 2)
  let κ := expConst (a/2) (θ/2) (θ/4)
  let ε := a*θ/16
  let m0 := ⌈32/(a*θ^2)⌉₊
  have ha : Magnitude (compressionClipMajorant M) a := clipped_magnitude hα
  have hP := hingePower_magnitude hh
  have h64 : Magnitude 64 (64:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h2 : Magnitude 2 (2:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h4 : Magnitude 4 (4:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h16 : Magnitude 16 (16:ℝ) := Magnitude.natCast (by decide) le_rfl
  have h32 : Magnitude 32 (32:ℝ) := Magnitude.natCast (by decide) le_rfl
  have hθ : Magnitude (compressionThetaMajorant M) θ := ha.div (h64.mul hP)
  have hκ : Magnitude (compressionKappaMajorant M) κ :=
    (ha.div h2 |>.div h4).min ((hθ.div h4 |>.mul (hθ.div h2)).div h16)
  have hε : Magnitude (compressionPrecisionMajorant M) ε := (ha.mul hθ).div h16
  have hm0 : m0 ≤ compressionInitialMajorant M := (h32.div (ha.mul (hθ.pow 2))).ceil_le
  let U := compressionInputMajorant M
  have hcU : Magnitude U (a/2) := (ha.div h2).mono (by
    dsimp only [U,compressionInputMajorant]
    omega)
  have hkU : Magnitude U κ := hκ.mono (by dsimp only [U,compressionInputMajorant]; omega)
  have heU : Magnitude U ε := hε.mono (by dsimp only [U,compressionInputMajorant]; omega)
  have hmU : m0 ≤ U := hm0.trans (by dsimp only [U,compressionInputMajorant]; omega)
  have hqU : 1 ≤ U := by dsimp only [U,compressionInputMajorant]; omega
  have hL := sampleL_le_majorant hcU hkU heU hqU hmU
  have hQ := sampleQ_le_majorant hcU hkU heU hqU hmU
  have hB := sampleB_le_majorant hcU hkU heU hqU hmU
  exact Nat.add_le_add (Nat.mul_le_mul hL hQ) hB

theorem compressionOrder_le_majorant {M h : ℕ} {α : ℝ}
    (hα : Magnitude M α) (hh : h ≤ M) :
    compressionOrder α h ≤ compressionOrderMajorant M := by
  have ha := clipped_magnitude hα
  have hP := hingePower_magnitude hh
  have ha0 := ha.pos
  have hhr : (h:ℝ) ≤ M := Nat.cast_le.mpr hh
  have h1 : 4/min α 1 ≤ ((4*compressionClipMajorant M:ℕ):ℝ) := by
    push_cast
    calc 4/min α 1 = 4*(1/min α 1) := by ring
      _ ≤ 4*compressionClipMajorant M := mul_le_mul_of_nonneg_left ha.inv_upper (by norm_num)
  have h2 : 4*h*(2:ℝ)^h.choose 2/min α 1 ≤
      ((4*M*compressionPowerMajorant M*compressionClipMajorant M:ℕ):ℝ) := by
    push_cast
    calc 4*h*(2:ℝ)^h.choose 2/min α 1 = 4*h*(2:ℝ)^h.choose 2*(1/min α 1) := by ring
      _ ≤ 4*M*compressionPowerMajorant M*compressionClipMajorant M := by
        gcongr <;> first | exact hhr | exact hP.upper | exact ha.inv_upper
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.ceil_le.mpr h1) (Nat.ceil_le.mpr h2)) 1

#print axioms sampleEta_magnitude
#print axioms sampleQ_le_majorant
end TypedTriangle.TowerBounds
