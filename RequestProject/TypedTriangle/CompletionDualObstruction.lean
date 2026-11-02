module
public import RequestProject.TypedTriangle.CompletionScalarStability
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace TypedTriangle.Completion.DualObstruction
/-- Obstruction for the conservative global-envelope criterion only.
This is not an obstruction to a Latin completion or to the full M bound. -/
theorem conservative_bound_obstruction (f m : ℝ → ℝ)
    (hF : ∀ a, 0 < a → a < 1 → 0 ≤ f a ∧ f a ≤ 1/2)
    (hM : ∀ a, 0 < a → a < 1 → 0 ≤ m a ∧ m a ≤ 1/a)
    (hMono : ∀ a b, 0 < a → a ≤ b → b < 1 → f b ≤ f a)
    (hEnv : ∀ a z, 0 < a → a < z → z < 1 →
      m a+(1/a-1/z)*f z ≤ 1/a) :
    ¬ (∀ x y, Admissible x y → 1 ≤ scalarBound (115989/500000:ℝ) f m x y) := by
  intro hCert
  have h0 := hEnv (115989/500000:ℝ) (8503/20000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h0
  have h1 := hEnv (5507/18000:ℝ) (80519/180000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h1
  have h2 := hEnv (56567/180000:ℝ) (4501/10000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h2
  have h3 := hEnv (11513/36000:ℝ) (81517/180000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h3
  have h4 := hEnv (3629/11250:ℝ) (81517/180000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h4
  have h5 := hEnv (6507/20000:ℝ) (81517/180000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h5
  have h6 := hEnv (29531/90000:ℝ) (2563/5625:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h6
  have h7 := hEnv (8503/20000:ℝ) (22001/45000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h7
  have h8 := hEnv (80519/180000:ℝ) (89501/180000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h8
  have h9 := hEnv (4501/10000:ℝ) (89501/180000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h9
  have h10 := hEnv (81517/180000:ℝ) (89501/180000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h10
  have h11 := hEnv (2563/5625:ℝ) (1/2:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h11
  have h12 := hEnv (22001/45000:ℝ) (18499/36000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h12
  have h13 := hEnv (89501/180000:ℝ) (15499/30000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h13
  have h14 := hEnv (1/2:ℝ) (93493/180000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h14
  have h15 := hEnv (18499/36000:ℝ) (10499/20000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h15
  have h16 := hEnv (15499/30000:ℝ) (10499/20000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h16
  have h17 := hEnv (93493/180000:ℝ) (9499/18000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h17
  have h18 := hEnv (10499/20000:ℝ) (95489/180000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h18
  have h19 := hEnv (9499/18000:ℝ) (33493/60000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h19
  have h20 := hEnv (95489/180000:ℝ) (33493/60000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h20
  have h21 := hCert (1001/3000:ℝ) (115989/500000:ℝ) (by norm_num [Admissible])
  norm_num [scalarBound] at h21
  have h22 := hCert (8503/20000:ℝ) (5507/18000:ℝ) (by norm_num [Admissible])
  norm_num [scalarBound] at h22
  have h23 := hCert (80519/180000:ℝ) (11513/36000:ℝ) (by norm_num [Admissible])
  norm_num [scalarBound] at h23
  have h24 := hCert (4501/10000:ℝ) (3629/11250:ℝ) (by norm_num [Admissible])
  norm_num [scalarBound] at h24
  have h25 := hCert (81517/180000:ℝ) (3629/11250:ℝ) (by norm_num [Admissible])
  norm_num [scalarBound] at h25
  have h26 := hCert (2563/5625:ℝ) (3629/11250:ℝ) (by norm_num [Admissible])
  norm_num [scalarBound] at h26
  have h27 := hCert (22001/45000:ℝ) (29531/90000:ℝ) (by norm_num [Admissible])
  norm_num [scalarBound] at h27
  have h28 := hCert (89501/180000:ℝ) (29531/90000:ℝ) (by norm_num [Admissible])
  norm_num [scalarBound] at h28
  have h29 := hCert (1/2:ℝ) (6507/20000:ℝ) (by norm_num [Admissible])
  norm_num [scalarBound] at h29
  have h30 := hCert (18499/36000:ℝ) (3629/11250:ℝ) (by norm_num [Admissible])
  norm_num [scalarBound] at h30
  have h31 := hCert (15499/30000:ℝ) (11513/36000:ℝ) (by norm_num [Admissible])
  norm_num [scalarBound] at h31
  have h32 := hCert (93493/180000:ℝ) (11513/36000:ℝ) (by norm_num [Admissible])
  norm_num [scalarBound] at h32
  have h33 := hCert (10499/20000:ℝ) (56567/180000:ℝ) (by norm_num [Admissible])
  norm_num [scalarBound] at h33
  have h34 := hCert (9499/18000:ℝ) (56567/180000:ℝ) (by norm_num [Admissible])
  norm_num [scalarBound] at h34
  have h35 := hCert (95489/180000:ℝ) (56567/180000:ℝ) (by norm_num [Admissible])
  norm_num [scalarBound] at h35
  have b0 := (hF (1001/3000:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b0
  have b1 := (hF (8503/20000:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b1
  have b2 := (hF (80519/180000:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b2
  have b3 := (hF (4501/10000:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b3
  have b4 := (hF (81517/180000:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b4
  have b5 := (hF (2563/5625:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b5
  have b6 := (hF (22001/45000:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b6
  have b7 := (hF (89501/180000:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b7
  have b8 := (hF (1/2:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b8
  have b9 := (hF (18499/36000:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b9
  have b10 := (hF (15499/30000:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b10
  have b11 := (hF (93493/180000:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b11
  have b12 := (hF (10499/20000:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b12
  have b13 := (hF (9499/18000:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b13
  have b14 := (hF (95489/180000:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b14
  have b15 := (hF (33493/60000:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b15
  have b16 := (hM (115989/500000:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b16
  have b17 := (hM (5507/18000:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b17
  have b18 := (hM (56567/180000:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b18
  have b19 := (hM (11513/36000:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b19
  have b20 := (hM (3629/11250:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b20
  have b21 := (hM (6507/20000:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b21
  have b22 := (hM (29531/90000:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b22
  have b23 := (hM (8503/20000:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b23
  have b24 := (hM (80519/180000:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b24
  have b25 := (hM (4501/10000:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b25
  have b26 := (hM (81517/180000:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b26
  have b27 := (hM (2563/5625:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b27
  have b28 := (hM (22001/45000:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b28
  have b29 := (hM (89501/180000:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b29
  have b30 := (hM (1/2:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b30
  have b31 := (hM (18499/36000:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b31
  have b32 := (hM (15499/30000:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b32
  have b33 := (hM (93493/180000:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b33
  have b34 := (hM (10499/20000:ℝ) (by norm_num) (by norm_num)).1
  norm_num at b34
  have b35 := (hM (9499/18000:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b35
  have b36 := (hM (95489/180000:ℝ) (by norm_num) (by norm_num)).2
  norm_num at b36
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,b26,b27,b28,b29,b30,b31,b32,b33,b34,b35,b36]
#print axioms conservative_bound_obstruction
end TypedTriangle.Completion.DualObstruction
