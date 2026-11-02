module
public import RequestProject.TypedTriangle.CompletionScalarStability
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace TypedTriangle.Completion.FullMDualObstruction
def fullBound (d : ℝ) (f : ℝ → ℝ) (M : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (M y (1-x)-f x/x)*max (x-d) 0+(M x (1-y)-f x/x)*max (y-d) 0+f x/x*(1-2*d)
/-- The finite certificate obstructs the full scalar criterion, not Latin
completion or the success of the actual discharging rule. -/
theorem full_scalar_criterion_obstruction (f : ℝ → ℝ) (M : ℝ → ℝ → ℝ)
    (hF : ∀ a, 0 < a → a < 1 → 0 ≤ f a ∧ f a ≤ 1/2)
    (hM : ∀ a b, 0 < a → a ≤ b → b < 1 → 0 ≤ M a b ∧ M a b ≤ 1/a)
    (hEnv : ∀ a b z, 0 < a → a < z → z ≤ b → b < 1 →
      M a b+(1/a-1/z)*f z ≤ 1/a) :
    ¬ (∀ x y, Admissible x y → 1 ≤ fullBound (115989/500000:ℝ) f M x y) := by
  intro hCert
  let u84 : ℝ := (M (115989/500000:ℝ) (1999/3000:ℝ))
  let u111 : ℝ := (M (5507/18000:ℝ) (11497/20000:ℝ))
  let u114 : ℝ := (max (M (56567/180000:ℝ) (84511/180000:ℝ)) (max (M (56567/180000:ℝ) (8501/18000:ℝ)) (M (56567/180000:ℝ) (9501/20000:ℝ))))
  let u116 : ℝ := (max (M (11513/36000:ℝ) (86507/180000:ℝ)) (max (M (11513/36000:ℝ) (14501/30000:ℝ)) (M (11513/36000:ℝ) (99481/180000:ℝ))))
  let u117 : ℝ := (max (M (3629/11250:ℝ) (17501/36000:ℝ)) (max (M (3629/11250:ℝ) (3062/5625:ℝ)) (max (M (3629/11250:ℝ) (98483/180000:ℝ)) (M (3629/11250:ℝ) (5499/10000:ℝ)))))
  let u118 : ℝ := (M (6507/20000:ℝ) (1/2:ℝ))
  let u119 : ℝ := (max (M (29531/90000:ℝ) (90499/180000:ℝ)) (M (29531/90000:ℝ) (22999/45000:ℝ)))
  let u154 : ℝ := (M (8503/20000:ℝ) (12493/18000:ℝ))
  let u162 : ℝ := (M (80519/180000:ℝ) (24487/36000:ℝ))
  let u163 : ℝ := (M (4501/10000:ℝ) (7621/11250:ℝ))
  let u164 : ℝ := (M (81517/180000:ℝ) (7621/11250:ℝ))
  let u165 : ℝ := (M (2563/5625:ℝ) (7621/11250:ℝ))
  let u177 : ℝ := (M (22001/45000:ℝ) (60469/90000:ℝ))
  let u180 : ℝ := (M (89501/180000:ℝ) (60469/90000:ℝ))
  let u181 : ℝ := (M (1/2:ℝ) (13493/20000:ℝ))
  let u186 : ℝ := (M (18499/36000:ℝ) (7621/11250:ℝ))
  let u187 : ℝ := (M (15499/30000:ℝ) (24487/36000:ℝ))
  let u188 : ℝ := (M (93493/180000:ℝ) (24487/36000:ℝ))
  let u190 : ℝ := (M (10499/20000:ℝ) (123433/180000:ℝ))
  let u191 : ℝ := (M (9499/18000:ℝ) (123433/180000:ℝ))
  let u192 : ℝ := (M (95489/180000:ℝ) (123433/180000:ℝ))
  have e0_0 : M (115989/500000:ℝ) (1999/3000:ℝ) ≤ (500000/115989:ℝ)-(1931720000/986254467:ℝ)*f (8503/20000:ℝ) := by
    have hh := hEnv (115989/500000:ℝ) (1999/3000:ℝ) (8503/20000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h0 : u84+(1931720000/986254467:ℝ)*f (8503/20000:ℝ) ≤ (500000/115989:ℝ) := by
    have hh : u84 ≤ (500000/115989:ℝ)-(1931720000/986254467:ℝ)*f (8503/20000:ℝ) := by
      dsimp only [u84]
      exact e0_0
    linarith only [hh]
  have e1_0 : M (5507/18000:ℝ) (11497/20000:ℝ) ≤ (18000/5507:ℝ)-(458082000/443418133:ℝ)*f (80519/180000:ℝ) := by
    have hh := hEnv (5507/18000:ℝ) (11497/20000:ℝ) (80519/180000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h1 : u111+(458082000/443418133:ℝ)*f (80519/180000:ℝ) ≤ (18000/5507:ℝ) := by
    have hh : u111 ≤ (18000/5507:ℝ)-(458082000/443418133:ℝ)*f (80519/180000:ℝ) := by
      dsimp only [u111]
      exact e1_0
    linarith only [hh]
  have e2_0 : M (56567/180000:ℝ) (84511/180000:ℝ) ≤ (180000/56567:ℝ)-(4990000/5196083:ℝ)*f (4501/10000:ℝ) := by
    have hh := hEnv (56567/180000:ℝ) (84511/180000:ℝ) (4501/10000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have e2_1 : M (56567/180000:ℝ) (8501/18000:ℝ) ≤ (180000/56567:ℝ)-(4990000/5196083:ℝ)*f (4501/10000:ℝ) := by
    have hh := hEnv (56567/180000:ℝ) (8501/18000:ℝ) (4501/10000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have e2_2 : M (56567/180000:ℝ) (9501/20000:ℝ) ≤ (180000/56567:ℝ)-(4990000/5196083:ℝ)*f (4501/10000:ℝ) := by
    have hh := hEnv (56567/180000:ℝ) (9501/20000:ℝ) (4501/10000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h2 : u114+(4990000/5196083:ℝ)*f (4501/10000:ℝ) ≤ (180000/56567:ℝ) := by
    have hh : u114 ≤ (180000/56567:ℝ)-(4990000/5196083:ℝ)*f (4501/10000:ℝ) := by
      dsimp only [u114]
      exact (max_le e2_0 (max_le e2_1 e2_2))
    linarith only [hh]
  have e3_0 : M (11513/36000:ℝ) (86507/180000:ℝ) ≤ (36000/11513:ℝ)-(862272000/938505221:ℝ)*f (81517/180000:ℝ) := by
    have hh := hEnv (11513/36000:ℝ) (86507/180000:ℝ) (81517/180000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have e3_1 : M (11513/36000:ℝ) (14501/30000:ℝ) ≤ (36000/11513:ℝ)-(862272000/938505221:ℝ)*f (81517/180000:ℝ) := by
    have hh := hEnv (11513/36000:ℝ) (14501/30000:ℝ) (81517/180000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have e3_2 : M (11513/36000:ℝ) (99481/180000:ℝ) ≤ (36000/11513:ℝ)-(862272000/938505221:ℝ)*f (81517/180000:ℝ) := by
    have hh := hEnv (11513/36000:ℝ) (99481/180000:ℝ) (81517/180000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h3 : u116+(862272000/938505221:ℝ)*f (81517/180000:ℝ) ≤ (36000/11513:ℝ) := by
    have hh : u116 ≤ (36000/11513:ℝ)-(862272000/938505221:ℝ)*f (81517/180000:ℝ) := by
      dsimp only [u116]
      exact (max_le e3_0 (max_le e3_1 e3_2))
    linarith only [hh]
  have e4_0 : M (3629/11250:ℝ) (17501/36000:ℝ) ≤ (11250/3629:ℝ)-(263846250/295825193:ℝ)*f (81517/180000:ℝ) := by
    have hh := hEnv (3629/11250:ℝ) (17501/36000:ℝ) (81517/180000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have e4_1 : M (3629/11250:ℝ) (3062/5625:ℝ) ≤ (11250/3629:ℝ)-(263846250/295825193:ℝ)*f (81517/180000:ℝ) := by
    have hh := hEnv (3629/11250:ℝ) (3062/5625:ℝ) (81517/180000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have e4_2 : M (3629/11250:ℝ) (98483/180000:ℝ) ≤ (11250/3629:ℝ)-(263846250/295825193:ℝ)*f (81517/180000:ℝ) := by
    have hh := hEnv (3629/11250:ℝ) (98483/180000:ℝ) (81517/180000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have e4_3 : M (3629/11250:ℝ) (5499/10000:ℝ) ≤ (11250/3629:ℝ)-(263846250/295825193:ℝ)*f (81517/180000:ℝ) := by
    have hh := hEnv (3629/11250:ℝ) (5499/10000:ℝ) (81517/180000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h4 : u117+(263846250/295825193:ℝ)*f (81517/180000:ℝ) ≤ (11250/3629:ℝ) := by
    have hh : u117 ≤ (11250/3629:ℝ)-(263846250/295825193:ℝ)*f (81517/180000:ℝ) := by
      dsimp only [u117]
      exact (max_le e4_0 (max_le e4_1 (max_le e4_2 e4_3)))
    linarith only [hh]
  have e5_0 : M (6507/20000:ℝ) (1/2:ℝ) ≤ (20000/6507:ℝ)-(459080000/530431119:ℝ)*f (81517/180000:ℝ) := by
    have hh := hEnv (6507/20000:ℝ) (1/2:ℝ) (81517/180000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h5 : u118+(459080000/530431119:ℝ)*f (81517/180000:ℝ) ≤ (20000/6507:ℝ) := by
    have hh : u118 ≤ (20000/6507:ℝ)-(459080000/530431119:ℝ)*f (81517/180000:ℝ) := by
      dsimp only [u118]
      exact e5_0
    linarith only [hh]
  have e6_0 : M (29531/90000:ℝ) (90499/180000:ℝ) ≤ (90000/29531:ℝ)-(64558125/75687953:ℝ)*f (2563/5625:ℝ) := by
    have hh := hEnv (29531/90000:ℝ) (90499/180000:ℝ) (2563/5625:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have e6_1 : M (29531/90000:ℝ) (22999/45000:ℝ) ≤ (90000/29531:ℝ)-(64558125/75687953:ℝ)*f (2563/5625:ℝ) := by
    have hh := hEnv (29531/90000:ℝ) (22999/45000:ℝ) (2563/5625:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h6 : u119+(64558125/75687953:ℝ)*f (2563/5625:ℝ) ≤ (90000/29531:ℝ) := by
    have hh : u119 ≤ (90000/29531:ℝ)-(64558125/75687953:ℝ)*f (2563/5625:ℝ) := by
      dsimp only [u119]
      exact (max_le e6_0 e6_1)
    linarith only [hh]
  have e7_0 : M (8503/20000:ℝ) (12493/18000:ℝ) ≤ (20000/8503:ℝ)-(57385000/187074503:ℝ)*f (22001/45000:ℝ) := by
    have hh := hEnv (8503/20000:ℝ) (12493/18000:ℝ) (22001/45000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h7 : u154+(57385000/187074503:ℝ)*f (22001/45000:ℝ) ≤ (20000/8503:ℝ) := by
    have hh : u154 ≤ (20000/8503:ℝ)-(57385000/187074503:ℝ)*f (22001/45000:ℝ) := by
      dsimp only [u154]
      exact e7_0
    linarith only [hh]
  have e8_0 : M (80519/180000:ℝ) (24487/36000:ℝ) ≤ (180000/80519:ℝ)-(1616760000/7206531019:ℝ)*f (89501/180000:ℝ) := by
    have hh := hEnv (80519/180000:ℝ) (24487/36000:ℝ) (89501/180000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h8 : u162+(1616760000/7206531019:ℝ)*f (89501/180000:ℝ) ≤ (180000/80519:ℝ) := by
    have hh : u162 ≤ (180000/80519:ℝ)-(1616760000/7206531019:ℝ)*f (89501/180000:ℝ) := by
      dsimp only [u162]
      exact e8_0
    linarith only [hh]
  have e9_0 : M (4501/10000:ℝ) (7621/11250:ℝ) ≤ (10000/4501:ℝ)-(84830000/402844001:ℝ)*f (89501/180000:ℝ) := by
    have hh := hEnv (4501/10000:ℝ) (7621/11250:ℝ) (89501/180000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h9 : u163+(84830000/402844001:ℝ)*f (89501/180000:ℝ) ≤ (10000/4501:ℝ) := by
    have hh : u163 ≤ (10000/4501:ℝ)-(84830000/402844001:ℝ)*f (89501/180000:ℝ) := by
      dsimp only [u163]
      exact e9_0
    linarith only [hh]
  have e10_0 : M (81517/180000:ℝ) (7621/11250:ℝ) ≤ (180000/81517:ℝ)-(1437120000/7295853017:ℝ)*f (89501/180000:ℝ) := by
    have hh := hEnv (81517/180000:ℝ) (7621/11250:ℝ) (89501/180000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h10 : u164+(1437120000/7295853017:ℝ)*f (89501/180000:ℝ) ≤ (180000/81517:ℝ) := by
    have hh : u164 ≤ (180000/81517:ℝ)-(1437120000/7295853017:ℝ)*f (89501/180000:ℝ) := by
      dsimp only [u164]
      exact e10_0
    linarith only [hh]
  have e11_0 : M (2563/5625:ℝ) (7621/11250:ℝ) ≤ (5625/2563:ℝ)-(499/2563:ℝ)*f (1/2:ℝ) := by
    have hh := hEnv (2563/5625:ℝ) (7621/11250:ℝ) (1/2:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h11 : u165+(499/2563:ℝ)*f (1/2:ℝ) ≤ (5625/2563:ℝ) := by
    have hh : u165 ≤ (5625/2563:ℝ)-(499/2563:ℝ)*f (1/2:ℝ) := by
      dsimp only [u165]
      exact e11_0
    linarith only [hh]
  have e12_0 : M (22001/45000:ℝ) (60469/90000:ℝ) ≤ (45000/22001:ℝ)-(40419000/406996499:ℝ)*f (18499/36000:ℝ) := by
    have hh := hEnv (22001/45000:ℝ) (60469/90000:ℝ) (18499/36000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h12 : u177+(40419000/406996499:ℝ)*f (18499/36000:ℝ) ≤ (45000/22001:ℝ) := by
    have hh : u177 ≤ (45000/22001:ℝ)-(40419000/406996499:ℝ)*f (18499/36000:ℝ) := by
      dsimp only [u177]
      exact e12_0
    linarith only [hh]
  have e13_0 : M (89501/180000:ℝ) (60469/90000:ℝ) ≤ (180000/89501:ℝ)-(104790000/1387175999:ℝ)*f (15499/30000:ℝ) := by
    have hh := hEnv (89501/180000:ℝ) (60469/90000:ℝ) (15499/30000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h13 : u180+(104790000/1387175999:ℝ)*f (15499/30000:ℝ) ≤ (180000/89501:ℝ) := by
    have hh : u180 ≤ (180000/89501:ℝ)-(104790000/1387175999:ℝ)*f (15499/30000:ℝ) := by
      dsimp only [u180]
      exact e13_0
    linarith only [hh]
  have e14_0 : M (1/2:ℝ) (13493/20000:ℝ) ≤ (2/1:ℝ)-(6986/93493:ℝ)*f (93493/180000:ℝ) := by
    have hh := hEnv (1/2:ℝ) (13493/20000:ℝ) (93493/180000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h14 : u181+(6986/93493:ℝ)*f (93493/180000:ℝ) ≤ (2/1:ℝ) := by
    have hh : u181 ≤ (2/1:ℝ)-(6986/93493:ℝ)*f (93493/180000:ℝ) := by
      dsimp only [u181]
      exact e14_0
    linarith only [hh]
  have e15_0 : M (18499/36000:ℝ) (7621/11250:ℝ) ≤ (36000/18499:ℝ)-(7984000/194221001:ℝ)*f (10499/20000:ℝ) := by
    have hh := hEnv (18499/36000:ℝ) (7621/11250:ℝ) (10499/20000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h15 : u186+(7984000/194221001:ℝ)*f (10499/20000:ℝ) ≤ (36000/18499:ℝ) := by
    have hh : u186 ≤ (36000/18499:ℝ)-(7984000/194221001:ℝ)*f (10499/20000:ℝ) := by
      dsimp only [u186]
      exact e15_0
    linarith only [hh]
  have e16_0 : M (15499/30000:ℝ) (24487/36000:ℝ) ≤ (30000/15499:ℝ)-(4990000/162724001:ℝ)*f (10499/20000:ℝ) := by
    have hh := hEnv (15499/30000:ℝ) (24487/36000:ℝ) (10499/20000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h16 : u187+(4990000/162724001:ℝ)*f (10499/20000:ℝ) ≤ (30000/15499:ℝ) := by
    have hh : u187 ≤ (30000/15499:ℝ)-(4990000/162724001:ℝ)*f (10499/20000:ℝ) := by
      dsimp only [u187]
      exact e16_0
    linarith only [hh]
  have e17_0 : M (93493/180000:ℝ) (24487/36000:ℝ) ≤ (180000/93493:ℝ)-(26946000/888090007:ℝ)*f (9499/18000:ℝ) := by
    have hh := hEnv (93493/180000:ℝ) (24487/36000:ℝ) (9499/18000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h17 : u188+(26946000/888090007:ℝ)*f (9499/18000:ℝ) ≤ (180000/93493:ℝ) := by
    have hh : u188 ≤ (180000/93493:ℝ)-(26946000/888090007:ℝ)*f (9499/18000:ℝ) := by
      dsimp only [u188]
      exact e17_0
    linarith only [hh]
  have e18_0 : M (10499/20000:ℝ) (123433/180000:ℝ) ≤ (20000/10499:ℝ)-(19960000/1002539011:ℝ)*f (95489/180000:ℝ) := by
    have hh := hEnv (10499/20000:ℝ) (123433/180000:ℝ) (95489/180000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h18 : u190+(19960000/1002539011:ℝ)*f (95489/180000:ℝ) ≤ (20000/10499:ℝ) := by
    have hh : u190 ≤ (20000/10499:ℝ)-(19960000/1002539011:ℝ)*f (95489/180000:ℝ) := by
      dsimp only [u190]
      exact e18_0
    linarith only [hh]
  have e19_0 : M (9499/18000:ℝ) (123433/180000:ℝ) ≤ (18000/9499:ℝ)-(32934000/318150007:ℝ)*f (33493/60000:ℝ) := by
    have hh := hEnv (9499/18000:ℝ) (123433/180000:ℝ) (33493/60000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h19 : u191+(32934000/318150007:ℝ)*f (33493/60000:ℝ) ≤ (18000/9499:ℝ) := by
    have hh : u191 ≤ (18000/9499:ℝ)-(32934000/318150007:ℝ)*f (33493/60000:ℝ) := by
      dsimp only [u191]
      exact e19_0
    linarith only [hh]
  have e20_0 : M (95489/180000:ℝ) (123433/180000:ℝ) ≤ (180000/95489:ℝ)-(299400000/3198213077:ℝ)*f (33493/60000:ℝ) := by
    have hh := hEnv (95489/180000:ℝ) (123433/180000:ℝ) (33493/60000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hh
    linarith only [hh]
  have h20 : u192+(299400000/3198213077:ℝ)*f (33493/60000:ℝ) ≤ (180000/95489:ℝ) := by
    have hh : u192 ≤ (180000/95489:ℝ)-(299400000/3198213077:ℝ)*f (33493/60000:ℝ) := by
      dsimp only [u192]
      exact e20_0
    linarith only [hh]
  have c21 := hCert (1001/3000:ℝ) (115989/500000:ℝ) (by norm_num [Admissible])
  norm_num [fullBound] at c21
  have s21y : M (115989/500000:ℝ) (1999/3000:ℝ) ≤ u84 := by simp [u84,le_max_iff]
  have p21y := mul_le_mul_of_nonneg_left s21y (by norm_num : (0:ℝ) ≤ (152533/1500000:ℝ))
  have h21 : -(152533/1500000:ℝ)*u84-(0/1:ℝ)*(0:ℝ)-(651533/500500:ℝ)*f (1001/3000:ℝ) ≤ -1 := by
    nlinarith only [c21,p21y]
  have c22 := hCert (8503/20000:ℝ) (5507/18000:ℝ) (by norm_num [Admissible])
  norm_num [fullBound] at c22
  have s22y : M (5507/18000:ℝ) (11497/20000:ℝ) ≤ u111 := by simp [u111,le_max_iff]
  have p22y := mul_le_mul_of_nonneg_left s22y (by norm_num : (0:ℝ) ≤ (48293/250000:ℝ))
  have s22x : M (8503/20000:ℝ) (12493/18000:ℝ) ≤ u154 := by simp [u154,le_max_iff]
  have p22x := mul_le_mul_of_nonneg_left s22x (by norm_num : (0:ℝ) ≤ (332849/4500000:ℝ))
  have h22 : -(48293/250000:ℝ)*u111-(332849/4500000:ℝ)*u154-(48403/76527:ℝ)*f (8503/20000:ℝ) ≤ -1 := by
    nlinarith only [c22,p22y,p22x]
  have c23 := hCert (80519/180000:ℝ) (11513/36000:ℝ) (by norm_num [Admissible])
  norm_num [fullBound] at c23
  have s23y : M (11513/36000:ℝ) (99481/180000:ℝ) ≤ u116 := by simp [u116,le_max_iff]
  have p23y := mul_le_mul_of_nonneg_left s23y (by norm_num : (0:ℝ) ≤ (484537/2250000:ℝ))
  have s23x : M (80519/180000:ℝ) (24487/36000:ℝ) ≤ u162 := by simp [u162,le_max_iff]
  have p23x := mul_le_mul_of_nonneg_left s23x (by norm_num : (0:ℝ) ≤ (49403/562500:ℝ))
  have h23 : -(484537/2250000:ℝ)*u116-(49403/562500:ℝ)*u162-(41916/80519:ℝ)*f (80519/180000:ℝ) ≤ -1 := by
    nlinarith only [c23,p23y,p23x]
  have c24 := hCert (4501/10000:ℝ) (3629/11250:ℝ) (by norm_num [Admissible])
  norm_num [fullBound] at c24
  have s24y : M (3629/11250:ℝ) (5499/10000:ℝ) ≤ u117 := by simp [u117,le_max_iff]
  have p24y := mul_le_mul_of_nonneg_left s24y (by norm_num : (0:ℝ) ≤ (109061/500000:ℝ))
  have s24x : M (4501/10000:ℝ) (7621/11250:ℝ) ≤ u163 := by simp [u163,le_max_iff]
  have p24x := mul_le_mul_of_nonneg_left s24x (by norm_num : (0:ℝ) ≤ (407699/4500000:ℝ))
  have h24 : -(109061/500000:ℝ)*u117-(407699/4500000:ℝ)*u163-(20459/40509:ℝ)*f (4501/10000:ℝ) ≤ -1 := by
    nlinarith only [c24,p24y,p24x]
  have c25 := hCert (81517/180000:ℝ) (3629/11250:ℝ) (by norm_num [Admissible])
  norm_num [fullBound] at c25
  have s25y : M (3629/11250:ℝ) (98483/180000:ℝ) ≤ u117 := by simp [u117,le_max_iff]
  have p25y := mul_le_mul_of_nonneg_left s25y (by norm_num : (0:ℝ) ≤ (124253/562500:ℝ))
  have s25x : M (81517/180000:ℝ) (7621/11250:ℝ) ≤ u164 := by simp [u164,le_max_iff]
  have p25x := mul_le_mul_of_nonneg_left s25x (by norm_num : (0:ℝ) ≤ (407699/4500000:ℝ))
  have h25 : -(124253/562500:ℝ)*u117-(407699/4500000:ℝ)*u164-(40419/81517:ℝ)*f (81517/180000:ℝ) ≤ -1 := by
    nlinarith only [c25,p25y,p25x]
  have c26 := hCert (2563/5625:ℝ) (3629/11250:ℝ) (by norm_num [Admissible])
  norm_num [fullBound] at c26
  have s26y : M (3629/11250:ℝ) (3062/5625:ℝ) ≤ u117 := by simp [u117,le_max_iff]
  have p26y := mul_le_mul_of_nonneg_left s26y (by norm_num : (0:ℝ) ≤ (1006499/4500000:ℝ))
  have s26x : M (2563/5625:ℝ) (7621/11250:ℝ) ≤ u165 := by simp [u165,le_max_iff]
  have p26x := mul_le_mul_of_nonneg_left s26x (by norm_num : (0:ℝ) ≤ (407699/4500000:ℝ))
  have h26 : -(1006499/4500000:ℝ)*u117-(407699/4500000:ℝ)*u165-(2495/5126:ℝ)*f (2563/5625:ℝ) ≤ -1 := by
    nlinarith only [c26,p26y,p26x]
  have c27 := hCert (22001/45000:ℝ) (29531/90000:ℝ) (by norm_num [Admissible])
  norm_num [fullBound] at c27
  have s27y : M (29531/90000:ℝ) (22999/45000:ℝ) ≤ u119 := by simp [u119,le_max_iff]
  have p27y := mul_le_mul_of_nonneg_left s27y (by norm_num : (0:ℝ) ≤ (1156199/4500000:ℝ))
  have s27x : M (22001/45000:ℝ) (60469/90000:ℝ) ≤ u177 := by simp [u177,le_max_iff]
  have p27x := mul_le_mul_of_nonneg_left s27x (by norm_num : (0:ℝ) ≤ (432649/4500000:ℝ))
  have h27 : -(1156199/4500000:ℝ)*u119-(432649/4500000:ℝ)*u177-(16467/44002:ℝ)*f (22001/45000:ℝ) ≤ -1 := by
    nlinarith only [c27,p27y,p27x]
  have c28 := hCert (89501/180000:ℝ) (29531/90000:ℝ) (by norm_num [Admissible])
  norm_num [fullBound] at c28
  have s28y : M (29531/90000:ℝ) (90499/180000:ℝ) ≤ u119 := by simp [u119,le_max_iff]
  have p28y := mul_le_mul_of_nonneg_left s28y (by norm_num : (0:ℝ) ≤ (149203/562500:ℝ))
  have s28x : M (89501/180000:ℝ) (60469/90000:ℝ) ≤ u180 := by simp [u180,le_max_iff]
  have p28x := mul_le_mul_of_nonneg_left s28x (by norm_num : (0:ℝ) ≤ (432649/4500000:ℝ))
  have h28 : -(149203/562500:ℝ)*u119-(432649/4500000:ℝ)*u180-(31437/89501:ℝ)*f (89501/180000:ℝ) ≤ -1 := by
    nlinarith only [c28,p28y,p28x]
  have c29 := hCert (1/2:ℝ) (6507/20000:ℝ) (by norm_num [Admissible])
  norm_num [fullBound] at c29
  have s29y : M (6507/20000:ℝ) (1/2:ℝ) ≤ u118 := by simp [u118,le_max_iff]
  have p29y := mul_le_mul_of_nonneg_left s29y (by norm_num : (0:ℝ) ≤ (134011/500000:ℝ))
  have s29x : M (1/2:ℝ) (13493/20000:ℝ) ≤ u181 := by simp [u181,le_max_iff]
  have p29x := mul_le_mul_of_nonneg_left s29x (by norm_num : (0:ℝ) ≤ (23343/250000:ℝ))
  have h29 : -(134011/500000:ℝ)*u118-(23343/250000:ℝ)*u181-(3493/10000:ℝ)*f (1/2:ℝ) ≤ -1 := by
    nlinarith only [c29,p29y,p29x]
  have c30 := hCert (18499/36000:ℝ) (3629/11250:ℝ) (by norm_num [Admissible])
  norm_num [fullBound] at c30
  have s30y : M (3629/11250:ℝ) (17501/36000:ℝ) ≤ u117 := by simp [u117,le_max_iff]
  have p30y := mul_le_mul_of_nonneg_left s30y (by norm_num : (0:ℝ) ≤ (634237/2250000:ℝ))
  have s30x : M (18499/36000:ℝ) (7621/11250:ℝ) ≤ u186 := by simp [u186,le_max_iff]
  have p30x := mul_le_mul_of_nonneg_left s30x (by norm_num : (0:ℝ) ≤ (407699/4500000:ℝ))
  have h30 : -(634237/2250000:ℝ)*u117-(407699/4500000:ℝ)*u186-(29441/92495:ℝ)*f (18499/36000:ℝ) ≤ -1 := by
    nlinarith only [c30,p30y,p30x]
  have c31 := hCert (15499/30000:ℝ) (11513/36000:ℝ) (by norm_num [Admissible])
  norm_num [fullBound] at c31
  have s31y : M (11513/36000:ℝ) (14501/30000:ℝ) ≤ u116 := by simp [u116,le_max_iff]
  have p31y := mul_le_mul_of_nonneg_left s31y (by norm_num : (0:ℝ) ≤ (426983/1500000:ℝ))
  have s31x : M (15499/30000:ℝ) (24487/36000:ℝ) ≤ u187 := by simp [u187,le_max_iff]
  have p31x := mul_le_mul_of_nonneg_left s31x (by norm_num : (0:ℝ) ≤ (49403/562500:ℝ))
  have h31 : -(426983/1500000:ℝ)*u116-(49403/562500:ℝ)*u187-(29441/92994:ℝ)*f (15499/30000:ℝ) ≤ -1 := by
    nlinarith only [c31,p31y,p31x]
  have c32 := hCert (93493/180000:ℝ) (11513/36000:ℝ) (by norm_num [Admissible])
  norm_num [fullBound] at c32
  have s32y : M (11513/36000:ℝ) (86507/180000:ℝ) ≤ u116 := by simp [u116,le_max_iff]
  have p32y := mul_le_mul_of_nonneg_left s32y (by norm_num : (0:ℝ) ≤ (80839/281250:ℝ))
  have s32x : M (93493/180000:ℝ) (24487/36000:ℝ) ≤ u188 := by simp [u188,le_max_iff]
  have p32x := mul_le_mul_of_nonneg_left s32x (by norm_num : (0:ℝ) ≤ (49403/562500:ℝ))
  have h32 : -(80839/281250:ℝ)*u116-(49403/562500:ℝ)*u188-(28942/93493:ℝ)*f (93493/180000:ℝ) ≤ -1 := by
    nlinarith only [c32,p32y,p32x]
  have c33 := hCert (10499/20000:ℝ) (56567/180000:ℝ) (by norm_num [Admissible])
  norm_num [fullBound] at c33
  have s33y : M (56567/180000:ℝ) (9501/20000:ℝ) ≤ u114 := by simp [u114,le_max_iff]
  have p33y := mul_le_mul_of_nonneg_left s33y (by norm_num : (0:ℝ) ≤ (73243/250000:ℝ))
  have s33x : M (10499/20000:ℝ) (123433/180000:ℝ) ≤ u190 := by simp [u190,le_max_iff]
  have p33x := mul_le_mul_of_nonneg_left s33x (by norm_num : (0:ℝ) ≤ (185137/2250000:ℝ))
  have h33 : -(73243/250000:ℝ)*u114-(185137/2250000:ℝ)*u190-(28942/94491:ℝ)*f (10499/20000:ℝ) ≤ -1 := by
    nlinarith only [c33,p33y,p33x]
  have c34 := hCert (9499/18000:ℝ) (56567/180000:ℝ) (by norm_num [Admissible])
  norm_num [fullBound] at c34
  have s34y : M (56567/180000:ℝ) (8501/18000:ℝ) ≤ u114 := by simp [u114,le_max_iff]
  have p34y := mul_le_mul_of_nonneg_left s34y (by norm_num : (0:ℝ) ≤ (1330849/4500000:ℝ))
  have s34x : M (9499/18000:ℝ) (123433/180000:ℝ) ≤ u191 := by simp [u191,le_max_iff]
  have p34x := mul_le_mul_of_nonneg_left s34x (by norm_num : (0:ℝ) ≤ (185137/2250000:ℝ))
  have h34 : -(1330849/4500000:ℝ)*u114-(185137/2250000:ℝ)*u191-(28443/94990:ℝ)*f (9499/18000:ℝ) ≤ -1 := by
    nlinarith only [c34,p34y,p34x]
  have c35 := hCert (95489/180000:ℝ) (56567/180000:ℝ) (by norm_num [Admissible])
  norm_num [fullBound] at c35
  have s35y : M (56567/180000:ℝ) (84511/180000:ℝ) ≤ u114 := by simp [u114,le_max_iff]
  have p35y := mul_le_mul_of_nonneg_left s35y (by norm_num : (0:ℝ) ≤ (335831/1125000:ℝ))
  have s35x : M (95489/180000:ℝ) (123433/180000:ℝ) ≤ u192 := by simp [u192,le_max_iff]
  have p35x := mul_le_mul_of_nonneg_left s35x (by norm_num : (0:ℝ) ≤ (185137/2250000:ℝ))
  have h35 : -(335831/1125000:ℝ)*u114-(185137/2250000:ℝ)*u192-(27944/95489:ℝ)*f (95489/180000:ℝ) ≤ -1 := by
    nlinarith only [c35,p35y,p35x]
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
  have b16 : 0 ≤ u84 := by
    have hh := (hM (115989/500000:ℝ) (1999/3000:ℝ) (by norm_num) (by norm_num) (by norm_num)).1
    have hs : M (115989/500000:ℝ) (1999/3000:ℝ) ≤ u84 := by simp [u84,le_max_iff]
    exact hh.trans hs
  have b17 : u111 ≤ (18000/5507:ℝ) := by
    dsimp only [u111]
    convert ((hM (5507/18000:ℝ) (11497/20000:ℝ) (by norm_num) (by norm_num) (by norm_num)).2) using 1 <;> norm_num
  have b18 : u114 ≤ (180000/56567:ℝ) := by
    dsimp only [u114]
    convert (max_le ((hM (56567/180000:ℝ) (84511/180000:ℝ) (by norm_num) (by norm_num) (by norm_num)).2) (max_le ((hM (56567/180000:ℝ) (8501/18000:ℝ) (by norm_num) (by norm_num) (by norm_num)).2) ((hM (56567/180000:ℝ) (9501/20000:ℝ) (by norm_num) (by norm_num) (by norm_num)).2))) using 1 <;> norm_num
  have b19 : 0 ≤ u116 := by
    have hh := (hM (11513/36000:ℝ) (86507/180000:ℝ) (by norm_num) (by norm_num) (by norm_num)).1
    have hs : M (11513/36000:ℝ) (86507/180000:ℝ) ≤ u116 := by simp [u116,le_max_iff]
    exact hh.trans hs
  have b20 : u117 ≤ (11250/3629:ℝ) := by
    dsimp only [u117]
    convert (max_le ((hM (3629/11250:ℝ) (17501/36000:ℝ) (by norm_num) (by norm_num) (by norm_num)).2) (max_le ((hM (3629/11250:ℝ) (3062/5625:ℝ) (by norm_num) (by norm_num) (by norm_num)).2) (max_le ((hM (3629/11250:ℝ) (98483/180000:ℝ) (by norm_num) (by norm_num) (by norm_num)).2) ((hM (3629/11250:ℝ) (5499/10000:ℝ) (by norm_num) (by norm_num) (by norm_num)).2)))) using 1 <;> norm_num
  have b21 : u118 ≤ (20000/6507:ℝ) := by
    dsimp only [u118]
    convert ((hM (6507/20000:ℝ) (1/2:ℝ) (by norm_num) (by norm_num) (by norm_num)).2) using 1 <;> norm_num
  have b22 : 0 ≤ u119 := by
    have hh := (hM (29531/90000:ℝ) (90499/180000:ℝ) (by norm_num) (by norm_num) (by norm_num)).1
    have hs : M (29531/90000:ℝ) (90499/180000:ℝ) ≤ u119 := by simp [u119,le_max_iff]
    exact hh.trans hs
  have b23 : 0 ≤ u154 := by
    have hh := (hM (8503/20000:ℝ) (12493/18000:ℝ) (by norm_num) (by norm_num) (by norm_num)).1
    have hs : M (8503/20000:ℝ) (12493/18000:ℝ) ≤ u154 := by simp [u154,le_max_iff]
    exact hh.trans hs
  have b24 : 0 ≤ u162 := by
    have hh := (hM (80519/180000:ℝ) (24487/36000:ℝ) (by norm_num) (by norm_num) (by norm_num)).1
    have hs : M (80519/180000:ℝ) (24487/36000:ℝ) ≤ u162 := by simp [u162,le_max_iff]
    exact hh.trans hs
  have b25 : 0 ≤ u163 := by
    have hh := (hM (4501/10000:ℝ) (7621/11250:ℝ) (by norm_num) (by norm_num) (by norm_num)).1
    have hs : M (4501/10000:ℝ) (7621/11250:ℝ) ≤ u163 := by simp [u163,le_max_iff]
    exact hh.trans hs
  have b26 : 0 ≤ u164 := by
    have hh := (hM (81517/180000:ℝ) (7621/11250:ℝ) (by norm_num) (by norm_num) (by norm_num)).1
    have hs : M (81517/180000:ℝ) (7621/11250:ℝ) ≤ u164 := by simp [u164,le_max_iff]
    exact hh.trans hs
  have b27 : 0 ≤ u165 := by
    have hh := (hM (2563/5625:ℝ) (7621/11250:ℝ) (by norm_num) (by norm_num) (by norm_num)).1
    have hs : M (2563/5625:ℝ) (7621/11250:ℝ) ≤ u165 := by simp [u165,le_max_iff]
    exact hh.trans hs
  have b28 : u177 ≤ (45000/22001:ℝ) := by
    dsimp only [u177]
    convert ((hM (22001/45000:ℝ) (60469/90000:ℝ) (by norm_num) (by norm_num) (by norm_num)).2) using 1 <;> norm_num
  have b29 : u180 ≤ (180000/89501:ℝ) := by
    dsimp only [u180]
    convert ((hM (89501/180000:ℝ) (60469/90000:ℝ) (by norm_num) (by norm_num) (by norm_num)).2) using 1 <;> norm_num
  have b30 : u181 ≤ (2/1:ℝ) := by
    dsimp only [u181]
    convert ((hM (1/2:ℝ) (13493/20000:ℝ) (by norm_num) (by norm_num) (by norm_num)).2) using 1 <;> norm_num
  have b31 : 0 ≤ u186 := by
    have hh := (hM (18499/36000:ℝ) (7621/11250:ℝ) (by norm_num) (by norm_num) (by norm_num)).1
    have hs : M (18499/36000:ℝ) (7621/11250:ℝ) ≤ u186 := by simp [u186,le_max_iff]
    exact hh.trans hs
  have b32 : 0 ≤ u187 := by
    have hh := (hM (15499/30000:ℝ) (24487/36000:ℝ) (by norm_num) (by norm_num) (by norm_num)).1
    have hs : M (15499/30000:ℝ) (24487/36000:ℝ) ≤ u187 := by simp [u187,le_max_iff]
    exact hh.trans hs
  have b33 : 0 ≤ u188 := by
    have hh := (hM (93493/180000:ℝ) (24487/36000:ℝ) (by norm_num) (by norm_num) (by norm_num)).1
    have hs : M (93493/180000:ℝ) (24487/36000:ℝ) ≤ u188 := by simp [u188,le_max_iff]
    exact hh.trans hs
  have b34 : 0 ≤ u190 := by
    have hh := (hM (10499/20000:ℝ) (123433/180000:ℝ) (by norm_num) (by norm_num) (by norm_num)).1
    have hs : M (10499/20000:ℝ) (123433/180000:ℝ) ≤ u190 := by simp [u190,le_max_iff]
    exact hh.trans hs
  have b35 : u191 ≤ (18000/9499:ℝ) := by
    dsimp only [u191]
    convert ((hM (9499/18000:ℝ) (123433/180000:ℝ) (by norm_num) (by norm_num) (by norm_num)).2) using 1 <;> norm_num
  have b36 : u192 ≤ (180000/95489:ℝ) := by
    dsimp only [u192]
    convert ((hM (95489/180000:ℝ) (123433/180000:ℝ) (by norm_num) (by norm_num) (by norm_num)).2) using 1 <;> norm_num
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,b26,b27,b28,b29,b30,b31,b32,b33,b34,b35,b36]
#print axioms full_scalar_criterion_obstruction
end TypedTriangle.Completion.FullMDualObstruction
