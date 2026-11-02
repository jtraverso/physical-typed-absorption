module
public import RequestProject.TypedTriangle.ApplicationsLatinPaschClassification
public import RequestProject.TypedTriangle.ApplicationsLatinPaschAlgebra
public import RequestProject.TypedTriangle.ApplicationsLatinProfile
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Applications.Latin

theorem allowed_eq_image {A : Type} [Fintype A] :
    allowed (host A) types=(univ : Finset (A×A×A)).image
      (fun p => latinTriangle p.1 p.2.1 p.2.2) := by
  ext Q
  simp only [allowed,mem_filter,mem_univ,true_and,mem_image,Prod.exists]
  constructor
  · intro hQ
    obtain ⟨r,c,s,h⟩ := (allowed_iff Q).mp hQ
    exact ⟨r,c,s,h.symm⟩
  · rintro ⟨r,c,s,rfl⟩
    exact latinTriangle_allowed r c s

theorem card_allowed {A : Type} [Fintype A] :
    (allowed (host A) types).card=(Fintype.card A)^3 := by
  have hInj : Function.Injective (fun p : A×A×A => latinTriangle p.1 p.2.1 p.2.2) := by
    intro p q h
    obtain ⟨hR,hC,hS⟩ := (latinTriangle_eq_iff _ _ _ _ _ _).mp h
    exact Prod.ext hR (Prod.ext hC hS)
  rw [allowed_eq_image,card_image_of_injective _ hInj]
  simp [pow_succ,Nat.mul_assoc]

/-- Every actual unordered Pasch has exactly four rooted incidences. -/
theorem sum_rootedCount {V : Type} [DecidableEq V] (D : Finset (Finset V)) :
    (∑ Q∈D, Pasch.rootedCount D Q)=4*Pasch.count D := by
  have hr (Q : Finset V) : Pasch.rootedCount D Q =
      ∑ S∈Pasch.configurations D, if Q∈S then 1 else 0 := by
    simp only [Pasch.rootedCount,card_eq_sum_ones,sum_filter]
  simp_rw [hr]
  rw [sum_comm]
  have hs (S) (hS : S∈Pasch.configurations D) :
      (∑ Q∈D, if Q∈S then 1 else 0)=4 := by
    have hSub := (Pasch.mem_configurations.mp hS).1
    have hFilter : D.filter (fun Q => Q∈S)=S := by
      ext Q
      simp only [mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨hSub h,h⟩⟩
    rw [←sum_filter,hFilter]
    simpa using (Pasch.mem_configurations.mp hS).2.1
  calc
    _ = ∑ S∈Pasch.configurations D,4 := sum_congr rfl hs
    _ = 4*Pasch.count D := by simp [Pasch.count,Nat.mul_comm]

theorem four_mul_count_allowed {A : Type} [Fintype A] :
    4*Pasch.count (allowed (host A) types)=
      (Fintype.card A)^3*(Fintype.card A-1)^3 := by
  rw [←sum_rootedCount]
  have hr Q (hQ : Q∈allowed (host A) types) :
      Pasch.rootedCount (allowed (host A) types) Q=(Fintype.card A-1)^3 := by
    obtain ⟨r,c,s,rfl⟩ := (allowed_iff Q).mp (isAllowed_of_mem_allowed hQ)
    exact rootedCount_allowed r c s
  rw [sum_congr rfl hr]
  simp [card_allowed]

theorem target_constant_eq_count {V : Type} [DecidableEq V]
    (a : ℝ) (D : Finset (Finset V)) :
    Pasch.target (fun _ => a) D=(Pasch.count D : ℝ)*a^4 := by
  rw [Pasch.target,Pasch.statistic_eq_sum]
  have hp S (hS : S∈Pasch.configurations D) : (∏ Q∈S,a)=a^4 := by
    simp only [prod_const,(Pasch.mem_configurations.mp hS).2.1]
  rw [sum_congr rfl hp]
  simp [Pasch.count]

/-- The exact finite-order target, with the correction terms retained. -/
theorem uniform_target {A : Type} [Fintype A] [Nonempty A] :
    Pasch.target (fun _ : Finset (Vertex A) => 1/(Fintype.card A : ℝ))
      (allowed (host A) types)=
        ((Fintype.card A : ℝ)-1)^3/(4*(Fintype.card A : ℝ)) := by
  have hn : 0 < (Fintype.card A : ℝ) := by exact_mod_cast (Fintype.card_pos (α:=A))
  have hnNat : 1 ≤ Fintype.card A := Fintype.card_pos
  have hc : 4*(Pasch.count (allowed (host A) types) : ℝ)=
      (Fintype.card A : ℝ)^3*((Fintype.card A : ℝ)-1)^3 := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_sub hnNat,Nat.cast_one]
      using congrArg (fun x : ℕ => (x : ℝ)) (four_mul_count_allowed (A:=A))
  have hc' : (Pasch.count (allowed (host A) types) : ℝ)=
      (Fintype.card A : ℝ)^3*((Fintype.card A : ℝ)-1)^3/4 := by linarith only [hc]
  rw [target_constant_eq_count]
  rw [hc']
  field_simp [ne_of_gt hn] <;> ring

theorem uniform_target_choose {A : Type} [Fintype A] [Nonempty A] :
    Pasch.target (fun _ : Finset (Vertex A) => 1/(Fintype.card A : ℝ))
      (allowed (host A) types)=
        2*((Fintype.card A).choose 2 : ℝ)^3/(Fintype.card A : ℝ)^4 := by
  rw [uniform_target,Nat.cast_choose_two]
  have hn : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hn]
  ring

theorem target_congr_on {V : Type} [DecidableEq V]
    (μ ψ : Finset V → ℝ) (D : Finset (Finset V)) (h : ∀ Q∈D,μ Q=ψ Q) :
    Pasch.target μ D=Pasch.target ψ D := by
  simp only [Pasch.target,Pasch.statistic_eq_sum]
  apply sum_congr rfl
  intro S hS
  apply prod_congr rfl
  intro Q hQ
  exact h Q ((Pasch.mem_configurations.mp hS).1 hQ)

theorem uniform_weight_target {A : Type} [Fintype A] [Nonempty A] :
    Pasch.target (weight (fun _ _ _ : A => 1/(Fintype.card A : ℝ)))
      (allowed (host A) types)=
        ((Fintype.card A : ℝ)-1)^3/(4*(Fintype.card A : ℝ)) := by
  rw [target_congr_on (weight (fun _ _ _ : A => 1/(Fintype.card A : ℝ)))
    (fun _ => 1/(Fintype.card A : ℝ)) (allowed (host A) types) (by
      intro Q hQ
      obtain ⟨r,c,s,rfl⟩ := (allowed_iff Q).mp (isAllowed_of_mem_allowed hQ)
      exact weight_triangle _ r c s)]
  exact uniform_target

theorem prod_latinPasch {A : Type} (μ : Finset (Vertex A) → ℝ)
    {r r' c c' s s' : A} (hr : r'≠r) (hc : c'≠c) (hs : s'≠s) :
    (∏ Q∈latinPasch r r' c c' s s',μ Q)=
      μ (latinTriangle r c s)*μ (latinTriangle r c' s')*
        μ (latinTriangle r' c s')*μ (latinTriangle r' c' s) := by
  simp [latinPasch,latinTriangle_eq_iff,hr,hc,hs,Ne.symm hr,Ne.symm hc,Ne.symm hs]
  ring

theorem four_mul_target_eq_rooted {V : Type} [DecidableEq V]
    (μ : Finset V → ℝ) (D : Finset (Finset V)) :
    4*Pasch.target μ D =
      ∑ Q∈D,∑ S∈(Pasch.configurations D).filter (fun S => Q∈S),∏ T∈S,μ T := by
  symm
  calc
    _ = ∑ S∈Pasch.configurations D,∑ Q∈D,if Q∈S then ∏ T∈S,μ T else 0 := by
      simp_rw [sum_filter]
      rw [sum_comm]
    _ = ∑ S∈Pasch.configurations D,4*(∏ T∈S,μ T) := by
      apply sum_congr rfl
      intro S hS
      have hSub := (Pasch.mem_configurations.mp hS).1
      have hFilter : D.filter (fun Q => Q∈S)=S := by
        ext Q
        simp only [mem_filter]
        exact ⟨fun h => h.2,fun h => ⟨hSub h,h⟩⟩
      rw [←sum_filter,hFilter,sum_const,(Pasch.mem_configurations.mp hS).2.1]
      simp
    _ = _ := by rw [Pasch.target,Pasch.statistic_eq_sum,mul_sum]

theorem rooted_target_sum {A : Type} [Fintype A]
    (p : A → A → A → ℝ) (r c s : A) :
    (∑ S∈(Pasch.configurations (allowed (host A) types)).filter
      (fun S => latinTriangle r c s∈S),∏ T∈S,weight p T) =
      ∑ r'∈(univ : Finset A).erase r,∑ c'∈(univ : Finset A).erase c,
        ∑ s'∈(univ : Finset A).erase s,
          p r c s*p r c' s'*p r' c s'*p r' c' s := by
  rw [rooted_configurations_eq_image,sum_image]
  · have hProd q (hq : q∈rootedAlternatives r c s) :
        (∏ T∈latinPasch r q.1 c q.2.1 s q.2.2,weight p T)=
          p r c s*p r q.2.1 q.2.2*p q.1 c q.2.2*p q.1 q.2.1 s := by
      obtain ⟨hr,hc,hs⟩ := (mem_rootedAlternatives r c s q).mp hq
      simpa only [weight_triangle] using prod_latinPasch (weight p) hr hc hs
    rw [sum_congr rfl hProd]
    dsimp only [rootedAlternatives]
    simp only [Finset.product_eq_sprod]
    rw [Finset.sum_product' (univ.erase r) ((univ.erase c) ×ˢ (univ.erase s))
      (fun r' (z : A×A) => p r c s*p r z.1 z.2*p r' c z.2*p r' z.1 s)]
    apply sum_congr rfl
    intro r' _
    exact Finset.sum_product' (univ.erase c) (univ.erase s)
      (fun c' s' => p r c s*p r c' s'*p r' c s'*p r' c' s)
  · exact rootedAlternatives_injective r c s

theorem root_first_sum_eq_pair_sums {A : Type} [Fintype A]
    (f : A → A → A → A → A → A → ℝ) :
    (∑ r,∑ c,∑ s,∑ r'∈(univ : Finset A).erase r,
      ∑ c'∈(univ : Finset A).erase c,∑ s'∈(univ : Finset A).erase s,
        f r r' c c' s s') =
      distinctPairSum (fun r r' => distinctPairSum (fun c c' =>
        distinctPairSum (fun s s' => f r r' c c' s s'))) := by
  symm
  unfold distinctPairSum
  apply sum_congr rfl
  intro r _
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  have hSwap r' :
      (∑ c'∈(univ : Finset A).erase c,∑ s,∑ s'∈(univ : Finset A).erase s,f r r' c c' s s')=
      ∑ s,∑ c'∈(univ : Finset A).erase c,∑ s'∈(univ : Finset A).erase s,f r r' c c' s s' := by
    rw [sum_comm]
  simp_rw [hSwap]
  rw [sum_comm]

theorem four_mul_signed_target {A : Type} [Fintype A]
    (θ : ℝ) (σ τ υ : A → ℝ) :
    4*Pasch.target (weight (fun r c s =>
      (1+θ*σ r*τ c*υ s)/(Fintype.card A : ℝ))) (allowed (host A) types)=
        signedBoxSum θ σ τ υ/(Fintype.card A : ℝ)^4 := by
  rw [four_mul_target_eq_rooted,sum_allowed_eq]
  simp_rw [rooted_target_sum]
  rw [root_first_sum_eq_pair_sums]
  have hp r r' c c' s s' :
      ((1+θ*σ r*τ c*υ s)/(Fintype.card A : ℝ))*
        ((1+θ*σ r*τ c'*υ s')/(Fintype.card A : ℝ))*
        ((1+θ*σ r'*τ c*υ s')/(Fintype.card A : ℝ))*
        ((1+θ*σ r'*τ c'*υ s)/(Fintype.card A : ℝ)) =
      ((1+θ*σ r*τ c*υ s)*(1+θ*σ r*τ c'*υ s')*
        (1+θ*σ r'*τ c*υ s')*(1+θ*σ r'*τ c'*υ s))/(Fintype.card A : ℝ)^4 := by ring
  simp_rw [hp]
  simp only [div_eq_mul_inv,distinctPairSum_mul_right,signedBoxSum]

/-- Exact Pasch target of a balanced rank-one perturbation of the
uniform three-dimensional stochastic array. -/
theorem balanced_signed_target {A : Type} [Fintype A] [Nonempty A]
    (θ : ℝ) (σ τ υ : A → ℝ)
    (hσ : ∑ x,σ x=0) (hτ : ∑ x,τ x=0) (hυ : ∑ x,υ x=0)
    (hσ2 : ∀ x,(σ x)^2=1) (hτ2 : ∀ x,(τ x)^2=1) (hυ2 : ∀ x,(υ x)^2=1) :
    Pasch.target (weight (fun r c s => (1+θ*σ r*τ c*υ s)/(Fintype.card A : ℝ)))
      (allowed (host A) types)=
        (1+θ^4)*((Fintype.card A : ℝ)-1)^3/(4*(Fintype.card A : ℝ))+
          3*θ^2*((Fintype.card A : ℝ)-1)/(2*(Fintype.card A : ℝ)) := by
  have h := four_mul_signed_target θ σ τ υ
  rw [balanced_signedBoxSum θ σ τ υ hσ hτ hυ hσ2 hτ2 hυ2] at h
  have hn : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let n : ℝ := Fintype.card A
  let z := Pasch.target (weight (fun r c s => (1+θ*σ r*τ c*υ s)/n))
    (allowed (host A) types)
  change 4*z=((1+θ^4)*n^3*(n-1)^3+6*θ^2*n^3*(n-1))/n^4 at h
  change z=(1+θ^4)*(n-1)^3/(4*n)+3*θ^2*(n-1)/(2*n)
  have hn' : n≠0 := hn
  have hClear := (eq_div_iff (pow_ne_zero 4 hn')).mp h
  calc
    z = ((1+θ^4)*n^3*(n-1)^3+6*θ^2*n^3*(n-1))/(4*n^4) := by
      apply (eq_div_iff (mul_ne_zero (by norm_num : (4:ℝ)≠0) (pow_ne_zero 4 hn'))).mpr
      convert hClear using 1 <;> ring
    _ = _ := by field_simp [hn']; ring

#print axioms four_mul_count_allowed
#print axioms uniform_target
#print axioms uniform_target_choose
#print axioms uniform_weight_target
#print axioms four_mul_signed_target
#print axioms balanced_signed_target
end TypedTriangle.Applications.Latin
