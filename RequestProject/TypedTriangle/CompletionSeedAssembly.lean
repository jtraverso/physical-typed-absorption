module
public import RequestProject.TypedTriangle.CompletionFiniteRegularization
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Completion

def edgeLoad {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) :
    (Finset V → ℝ) →ₗ[ℝ] ({e : Sym2 V // e ∈ H.G.edgeSet} → ℝ) where
  toFun φ e := ∑ T ∈ (allowed H F).filter (fun T => e.val ∈ triEdges T), φ T
  map_add' φ ψ := by ext e; simp [sum_add_distrib]
  map_smul' c φ := by ext e; simp [mul_sum]

/-- Finite packing data needed from the sampling/circulation construction.
This is an explicit intermediate theorem interface, not a claimed theorem
from an external paper and not an axiom. Its production remains an input. -/
structure FiniteSeedData {V I : Type} [Fintype V] (H : Host V I)
    (F : Set (Multiset I)) (n a z A : ℝ) where
  length : ℕ
  packing : ℕ → Finset V → ℝ
  terminal : Finset V → ℝ
  residual : ℕ → {e : Sym2 V // e ∈ H.G.edgeSet} → ℝ
  initial : residual 0=(1/(1-a)) • ((fun _ => 1)-edgeLoad H F (fun _ => a/n))
  recurrence : ∀ i < length, edgeLoad H F (packing i)=2 • residual i-residual (i+1)
  terminal_exact : edgeLoad H F terminal=residual length
  packing_nonneg : ∀ i < length, ∀ T, 0 ≤ packing i T
  terminal_nonneg : ∀ T, 0 ≤ terminal T
  packing_bound : ∀ i < length, ∀ T, packing i T ≤ (1+z)*A*((i:ℝ)+1)^8/n
  terminal_bound : ∀ T, terminal T ≤ 1+z
  terminal_scale : 1/(2:ℝ)^length ≤ 1/n

theorem diffuseSeed_of_finiteData {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (n a z A C : ℝ)
    (hn : 0 < n) (ha : 0 ≤ a) (haOne : a < 1) (hz : 0 ≤ z) (hA : 0 ≤ A)
    (data : FiniteSeedData H F n a z A)
    (hLower : 1/(C*Fintype.card V) ≤ a/n)
    (hUpper : a/n+(1+z)*(1+A*1091670)/n ≤ C/Fintype.card V) :
    ∃ μ : Finset V → ℝ, IsDiffuseSeed H F C μ := by
  let Ψ := finiteRegularization data.length data.packing data.terminal
  let base : Finset V → ℝ := fun _ => a/n
  let μ := base+(1-a) • Ψ
  have hΨExact : edgeLoad H F Ψ=data.residual 0 :=
    finiteRegularization_exact (edgeLoad H F) data.length data.packing data.terminal
      data.residual data.recurrence data.terminal_exact
  have hμExact : edgeLoad H F μ=(fun _ => 1) := by
    apply add_floor_exact (edgeLoad H F) base Ψ (fun _ => 1) a
    · exact hΨExact.trans data.initial
    · exact ne_of_lt haOne
  have hΨNonneg : ∀ T,0 ≤ Ψ T := finiteRegularization_nonneg data.length
    data.packing data.terminal data.packing_nonneg data.terminal_nonneg
  have hΨUpper : ∀ T, Ψ T ≤ (1+z)*(1+A*1091670)/n :=
    finiteRegularization_bound data.length data.packing data.terminal n A z
      hn hA hz data.terminal_scale data.packing_bound data.terminal_bound
  refine ⟨μ,?_,?_⟩
  · intro T _
    have hLow : a/n ≤ μ T := by
      change a/n ≤ a/n+(1-a)*Ψ T
      have hh := mul_nonneg (sub_nonneg.mpr haOne.le) (hΨNonneg T)
      linarith only [hh]
    have hHigh : μ T ≤ a/n+(1+z)*(1+A*1091670)/n := by
      change a/n+(1-a)*Ψ T ≤ _
      have hh := mul_nonneg ha (hΨNonneg T)
      nlinarith only [hh,hΨUpper T]
    exact ⟨hLower.trans hLow,hHigh.trans hUpper⟩
  · intro e he
    exact congrFun hμExact ⟨e,he⟩

/-- Concrete improved constant C=10^55, conditional only on the displayed
finite packing data. No positivity or exactness obligation is hidden. -/
theorem diffuseSeed_concrete {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (n : ℝ) (hn : 0 < n)
    (hOrder : (Fintype.card V : ℝ)=3*n)
    (data : FiniteSeedData H F n (1/800000000) (1/100000000) regularizationCoefficient) :
    ∃ μ : Finset V → ℝ, IsDiffuseSeed H F (10^55) μ := by
  apply diffuseSeed_of_finiteData H F n (1/800000000) (1/100000000)
    regularizationCoefficient (10^55) hn (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [regularizationCoefficient]) data
  · rw [hOrder]
    have hh := mul_le_mul_of_nonneg_right seed_constant_improvement.2
      (le_of_lt (one_div_pos.mpr hn))
    convert hh using 1 <;> ring
  · rw [hOrder]
    have hh := mul_le_mul_of_nonneg_right seed_constant_improvement.1.le
      (le_of_lt (one_div_pos.mpr hn))
    convert hh using 1 <;> ring

#print axioms diffuseSeed_of_finiteData
#print axioms diffuseSeed_concrete
end TypedTriangle.Completion
