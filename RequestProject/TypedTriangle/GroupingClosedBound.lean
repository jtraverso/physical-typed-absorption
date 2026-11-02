module
public import RequestProject.TypedTriangle.GroupingExplicitBound
@[expose] public section
namespace TypedTriangle.GroupingExplicit

/-- A closed elementary majorant of the dimension-recursive kernel bound. -/
theorem kernelBound_le_power (d D : ℕ) :
    kernelBound d D ≤ (2 * D + 1) ^ (2 ^ d - 1) := by
  induction d generalizing D with
  | zero => simp [kernelBound]
  | succ d ih =>
      have hrad : 2 * (D * (2 * D + 1)) + 1 ≤ (2 * D + 1) ^ 2 := by nlinarith
      calc
        kernelBound (d + 1) D = (2 * D + 1) * kernelBound d (D * (2 * D + 1)) := rfl
        _ ≤ (2 * D + 1) * (2 * (D * (2 * D + 1)) + 1) ^ (2 ^ d - 1) :=
          Nat.mul_le_mul_left _ (ih _)
        _ ≤ (2 * D + 1) * ((2 * D + 1) ^ 2) ^ (2 ^ d - 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hrad (2 ^ d - 1))
        _ = (2 * D + 1) ^ (2 ^ (d + 1) - 1) := by
          rw [← pow_mul, ← pow_succ']
          congr 1
          rw [pow_succ]
          have hp : 0 < 2 ^ d := by positivity
          omega

end TypedTriangle.GroupingExplicit
namespace TypedTriangle.Grouping

theorem groupBound_le_power (d B R : ℕ) :
    groupBound d B R ≤ (2 * max B R + 1) ^ (2 ^ d - 1) :=
  (groupBound_le_explicit d B R).trans (GroupingExplicit.kernelBound_le_power d (max B R))

#print axioms groupBound_le_power
end TypedTriangle.Grouping
