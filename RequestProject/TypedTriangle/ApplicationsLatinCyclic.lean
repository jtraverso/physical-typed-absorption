module
public import RequestProject.TypedTriangle.ApplicationsLatinCore
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Applications.Latin

def LatinSquare.transport {A B : Type} (L : LatinSquare B) (e : A ≃ B) : LatinSquare A where
  toFun x y := e.symm (L (e x) (e y))
  row_bijective x := e.symm.bijective.comp ((L.row_bijective (e x)).comp e.bijective)
  column_bijective y := e.symm.bijective.comp ((L.column_bijective (e y)).comp e.bijective)

/-- The cyclic Latin square transported to an arbitrary nonempty finite alphabet. -/
def LatinSquare.cyclic (A : Type) [Fintype A] [Nonempty A] : LatinSquare A := by
  letI : NeZero (Fintype.card A) := ⟨Fintype.card_ne_zero⟩
  let e : A ≃ ZMod (Fintype.card A) := Fintype.equivOfCardEq (by simp)
  exact (LatinSquare.add (ZMod (Fintype.card A))).transport e

theorem cyclic_isPhysical (A : Type) [Fintype A] [Nonempty A] :
    IsPhysical (host A) types (edges (host A)) :=
  isPhysical_of_isDecomposition (decomposition_exact (LatinSquare.cyclic A))

#print axioms cyclic_isPhysical
end TypedTriangle.Applications.Latin
