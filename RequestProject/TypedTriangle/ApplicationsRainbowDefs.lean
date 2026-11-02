module
public import RequestProject.TypedTriangle.Basic
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Applications.Rainbow

/-- Complete multipartite host with equally sized labelled parts. -/
def host (k : ℕ) (A : Type) : Host (Fin k × A) (Fin k) where
  G := {
    Adj := fun u v => u.1 ≠ v.1
    symm := ⟨fun _ _ h => h.symm⟩
    loopless := ⟨fun _ h => h rfl⟩ }
  lab := Prod.fst

/-- The allowed label multisets have no repeated colour. -/
def types (k : ℕ) : Set (Multiset (Fin k)) := {s | s.Nodup}

@[simp] theorem host_adj {k : ℕ} {A : Type} (u v : Fin k × A) :
    (host k A).G.Adj u v ↔ u.1 ≠ v.1 := Iff.rfl

@[simp] theorem host_lab {k : ℕ} {A : Type} (u : Fin k × A) :
    (host k A).lab u = u.1 := rfl

@[simp] theorem mem_types {k : ℕ} (s : Multiset (Fin k)) :
    s ∈ types k ↔ s.Nodup := Iff.rfl

end TypedTriangle.Applications.Rainbow
