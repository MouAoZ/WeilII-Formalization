module

public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Natural isomorphisms between functors into inverse sequences -/

@[expose] public section

open CategoryTheory Opposite

namespace WeilII

/-- Vertex isomorphisms natural in the parameter assemble into an isomorphism of tower
functors when they commute with the successor arrows. Apply `NatTrans.ofOpSequence` in the
functor category, check invertibility there at every index, and flip the two arguments. -/
noncomputable def inverseSequenceFunctorIso {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ ℕᵒᵖ ⥤ D} (e : ∀ n : ℕ, F.flip.obj (op n) ≅ G.flip.obj (op n))
    (h : ∀ (n : ℕ) (M : C),
      (F.obj M).map (homOfLE n.le_succ).op ≫ (e n).hom.app M =
        (e (n+1)).hom.app M ≫ (G.obj M).map (homOfLE n.le_succ).op) : F ≅ G := by
  let t : F.flip ⟶ G.flip :=
    NatTrans.ofOpSequence (fun n ↦ (e n).hom) fun n ↦ NatTrans.ext (funext (h n))
  have (n : ℕᵒᵖ) : IsIso (t.app n) := inferInstanceAs (IsIso (e n.unop).hom)
  have := NatIso.isIso_of_isIso_app t
  exact (flipFunctor ℕᵒᵖ C D).mapIso (asIso t)

end WeilII
