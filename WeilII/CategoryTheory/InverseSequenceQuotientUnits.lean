module

public import WeilII.CategoryTheory.InverseSequenceFunctorIso
public import Mathlib.CategoryTheory.Whiskering

/-! # Pullback comparisons for inverse sequences of quotients -/

public section

open CategoryTheory Opposite

namespace WeilII

/-- For towers of quotients, a comparison preserving the quotient maps commutes with
the transitions. Precompose each successor square with the epic quotient map. -/
theorem inverseSequencePullbackOfUnits {C D : Type*} [Category* C] [Category* D]
    (U : C ⥤ D) {A : ℕ → C ⥤ C} {B : ℕ → D ⥤ D}
    (a : ∀ n, A (n+1) ⟶ A n) (b : ∀ n, B (n+1) ⟶ B n)
    (p : ∀ n, 𝟭 C ⟶ A n) (q : ∀ n, 𝟭 D ⟶ B n) (e : ∀ n, U ⋙ B n ≅ A n ⋙ U)
    (ha : ∀ n M, (p (n+1)).app M ≫ (a n).app M = (p n).app M)
    (hb : ∀ n M, (q (n+1)).app M ≫ (b n).app M = (q n).app M)
    (hq : ∀ n M, Epi ((q (n+1)).app (U.obj M)))
    (he : ∀ n M, (q n).app (U.obj M) ≫ (e n).hom.app M = U.map ((p n).app M)) :
    ∃ t : U ⋙ (Functor.ofOpSequence b).flip ≅
        (Functor.ofOpSequence a).flip ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj U,
      ∀ (M : C) (n : ℕ), (t.hom.app M).app (op n) = (e n).hom.app M := by
  refine ⟨inverseSequenceFunctorIso e (fun n M ↦ ?_), fun _ _ ↦ rfl⟩
  dsimp only [Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.comp_map,
    Functor.flip_obj_map]
  rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ]
  change (b n).app (U.obj M) ≫ (e n).hom.app M =
    (e (n+1)).hom.app M ≫ U.map ((a n).app M)
  apply (cancel_epi ((q (n+1)).app (U.obj M))).mp
  erw [← Category.assoc, hb, he, ← Category.assoc, he, ← U.map_comp, ha]

end WeilII
