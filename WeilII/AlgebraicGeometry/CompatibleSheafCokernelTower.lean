module

public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldModuleSheafEquivalenceLift

/-!
# Transitions and cone legs from scalar-linear cokernel projections

The constructions use `ResidueFieldModuleSheafEquivalenceLift` and mathlib's `Functor.OfSequence`.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilII

universe w v u

/-- Scalar-linear cokernel projections to the underlying sheaves of a fully faithful functor
assemble into a tower when each next relation dies under the previous projection.
The transition factors the lower projection through the higher cokernel. Cancellation of that
epimorphism gives scalar linearity and the map descends by full faithfulness. -/
public theorem exists_compatibleSheafCokernelTower
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Type w} [CommRing R]
    [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) Ab.{w})]
    [HasZeroMorphisms (Sheaf J Ab.{w})]
    {D : Type*} [Category* D] (V : D ⥤ Sheaf J (ModuleCat.{w} R)) [V.Full] [V.Faithful]
    (A : ℕ → D) (X : Sheaf J Ab.{w}) (s : R → (X ⟶ X)) (f : ℕ → (X ⟶ X))
    (q : ∀ n, X ⟶ (sheafCompose J (forget₂ (ModuleCat.{w} R) Ab)).obj (V.obj (A n)))
    (hs : ∀ n r, s r ≫ q n = q n ≫
      (sheafCompose J (forget₂ (ModuleCat.{w} R) Ab)).map (Sheaf.smulEnd (V.obj (A n)) r))
    (wq : ∀ n, f n ≫ q n = 0)
    (hq : ∀ n, Nonempty (IsColimit (CokernelCofork.ofπ (q n) (wq n))))
    (hw : ∀ n, f (n + 1) ≫ q n = 0) :
    ∃ t : ∀ n, A (n + 1) ⟶ A n, (∀ n, Epi (t n)) ∧
      ∃ p : (Functor.const ℕᵒᵖ).obj X ⟶ (Functor.ofOpSequence t ⋙ V) ⋙
        sheafCompose J (forget₂ (ModuleCat.{w} R) Ab), ∀ n, p.app (op n) = q n := by
  classical
  let U := sheafCompose J (forget₂ (ModuleCat.{w} R) Ab)
  have : U.Faithful := inferInstanceAs ((sheafCompose J (forget₂ (ModuleCat.{w} R) Ab)).Faithful)
  have : U.ReflectsEpimorphisms := Functor.reflectsEpimorphisms_of_faithful U
  have epiQ (n : ℕ) : Epi (q n) := Cofork.IsColimit.epi (hq n).some
  let b n := CokernelCofork.IsColimit.desc' (hq (n + 1)).some (q n) (hw n)
  have fac (n : ℕ) : q (n + 1) ≫ (b n).1 = q n := (b n).2
  have lin (n : ℕ) (r : R) :
      U.map (Sheaf.smulEnd (V.obj (A (n + 1))) r) ≫ (b n).1 =
        (b n).1 ≫ U.map (Sheaf.smulEnd (V.obj (A n)) r) := by
    apply (cancel_epi (q (n + 1))).mp
    rw [← Category.assoc, ← hs, Category.assoc, fac, hs, ← Category.assoc, fac]
  let t n := V.preimage (Sheaf.homOfSheafComposeForget₂ (b n).1 (lin n))
  have ht (n : ℕ) : U.map (V.map (t n)) = (b n).1 := by
    dsimp only [t, U]
    rw [Functor.map_preimage, Sheaf.sheafCompose_map_homOfSheafComposeForget₂]
  refine ⟨t, fun n ↦ ?_, NatTrans.ofOpSequence q (fun n ↦ ?_), fun _ ↦ rfl⟩
  · have : Epi (U.map (V.map (t n))) := ht n ▸ epi_of_epi_fac (fac n)
    exact V.epi_of_epi_map (U.epi_of_epi_map this)
  · simp only [Functor.const_obj_map, Functor.comp_map,
      Functor.ofOpSequence_map_homOfLE_succ]
    exact (by rw [← fac n, ← ht n] : q n = q (n + 1) ≫ U.map (V.map (t n)))

end WeilII
