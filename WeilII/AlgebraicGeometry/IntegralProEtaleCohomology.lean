module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Conj
public import WeilConjectures.CategoryTheory.ModuleObjects.SectionAction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UniformizerReduction

/-!
# Ordinary pro-étale cohomology with its integral scalar action

Mathlib's `Sheaf.H` computes cohomology as Ext from the constant integer sheaf.
The constant sections of the ring of integers act through its second argument.
-/

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory
open scoped CategoryTheory.Obj

namespace WeilII

universe u v

/-- Lift an abelian-group-valued functor with a natural ring action to modules, using
Mathlib's `ModuleCat.mkOfSMul` and `ModuleCat.homMk`. -/
@[expose] public noncomputable def integralProEtaleCohomology.liftModuleFunctor
    {C : Type*} [Category* C] (O : Type*) [CommRing O]
    (F : C ⥤ Ab.{v}) (act : ∀ X, O →+* End (F.obj X))
    (hact : ∀ {X Y} (f : X ⟶ Y) r,
      F.map f ≫ (act Y r).asHom = (act X r).asHom ≫ F.map f) :
    C ⥤ ModuleCat.{v} O where
  obj X := ModuleCat.mkOfSMul (act X)
  map {X Y} f := ModuleCat.homMk (M := ModuleCat.mkOfSMul (act X))
    (N := ModuleCat.mkOfSMul (act Y)) (F.map f) (hact f)
  map_id X := (forget₂ (ModuleCat O) Ab).map_injective (F.map_id X)
  map_comp f g := (forget₂ (ModuleCat O) Ab).map_injective (F.map_comp f g)

/-- Ordinary cohomology of integral pro-étale modules, with the action of a constant
scalar induced by its action on the underlying abelian sheaf. The scalar ring is written
in the same universe as the coefficient modules of the integral point fibre.
See `ProEtale.padicIntegersConstSectionRingHom`, `Mod.sectionActRingHom` and `Sheaf.functorH`. -/
@[expose] public noncomputable def integralProEtaleCohomology (Z : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) (i : ℕ) :
    Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z) ⥤
      ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers ℓ E.1)) :=
  let R := condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z
  let O := Shrink.{u + 1} (PadicAlgCl.integers ℓ E.1)
  let c : O →+* MonObj.Γ R := (padicIntegersConstSectionRingHom ℓ E Z).comp
    (PadicAlgCl.shrinkRingEquiv ℓ E.1).symm.toRingHom
  let G := Sheaf.functorH.{u + 1, u + 1} (Scheme.ProEt.topology Z) i
  integralProEtaleCohomology.liftModuleFunctor O (Mod.forget R ⋙ G)
    (fun M ↦ (G.mapEndRingHom M.X).comp ((Mod.sectionActRingHom M).comp c))
    (fun f r ↦ by
      change G.map f.hom ≫ G.map _ = G.map _ ≫ G.map f.hom
      rw [← G.map_comp, ← G.map_comp]
      exact congrArg G.map (Mod.sectionActRingHom_comp_hom f (c r)).symm)

end WeilII
