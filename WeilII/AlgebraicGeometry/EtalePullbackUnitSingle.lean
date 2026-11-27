module

public import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisons
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # Pullback of the étale monoidal unit in degree zero -/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

namespace WeilII

/-- On a unit sheaf in degree zero, the derived unit comparison is induced by the ordinary
pullback unit comparison. -/
theorem etalePullbackUnitSingle (C : Type v) [Category.{u+1} C] [Abelian C]
    [IsGrothendieckAbelian.{u+1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [UpperStarPreservesFlat C] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let := leftDerivedUpperStarOplaxMonoidal C f
    L((f)^*[C]).map (singleFunctorObjUnitIso C Y).inv ≫
        (singleFunctorCompLeftDerivedUpperStarIso C f).hom.app (𝟙_ _) ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map (Functor.OplaxMonoidal.η (f)^*[C]) =
      Functor.OplaxMonoidal.η L((f)^*[C]) ≫ (singleFunctorObjUnitIso C X).inv := by
  let := leftDerivedUpperStarOplaxMonoidal C f
  have h := leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp C f
  rw [← constantSinglePullbackIso_source_hom C f, constantSinglePullbackIso_hom,
    upperStarConstantSheafIso_hom_app_tensorUnit C f] at h
  exact h.trans (congrArg (fun z ↦ z ≫ (singleFunctorObjUnitIso C X).inv)
    (leftDerivedUpperStarOplaxMonoidal_η C f).symm)

end WeilII
