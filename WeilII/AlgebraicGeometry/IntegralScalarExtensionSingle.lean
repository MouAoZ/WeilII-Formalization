module

public import WeilII.AlgebraicGeometry.BoundedConstructibleAdicRealization
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstructibleStructure
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Realization of integral scalar extension on a sheaf in degree zero -/

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory
open scoped CategoryTheory.Obj

namespace WeilII

universe u

set_option backward.isDefEq.respectTransparency false in
/-- Realizing the bounded constructible scalar extension of an integral sheaf in degree zero
gives its ordinary scalar extension placed in degree zero. The two sheaf scalar extensions
are exact by `EllAdicRationalization` and `Colimit.Compatibility` in WeilConjectures.
Apply `singleFunctorCompLeftDerivedFunctorIso` to each, then commute the inverse
adic equivalence with the single functor using `mapDerivedCategorySingleFunctor`. -/
public noncomputable def integralScalarExtensionSingleIso
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    let R := condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X
    let c : ObjectProperty _ := IsConstructibleModuleObject R
    let single := (boundedConstructible R).lift (c.ι ⋙ DerivedCategory.singleFunctor _ 0)
      (fun M ↦ (boundedConstructible_singleFunctor_obj_zero_iff R M.obj).2 M.property)
    single ⋙ boundedConstructibleExtendScalars X ℓ E ⋙ constructibleToPadicAlgCl X ℓ E ⋙
        boundedAdicRealization ℓ X ≅
      c.ι ⋙ Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E) ⋙
        Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E) ⋙
        (adicSheafEquivCondensedMod ℓ X).inverse ⋙ DerivedCategory.singleFunctor _ 0 :=
  open scoped CondensedRing.CachedModInstances in by
  intro R c single
  let F := Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)
  let G := Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)
  let A := (adicSheafEquivCondensedMod ℓ X).inverse
  exact Functor.isoWhiskerLeft c.ι
    (Functor.isoWhiskerRight F.singleFunctorCompLeftDerivedFunctorIso
        (G.leftDerivedFunctor ⋙ A.mapDerivedCategory) ≪≫
      Functor.isoWhiskerLeft F
        (Functor.isoWhiskerRight G.singleFunctorCompLeftDerivedFunctorIso A.mapDerivedCategory ≪≫
          Functor.isoWhiskerLeft G (A.mapDerivedCategorySingleFunctor 0)))

end WeilII
