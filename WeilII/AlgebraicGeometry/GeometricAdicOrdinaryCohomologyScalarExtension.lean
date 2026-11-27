module

public import WeilII.AlgebraicGeometry.IntegralProEtaleCohomology
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalence
public import WeilConjectures.TraceFormula.PointFiberFunctorIntegral
public import WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology
import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstructibleStructure
import WeilConjectures.TraceFormula.IntegersToPadicAlgClLowerStar
import WeilII.AlgebraicGeometry.IntegralPointFiberCohomology
import WeilII.AlgebraicGeometry.PointFiberNativeSections
import WeilII.AlgebraicGeometry.IntegralScalarExtensionSingle

/-!
# Extension of scalars for ordinary geometric ℓ-adic cohomology

The ordinary direct image and point fibre comparisons are in
`TraceFormula.IntegersToPadicAlgClLowerStar` and `TraceFormula.PointFiberFunctorIntegral`
of `weil-conjectures`. The geometric cohomology functor is from
`WeilSheaf.AlgClosedCoefficientCohomology`.
-/

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- Over the algebraic closure of a finite field of characteristic different from ℓ,
extending the scalars of ordinary integral cohomology to the algebraic closure of ℚℓ
agrees naturally with the ordinary cohomology of the extended sheaf.

Proof. Write O for the ring of integers of E, Q for the algebraic closure of ℚℓ and s
for the geometric base point. A constructible O-module M gives the bounded constructible
complex M[0]. Both sheaf coefficient extensions are exact. The first inverts ℓ by a
sequential colimit, and the second is a filtered colimit of finite free extensions.
Consequently their derived composite on M[0] is the two successive ordinary extensions
of M placed in degree zero.

Put P = Ra_* M[0] in the integral bounded constructible category on s. Integral point
sections of P compute ordinary sheaf cohomology: on an injective resolution, evaluation
of a map from the regular module at 1 gives global sections of the underlying abelian
sheaf. Forgetting to abelian sheaves preserves injectives since the free module functor
is exact by flatness of the coefficient sheaf. Multiplication by a constant acts on these
sections through the action of that constant on M. Since O → E is a localization and
E → Q is a field extension, flat base change for homology identifies the tensor product
of this cohomology with the homology of the derived scalar extension of the point fibre.

Apply the inverse of `pointFiberFunctorIntegralExtendScalarsIso` at P, then apply the
rational point fibre to `boundedConstructibleLowerStarIntegersToPadicAlgClIso` at M[0].
This computes the rational point fibre of the ordinary direct image of the extended
complex. The linear identification of point sections with native adic global sections,
followed by the native/condensed direct image comparison, identifies its degree-i
homology with `algClosedCohomology` of the extended sheaf in degree zero. All comparisons
are natural in M, so their composite restricts to the stated natural isomorphism. -/
public theorem nonempty_integralProEtaleCohomology_extendScalars_iso
    (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k₀ ≠ ℓ)]
    {Z : Scheme.{u}} (a : Z ⟶ Spec (.of (AlgebraicClosure k₀)))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (i : ℕ) :
    let c : ObjectProperty _ := IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z)
    let extendSheaf := Mod.extendScalars (padicIntegersToPadicSubfield Z ℓ E) ⋙
      Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Z ℓ E) ⋙
      (adicSheafEquivCondensedMod ℓ Z).inverse
    Nonempty (c.ι ⋙ integralProEtaleCohomology Z ℓ E i ⋙
        ModuleCat.extendScalars (PadicAlgCl.integersToULift ℓ E.1) ≅
      c.ι ⋙ extendSheaf ⋙ DerivedCategory.singleFunctor _ 0 ⋙ algClosedCohomology ℓ a i) :=
  open CondensedRing Functor in by
  intro c extendSheaf
  let k := AlgebraicClosure k₀
  have : Fact (ringChar k).Prime := ⟨Algebra.ringChar_eq k₀ k ▸ CharP.prime_ringChar k₀⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨Algebra.ringChar_eq k₀ k ▸ (Fact.out : ringChar k₀ ≠ ℓ)⟩
  let X : Over (Spec (.of k)) := Over.mk a
  have : IsSeparated X.hom := ‹IsSeparated a›
  have : LocallyOfFiniteType X.hom := ‹LocallyOfFiniteType a›
  have : QuasiCompact X.hom := ‹QuasiCompact a›
  let R := condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z
  let single := (boundedConstructible R).lift (c.ι ⋙ DerivedCategory.singleFunctor _ 0)
    (fun M ↦ (boundedConstructible_singleFunctor_obj_zero_iff R M.obj).2 M.property)
  let push := PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E.1 (toPoint X)
  let T := boundedConstructibleIntegersToPadicAlgCl ℓ E X
  let pushQ := boundedConstructibleLowerStar ℓ (toPoint X)
  let Γ := (adicGlobalSections ℓ (point k).left).rightDerivedFunctor
  let H := DerivedCategory.homologyFunctor (WeilCoefficients.{u} ℓ) (i : ℤ)
  let f := PadicAlgCl.integersToULift.{u} ℓ E.1
  let ext := ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f
  have : Limits.PreservesFiniteLimits ext :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (PadicAlgCl.flat_integersToULift ℓ E.1)
  obtain ⟨integral⟩ := nonempty_integralProEtaleCohomology_pointFiber_iso k ℓ X E i
  obtain ⟨fiber⟩ := nonempty_pointFiberFunctorIsoAdicRightDerivedGlobalSections ℓ k
  have pushIso : pushQ ⋙ boundedAdicRealization ℓ (point k).left ≅
      boundedAdicRealization ℓ Z ⋙ (adicLowerStar ℓ a).rightDerivedFunctor := by
    have e := boundedStarAdicRealizationIso ℓ (toPoint X)
    rw [toPoint_left] at e
    exact e
  -- Extend integral point-fibre cohomology, then move scalar extension through the fibre and pushforward.
  refine ⟨(associator c.ι (integralProEtaleCohomology Z ℓ E i) ext).symm ≪≫
    isoWhiskerRight integral ext ≪≫ ?_⟩
  refine isoWhiskerLeft (single ⋙ push ⋙ pointFiberFunctorIntegral ℓ k E)
    (ext.mapDerivedCategoryHomologyFunctorIso (i : ℤ)) ≪≫ ?_
  refine isoWhiskerRight (isoWhiskerLeft (single ⋙ push)
    (pointFiberFunctorIntegralExtendScalarsIso ℓ k E).symm) H ≪≫ ?_
  refine isoWhiskerLeft single (isoWhiskerRight
    (boundedConstructibleLowerStarIntegersToPadicAlgClIso ℓ E (toPoint X))
    (pointFiberFunctor ℓ k ⋙ H)) ≪≫ ?_
  -- Realize the rational pushforward in the native adic category.
  refine isoWhiskerLeft (single ⋙ T ⋙ pushQ) (isoWhiskerRight fiber H) ≪≫ ?_
  refine isoWhiskerLeft (single ⋙ T) (isoWhiskerRight pushIso (Γ ⋙ H)) ≪≫ ?_
  exact isoWhiskerRight (integralScalarExtensionSingleIso Z ℓ E)
    (algClosedCohomology ℓ a i)

end WeilII
