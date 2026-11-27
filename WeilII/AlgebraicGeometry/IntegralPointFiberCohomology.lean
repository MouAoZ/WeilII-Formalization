module

public import WeilII.AlgebraicGeometry.IntegralProEtaleCohomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStarDeligne
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstructibleStructure
public import WeilConjectures.TraceFormula.PointFiberFunctorIntegral
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ForgetRightDerivedLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralFlat
import WeilII.AlgebraicGeometry.IntegralPointSectionsLowerStar
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Linear
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
import WeilConjectures.CategoryTheory.ModuleObjects.Linear

/-!
# Integral point fibres and ordinary pro-étale sheaf cohomology

For a separated scheme of finite type over an algebraically closed field, the integral point
fibre of its ordinary derived direct image computes cohomology with integral coefficients.
The two functors come from `IntegralProEtaleCohomology` and the upstream
`BoundedConstructibleLowerStarDeligne` and `PointFiberFunctorIntegral`.
-/

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory
open scoped CategoryTheory.Obj

namespace WeilII

universe u

set_option maxHeartbeats 1600000 in
/-- For each nonnegative degree, ordinary integral cohomology is naturally isomorphic, as an
integral module, to the cohomology of the point fibre of the ordinary derived direct image.

Proof. Place a constructible module M in degree zero. Its only possible nonzero cohomology
sheaf is M, so the bounded constructible direct image applies. Its underlying derived object
is the ordinary derived direct image. Choose an injective resolution M → I and extend it by
zero in negative degrees. This bounded below complex of injectives is K-injective, so the
ordinary derived direct image is represented by the termwise direct image of I. At the
algebraically closed point the regular integral module is projective. Hence point sections
are exact and their termwise application to this direct image represents the point fibre.

Forgetting the module action is exact. Its left adjoint, the free module functor, preserves
monomorphisms by flatness of the integral coefficient sheaf. Thus the underlying abelian
sheaves of I resolve the underlying sheaf of M by injectives. In each degree, evaluation of
a map from the regular module at its unit identifies point sections of the direct image with
global sections on Z, using the pullback of the terminal object. Evaluation commutes with
postcomposition, so these identifications respect differentials. Taking degree-i homology
therefore identifies the underlying group of the point-fibre cohomology with the right
derived functor of global sections on M. The natural comparison of this derived functor
with sheaf cohomology gives the desired isomorphism in the indicated direction.

Precomposition by a constant scalar on the regular module sends the value at the unit to
that scalar times the value. Termwise on I this is a lift of multiplication by the same
constant section on M. Naturality of the comparison with sheaf cohomology identifies the
induced action on homology with the action defining `integralProEtaleCohomology`. The
isomorphism is therefore linear. A module morphism lifts to a chain map of resolutions,
unique up to homotopy. The termwise identifications commute with this map, and homotopic
lifts induce the same map on cohomology, giving naturality in M. In degree zero the
comparison is the inverse of evaluation at the unit.

See `PointFiberFunctorIntegral`, `PushIntegralFlat`, `ForgetRightDerivedLowerStar`,
`Sheaf.nonempty_rightDerived_sections_iso_functorH`, and
`InjectiveResolution.isoRightDerivedObjCochainComplex` in weil-conjectures. -/
public theorem nonempty_integralProEtaleCohomology_pointFiber_iso
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Z : Over (Spec (.of k))) [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (i : ℕ) :
    let R := condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z.left
    let c : ObjectProperty _ := IsConstructibleModuleObject R
    let single := (boundedConstructible R).lift (c.ι ⋙ DerivedCategory.singleFunctor _ 0)
      (fun M ↦ (boundedConstructible_singleFunctor_obj_zero_iff R M.obj).2 M.property)
    Nonempty (c.ι ⋙ integralProEtaleCohomology Z.left ℓ E i ≅
      single ⋙ CondensedRing.PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E.1
          (CondensedRing.toPoint Z) ⋙
        CondensedRing.pointFiberFunctorIntegral ℓ k E ⋙
        DerivedCategory.homologyFunctor _ (i : ℤ)) :=
  open CondensedRing Functor Limits in by
  classical
  intro R c single
  let _ := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let O := Shrink.{u + 1} (PadicAlgCl.integers ℓ E.1)
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.1
  let U := Mod.forget (D := Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1}) R
  let V := forget₂ (ModuleCat.{u + 1} O) Ab.{u + 1}
  let J := Scheme.ProEt.topology Z.left
  let Γ := Sheaf.sectionsFunctorAt.{u + 1} J (Scheme.ProEt.mk (𝟙 Z.left))
  let H := Sheaf.functorH.{u + 1, u + 1} J i
  let push := lowerStar Λ Z.hom
  let S := pointSectionsIntegral ℓ k E
  let F := push ⋙ S
  have : push.Additive := inferInstanceAs ((lowerStar Λ Z.hom).Additive)
  have : S.Additive := inferInstanceAs ((pointSectionsIntegral ℓ k E).Additive)
  have : F.Additive := inferInstanceAs ((push ⋙ S).Additive)
  let L := integralProEtaleCohomology Z.left ℓ E i
  let D := DerivedCategory.singleFunctor _ 0 ⋙ F.rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor _ (i : ℤ)
  let s : O →+* MonObj.Γ R := (padicIntegersConstSectionRingHom ℓ E Z.left).comp
    (PadicAlgCl.shrinkRingEquiv ℓ E.1).symm.toRingHom
  let _ := Mod.linearOfRingHom s
  obtain ⟨e, _, he⟩ := exists_integralPointSectionsLowerStarIso k Z.left Z.hom ℓ E
  -- Scalar multiplication is the action of a central endomorphism of each input module.
  have hF : F.Linear O := by
    apply (Functor.linear_iff O F).2
    intro M r
    rw [Mod.linearOfRingHom_smul_id]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (AddCommGrpCat.mono_iff_injective (e.hom.app M)).1 inferInstance
    change e.hom.app M (F.map ((Mod.smulNatTrans (s r).hom).app M) x) = e.hom.app M (r • x)
    let m := (Mod.smulNatTrans (s r).hom).app M
    calc
      _ = Γ.map (U.map m) (e.hom.app M x) := CategoryTheory.congr_fun (e.hom.naturality m) x
      _ = _ := (he M r x).symm
  have hsingle : (DerivedCategory.singleFunctor (Mod (Sheaf J Ab.{u + 1}) R) 0).Linear O :=
    inferInstance
  have hD : D.Linear O := inferInstanceAs
    ((DerivedCategory.singleFunctor _ 0 ⋙ F.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ (i : ℤ)).Linear O)
  let _ := HasDerivedCategory.standard Ab.{u + 1}
  let _ := HasDerivedCategory.standard (Sheaf J Ab.{u + 1})
  have hflat : PreservesFiniteLimits (MonoidalCategory.tensorLeft R) :=
    preservesFiniteLimits_tensorLeft_padicIntegersRingObj Z.left ℓ E.1
  have : PreservesFiniteLimits V := inferInstanceAs
    (PreservesFiniteLimits (forget₂ (ModuleCat.{u + 1} O) Ab.{u + 1}))
  have : PreservesFiniteColimits V :=
    ⟨fun T _ _ ↦ ModuleCat.forget₂PreservesColimitsOfShape.{u + 1, u + 1, 0, 0} O T⟩
  -- Derive the underived comparison of point sections, then evaluate in degree i.
  let d : F.rightDerivedFunctor ⋙ V.mapDerivedCategory ≅
      U.mapDerivedCategory ⋙ Γ.rightDerivedFunctor :=
    (rightDerivedFunctorCompMapDerivedCategoryIso F V).symm ≪≫
      rightDerivedFunctorIsoMapDerivedCategoryComp (show U ⋙ Γ ≅ F ⋙ V from e.symm)
  let G := DerivedCategory.homologyFunctor Ab.{u + 1} (i : ℤ)
  let h := (Sheaf.nonempty_rightDerived_sections_iso_functorH.{u + 1} J
    (Scheme.ProEt.isTerminalMkId Z.left) i).some
  let hΓ : Γ.rightDerived i ≅ H :=
    isoWhiskerLeft (ObjectProperty.topEquivalence (Sheaf J Ab.{u + 1})).inverse h
  let b : D ⋙ V ≅ U ⋙ H :=
    isoWhiskerLeft (DerivedCategory.singleFunctor _ 0 ⋙ F.rightDerivedFunctor)
        (V.mapDerivedCategoryHomologyFunctorIso (i : ℤ)) ≪≫
      isoWhiskerLeft (DerivedCategory.singleFunctor _ 0) (isoWhiskerRight d G) ≪≫
      isoWhiskerRight (U.mapDerivedCategorySingleFunctor 0) (Γ.rightDerivedFunctor ⋙ G) ≪≫
      isoWhiskerLeft U (Γ.singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso i ≪≫ hΓ)
  -- Naturality on scalar endomorphisms upgrades the comparison to an integral linear one.
  let linearIso : D ≅ L := NatIso.ofComponents (fun M ↦
    ModuleCat.isoMk (M := D.obj M) (N := L.obj M) (b.app M) (by
      intro r
      have hn := b.hom.naturality (r • 𝟙 M)
      change V.map (D.map (r • 𝟙 M)) ≫ _ = _ ≫ H.map (U.map (r • 𝟙 M)) at hn
      rw [D.map_smul, D.map_id, Mod.linearOfRingHom_smul_id] at hn
      exact hn.symm)) (by
      intro X Y f
      exact V.map_injective (b.hom.naturality f))
  refine ⟨isoWhiskerLeft c.ι linearIso.symm ≪≫ ?_⟩
  have : PreservesFiniteLimits S := inferInstanceAs
    (PreservesFiniteLimits (pointSectionsIntegral ℓ k E))
  have : PreservesFiniteColimits S := inferInstanceAs
    (PreservesFiniteColimits (pointSectionsIntegral ℓ k E))
  let dpush : F.rightDerivedFunctor ≅
      (lowerStar Λ (toPoint Z).left).rightDerivedFunctor ⋙ S.mapDerivedCategory := by
    rw [toPoint_left]
    exact rightDerivedFunctorCompMapDerivedCategoryIso push S
  exact isoWhiskerLeft (c.ι ⋙ DerivedCategory.singleFunctor _ 0)
    (isoWhiskerRight dpush (DerivedCategory.homologyFunctor _ (i : ℤ)))

end WeilII
