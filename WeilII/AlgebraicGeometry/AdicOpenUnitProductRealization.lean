module

public import WeilII.AlgebraicGeometry.AdicOpenExtensionPullback
public import WeilII.AlgebraicGeometry.BoundedConstructibleAdicRealization
import WeilII.AlgebraicGeometry.BoundedOpenUnitProductSupport
import WeilConjectures.SixFunctors.ProEtale.Adic.BaseChange
import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstructibleStructure
public import WeilConjectures.TraceFormula.KunnethVerdierOpen
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

namespace WeilII

open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.Scheme
open CategoryTheory Limits
open scoped CategoryTheory.Obj

universe u

set_option backward.isDefEq.respectTransparency false in
/-- Transport the product boundary-vanishing statement to native adic complexes and place
the parameter in the second factor. The braidings give cartesian squares with horizontal
isomorphisms for the direct image and both open extensions. -/
public theorem adicOpenUnitProduct_essImage (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y V S : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    (h : X ⟶ Y) (j : V ⟶ S) [IsOpenImmersion j.left]
    (K : AdicSheaf ℓ X.left) (hK : IsAdicConstructibleSheaf K) :
    (adicOpenImmersionLowerShriek ℓ (prod.map (𝟙 Y) j).left).mapDerivedCategory.essImage
      ((adicLowerStar ℓ (prod.map h (𝟙 S)).left).rightDerivedFunctor.obj
        ((adicOpenImmersionLowerShriek ℓ (prod.map (𝟙 X) j).left).mapDerivedCategory.obj
          ((adicUpperStar ℓ (prod.fst : X ⨯ V ⟶ X).left).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor _ 0).obj K)))) := by
  classical
  let M := (DerivedCategory.singleFunctor _ 0).obj K
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  let E := adicSheafDerivedEquivCondensedMod ℓ X.left
  let B : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) :=
    ⟨(DerivedCategory.singleFunctor _ 0).obj ((adicSheafEquivCondensedMod ℓ X.left).functor.obj K),
      (boundedConstructible_singleFunctor_obj_zero_iff _ _).2 hK.isConstructibleModuleObject⟩
  let eB : (boundedAdicRealization ℓ X.left).obj B ≅ M :=
    E.inverse.mapIso ((singleFunctorCompAdicSheafDerivedEquivCondensedModIso ℓ X.left 0).symm.app K) ≪≫
      E.unitIso.symm.app M
  have openMap (T : Over (Spec (.of k))) : IsOpenImmersion (prod.map j (𝟙 T)).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_prod_fst_with_id j T).map (Over.forget _))
      (inferInstanceAs (IsOpenImmersion j.left))
  let openIso {A C : Over (Spec (.of k))}
      [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
      [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
      (g : A ⟶ C) [IsOpenImmersion g.left]
      (N : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) A.left)) :
      (boundedAdicRealization ℓ C.left).obj ((boundedConstructibleLowerShriek ℓ g).obj N) ≅
        (adicOpenImmersionLowerShriek ℓ g.left).mapDerivedCategory.obj
          ((boundedAdicRealization ℓ A.left).obj N) :=
    (adicSheafDerivedEquivCondensedMod ℓ C.left).inverse.mapIso
      ((boundedConstructible _).ι.mapIso
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ g).app N)) ≪≫
    (adicSheafDerivedEquivCondensedMod ℓ C.left).inverse.mapIso
      ((boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ g).app N) ≪≫
    ((adicSheafDerivedEquivCondensedMod ℓ A.left).inverseCompIsoCompInverse
      (adicSheafDerivedEquivCondensedMod ℓ C.left)
      (adicOpenImmersionLowerShriekMapDerivedCategoryCompIso ℓ C.left g.left)).symm.app N.obj
  let p := (prod.snd : V ⨯ X ⟶ X)
  let p' := (prod.fst : X ⨯ V ⟶ X)
  let U := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p
  let ep : (boundedAdicRealization ℓ (V ⨯ X).left).obj (U.obj B) ≅
      (adicUpperStar ℓ p.left).mapDerivedCategory.obj M :=
    (adicSheafDerivedEquivCondensedMod ℓ (V ⨯ X).left).inverse.mapIso
      ((boundedConstructibleUpperStarCompatibility _ ℓ p).app B ≪≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) p.left).leftDerivedFunctorIsoMapDerivedCategory.app B.obj) ≪≫
    ((adicSheafDerivedEquivCondensedMod ℓ X.left).inverseCompIsoCompInverse
      (adicSheafDerivedEquivCondensedMod ℓ (V ⨯ X).left)
      (adicUpperStarMapDerivedCategoryCompIso ℓ X.left p.left)).symm.app B.obj ≪≫
    (adicUpperStar ℓ p.left).mapDerivedCategory.mapIso eB
  let a := prod.map j (𝟙 X)
  let b := prod.map j (𝟙 Y)
  let H := prod.map (𝟙 S) h
  obtain ⟨N, ⟨e⟩⟩ := boundedOpenUnitProductSupport ℓ h j B
  let ex := (openIso b N).symm ≪≫ (boundedAdicRealization ℓ (S ⨯ Y).left).mapIso e ≪≫
    (boundedStarAdicRealizationIso ℓ H).app _ ≪≫ (adicLowerStar ℓ H.left).rightDerivedFunctor.mapIso
      (openIso a (U.obj B) ≪≫ (adicOpenImmersionLowerShriek ℓ a.left).mapDerivedCategory.mapIso ep)
  let τ (A C : Over (Spec (.of k))) := ((Over.forget _).mapIso (prod.braiding A C))
  have sq {A C D F : Over (Spec (.of k))} (f : A ⟶ C) (g : D ⟶ F) :
      IsPullback (τ A D).hom (prod.map f g).left (prod.map g f).left (τ C F).hom := by
    apply IsPullback.of_horiz_isIso
    constructor
    exact congrArg CommaMorphism.left (show (prod.braiding A D).hom ≫ prod.map g f =
      prod.map f g ≫ (prod.braiding C F).hom by apply prod.hom_ext <;> simp)
  let sy := sq (𝟙 Y) j
  let sx := sq (𝟙 X) j
  let sh := (sq h (𝟙 S)).flip
  have := isIso_adicOpenExtensionPullbackMap ℓ sy
  have := isIso_adicOpenExtensionPullbackMap ℓ sx
  let comp : (adicUpperStar ℓ p.left).mapDerivedCategory ⋙
      (adicUpperStar ℓ (τ X V).hom).mapDerivedCategory ≅ (adicUpperStar ℓ p'.left).mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫ Functor.mapDerivedCategoryNatIso
      ((adicUpperStarComp ℓ _ _).symm ≪≫ adicUpperStarCongr ℓ
        (show (τ X V).hom ≫ p.left = p'.left by
          change (prod.braiding X V).hom.left ≫ _ = _
          rw [← Over.comp_left]; simp [p, p']))
  refine ⟨(adicUpperStar ℓ (τ Y V).hom).mapDerivedCategory.obj
    ((boundedAdicRealization ℓ (V ⨯ Y).left).obj N), ⟨?_⟩⟩
  exact (asIso (adicOpenExtensionPullbackMap ℓ sy.toCommSq)).app _ ≪≫
    (adicUpperStar ℓ (τ Y S).hom).mapDerivedCategory.mapIso ex ≪≫
    (adicDerivedBaseChangeIso ℓ sh).app _ ≪≫
    (adicLowerStar ℓ (prod.map h (𝟙 S)).left).rightDerivedFunctor.mapIso
      ((asIso (adicOpenExtensionPullbackMap ℓ sx.toCommSq)).symm.app _ ≪≫
        (adicOpenImmersionLowerShriek ℓ (prod.map (𝟙 X) j).left).mapDerivedCategory.mapIso (comp.app M))

end WeilII
