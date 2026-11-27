module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeLowerStar

public section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilII

universe u

/-- For closed direct image and a finite source coefficient ring, the mate of the exact
coefficient-restriction square under any two right adjoints of direct image is invertible.

Source: WeilConjectures, CoefficientChangeLowerStar, in particular
isDerivedBaseChange_rightDerivedLowerStar_map_comp, and ProjectionMapMate,
isIso_mateEquiv_mateEquiv. Apply proper preservation of derived base change
to the unit of derived extension of scalars on the closed subscheme. This makes
the scalar transpose of the direct image of the unit an isomorphism. The closed
direct image is exact, so its higher direct images vanish and its right derived
functor identifies with termwise direct image. The coefficient comparison under
this identification is the localization of the ordinary restriction square:
precompose with the localization of complexes and use the defining comparison
units of both derived functors. Both composites then act by the ordinary square
on complexes, and localization is fully faithful on transformations. Thus the
inverse mate of the displayed square under the two scalar adjunctions is the
isomorphism just obtained. Mating back gives the displayed square. Taking its
mate under the two given direct-image adjunctions is conjugation of the
isomorphism by composite adjunctions, hence again an isomorphism. -/
theorem closedDirectImage_restrictionMate_isIso
    {A B : Type (u+1)} [CommRing A] [CommRing B] [Finite A] (q : A →+* B)
    {S T : Scheme.{u}} (d : S ⟶ T) [IsClosedImmersion d]
    {GB : Etale.DerivedCategoryModule B T ⥤ Etale.DerivedCategoryModule B S}
    {GA : Etale.DerivedCategoryModule A T ⥤ Etale.DerivedCategoryModule A S}
    (adjB : (Etale.lowerStar (ModuleCat.{u+1} B) d).mapDerivedCategory ⊣ GB)
    (adjA : (Etale.lowerStar (ModuleCat.{u+1} A) d).mapDerivedCategory ⊣ GA) :
    IsIso (mateEquiv adjB adjA (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (Etale.lowerStarCompRestrictScalarsIso q d).symm).hom)) := by
  let push (R : Type (u + 1)) [CommRing R] := Etale.lowerStar (ModuleCat.{u+1} R) d
  let extSc (X : Scheme.{u}) := (Etale.sheafExtendScalars q X).leftDerivedFunctor
  let res (X : Scheme.{u}) := Sheaf.derivedRestrictScalars X.smallEtaleTopology q
  let scalarAdj (X : Scheme.{u}) : extSc X ⊣ res X :=
    Etale.leftDerivedEtaleSheafExtendScalarsAdjunction q X
  -- Conjugate the proper scalar-extension isomorphism along the composite adjunctions.
  have hproper (K) := Etale.isIso_rightDerivedLowerStarExtendScalarsMap_app q d K
  have : IsIso (Etale.rightDerivedLowerStarExtendScalarsMap q d) :=
    NatIso.isIso_of_isIso_app _
  let e : extSc S ⋙ (push B).mapDerivedCategory ≅ (push A).mapDerivedCategory ⋙ extSc T :=
    Functor.isoWhiskerLeft _ (push B).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      (asIso (Etale.rightDerivedLowerStarExtendScalarsMap q d)).symm ≪≫
      Functor.isoWhiskerRight (push A).rightDerivedFunctorIsoMapDerivedCategory _
  let e' : res T ⋙ GA ≅ GB ⋙ res S :=
    conjugateIsoEquiv (adjA.comp (scalarAdj T)) ((scalarAdj S).comp adjB) e
  let ff (R : Type (u + 1)) [CommRing R] : (push R).mapDerivedCategory.FullyFaithful :=
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u+1} R) d).mapDerivedCategoryAdjunction
      |>.fullyFaithfulROfIsIsoCounit
  have : (push A).mapDerivedCategory.Full := (ff A).full
  have : (push A).mapDerivedCategory.Faithful := (ff A).faithful
  have : (push B).mapDerivedCategory.Full := (ff B).full
  have : (push B).mapDerivedCategory.Faithful := (ff B).faithful
  -- Both sides of e' invert the counit, since GB does.
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro K
  have h : IsIso (GA.map ((res T).map (adjB.counit.app K))) :=
    (NatIso.isIso_map_iff e' (adjB.counit.app K)).2
      (inferInstanceAs (IsIso ((res S).map (GB.map (adjB.counit.app K)))))
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, Functor.comp_map,
    Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id]
  infer_instance

end WeilII
