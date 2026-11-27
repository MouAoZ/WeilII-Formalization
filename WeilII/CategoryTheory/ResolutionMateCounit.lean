module

public import WeilII.CategoryTheory.ResolutionCounit
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Comma.Over.Basic

open CategoryTheory Limits

namespace WeilII

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory C'] [HasDerivedCategory D']
  {I : C ⥤ D} {S : D ⥤ C} {J : C' ⥤ D'} {H : D' ⥤ C'} {P : D ⥤ D'} {U : C ⥤ C'}
  [I.Additive] [S.Additive] [J.Additive] [H.Additive] [P.Additive] [U.Additive]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I] [PreservesFiniteLimits J]
  [PreservesFiniteColimits J] [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- Push a termwise mate followed by a change of representative through the left adjoint.
In the slice over the target complex it becomes pullback of the source counit followed by
that change. The isomorphism on domains is the original left-adjoint square. -/
public theorem resolutionMate_overIso (a : I ⊣ S) (b : J ⊣ H) (e : I ⋙ P ≅ U ⋙ J)
    (K : CochainComplex D ℤ) (K' : CochainComplex D' ℤ)
    (r : (P.mapHomologicalComplex (.up ℤ)).obj K ⟶ K') :
    let β := mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)
    let t := (Functor.mapHomologicalComplexCompIso (F := S) (G := U) (Iso.refl _) (.up ℤ)).hom ≫
      β.mapHomologicalComplex (.up ℤ) ≫
      (Functor.mapHomologicalComplexCompIso (F := P) (G := H) (Iso.refl _) (.up ℤ)).inv
    let f := t.app K ≫ (H.mapHomologicalComplex (.up ℤ)).map r
    Nonempty (Over.mk (J.mapDerivedCategory.map (DerivedCategory.Q.map f) ≫ resolutionCounit b K') ≅
      Over.mk (P.mapDerivedCategory.map (resolutionCounit a K) ≫
        P.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map r)) := by
  intro β t f
  let SK := (S.mapHomologicalComplex (.up ℤ)).obj K
  let ca := (a.mapHomologicalComplex (.up ℤ)).counit.app K
  let cb := (b.mapHomologicalComplex (.up ℤ)).counit.app K'
  let ex := (Functor.mapHomologicalComplexCompIso (F := U) (G := J) (Iso.refl _) (.up ℤ)).app SK ≪≫
    (NatIso.mapHomologicalComplex e.symm (.up ℤ)).app SK ≪≫
    ((Functor.mapHomologicalComplexCompIso (F := I) (G := P) (Iso.refl _) (.up ℤ)).app SK).symm
  have chainEq : (J.mapHomologicalComplex (.up ℤ)).map f ≫ cb =
      ex.hom ≫ (P.mapHomologicalComplex (.up ℤ)).map ca ≫ r := by
    ext n
    simp only [f, t, cb, ca, ex, SK, HomologicalComplex.comp_f, NatTrans.comp_app,
      Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
      Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, NatIso.mapHomologicalComplex_hom_app_f,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      Adjunction.mapHomologicalComplex_counit_app_f, Functor.map_comp, Category.assoc]
    change J.map (𝟙 _) ≫ J.map (β.app (K.X n)) ≫ J.map (𝟙 _) ≫
      J.map (H.map (r.f n)) ≫ b.counit.app _ =
      𝟙 _ ≫ e.inv.app _ ≫ 𝟙 _ ≫ P.map (a.counit.app (K.X n)) ≫ r.f n
    have hn := b.counit.naturality (r.f n)
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, hn]
    change J.map ((mateEquiv a b (TwoSquare.mk U I J P e.inv)).app (K.X n)) ≫
      b.counit.app (P.obj (K.X n)) ≫ r.f n = _
    rw [← Category.assoc, mateEquiv_counit]
    exact Category.assoc _ _ _
  let dom := J.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso ex ≪≫
    (P.mapDerivedCategoryFactors.app _).symm ≪≫
    P.mapDerivedCategory.mapIso (I.mapDerivedCategoryFactors.app SK).symm
  refine ⟨Over.isoMk dom ?_⟩
  change dom.hom ≫ P.mapDerivedCategory.map (resolutionCounit a K) ≫
      P.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map r =
    J.mapDerivedCategory.map (DerivedCategory.Q.map f) ≫ resolutionCounit b K'
  simp only [dom, resolutionCounit, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
  rw [← P.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  erw [P.mapDerivedCategory.map_id, Category.id_comp]
  have hP := P.mapDerivedCategoryFactors.hom.naturality ca
  have hJ := J.mapDerivedCategoryFactors.hom.naturality f
  dsimp only [Functor.comp_map] at hP hJ
  erw [reassoc_of% hP, Iso.inv_hom_id_app_assoc, reassoc_of% hJ]
  exact congrArg (J.mapDerivedCategoryFactors.hom.app _ ≫ ·) (by
    simpa only [Functor.map_comp, Category.assoc] using congrArg DerivedCategory.Q.map chainEq.symm)

end WeilII
