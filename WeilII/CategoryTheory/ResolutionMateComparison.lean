module

public import WeilII.CategoryTheory.ResolutionMateCounit
import WeilII.CategoryTheory.PulledCounitArrows
import WeilII.CategoryTheory.MappedMateCounit

open CategoryTheory Limits

namespace WeilII

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory C'] [HasDerivedCategory D']
  {I : C ⥤ D} {S : D ⥤ C} {J : C' ⥤ D'} {H : D' ⥤ C'} {P : D ⥤ D'} {U : C ⥤ C'}
  [I.Additive] [S.Additive] [J.Additive] [H.Additive] [P.Additive] [U.Additive]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I] [PreservesFiniteLimits J]
  [PreservesFiniteColimits J] [PreservesFiniteLimits P] [PreservesFiniteColimits P]

variable [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions D']
  {E B E' B' : Type*} [Category* E] [Category* B] [Category* E'] [Category* B']
  {Iₘ : E ⥤ B} {Sₘ : B ⥤ E} {Jₘ : E' ⥤ B'} {Hₘ : B' ⥤ E'}
  {Uₘ : E ⥤ E'} {Pₘ : B ⥤ B'}
  {W : E ⥤ DerivedCategory C} {V : B ⥤ DerivedCategory D}
  {W' : E' ⥤ DerivedCategory C'} {V' : B' ⥤ DerivedCategory D'}

/-- Suppose a second pair of adjunctions, after forgetting coefficients, represents the
right adjoints of two exact derived inclusions on the given inputs. Then the coefficient
mate is isomorphic as an arrow to the mate on K-injective representatives followed by the
change of resolution. All choices of invertible left squares give the same arrow class. -/
public theorem resolutionMate_compare_of_counit_bijections
    (a : I ⊣ S) (b : J ⊣ H) (e : I ⋙ P ≅ U ⋙ J)
    (aₘ : Iₘ ⊣ Sₘ) (bₘ : Jₘ ⊣ Hₘ) (eₘ : Iₘ ⋙ Pₘ ≅ Uₘ ⋙ Jₘ)
    (ci : W ⋙ I.mapDerivedCategory ≅ Iₘ ⋙ V)
    (cj : W' ⋙ J.mapDerivedCategory ≅ Jₘ ⋙ V')
    (cp : V ⋙ P.mapDerivedCategory ≅ Pₘ ⋙ V')
    (ff : J.mapDerivedCategory.FullyFaithful) (M : B)
    (K : CochainComplex D ℤ) [K.IsKInjective] (x : DerivedCategory.Q.obj K ≅ V.obj M)
    (K' : CochainComplex D' ℤ) [K'.IsKInjective]
    (r : (P.mapHomologicalComplex (.up ℤ)).obj K ⟶ K') [IsIso (DerivedCategory.Q.map r)]
    (hi : ∀ N, Function.Bijective (fun f : N ⟶ W.obj (Sₘ.obj M) ↦
      I.mapDerivedCategory.map f ≫ ci.hom.app _ ≫ V.map (aₘ.counit.app M)))
    (hj : ∀ N, Function.Bijective (fun f : N ⟶ W'.obj (Hₘ.obj (Pₘ.obj M)) ↦
      J.mapDerivedCategory.map f ≫ cj.hom.app _ ≫ V'.map (bₘ.counit.app (Pₘ.obj M)))) :
    let β := mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)
    let t := (Functor.mapHomologicalComplexCompIso (F := S) (G := U) (Iso.refl _) (.up ℤ)).hom ≫
      β.mapHomologicalComplex (.up ℤ) ≫
      (Functor.mapHomologicalComplexCompIso (F := P) (G := H) (Iso.refl _) (.up ℤ)).inv
    let f := t.app K ≫ (H.mapHomologicalComplex (.up ℤ)).map r
    let g := (mateEquiv aₘ bₘ (TwoSquare.mk _ _ _ _ eₘ.inv)).app M
    Nonempty (Arrow.mk (DerivedCategory.Q.map f) ≅ Arrow.mk (W'.map g)) := by
  intro β t f g
  let z := P.mapDerivedCategoryFactors.app K ≪≫ asIso (DerivedCategory.Q.map r)
  let y := z.symm ≪≫ P.mapDerivedCategory.mapIso x ≪≫ cp.app M
  have h : z.hom ≫ y.hom = P.mapDerivedCategory.map x.hom ≫ cp.hom.app M := by
    simp only [y, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc, Functor.mapIso_hom, Iso.app_hom]
  exact arrowIso_of_pulled_counits (I := I.mapDerivedCategory) ff P.mapDerivedCategory
    (DerivedCategory.Q.map f) (W'.map g)
    (resolutionCounit a K) _ (resolutionCounit b K') _ x y h
    (resolutionCounit_bijective a K x) hi (resolutionCounit_bijective b K' y) hj
    (resolutionMate_overIso a b e K K' r) (mappedMate_overIso aₘ bₘ eₘ ci cj cp M)

end WeilII
