module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.SixFunctors.RegularQuotientTraceOnInjectiveTerms

open CategoryTheory Limits

namespace WeilII

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
  {I : C ⥤ D} {S : D ⥤ C} [I.Additive] [S.Additive]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]

/-- The localized termwise counit on a K-injective representative. -/
@[expose] public noncomputable def resolutionCounit (a : I ⊣ S) (K : CochainComplex D ℤ) :=
  I.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj K) ≫
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app K)

/-- On a K-injective input the localized termwise counit represents the right derived adjoint.
This follows by composing the derived hom-equivalence with the K-injective computation iso. -/
public theorem resolutionCounit_bijective (a : I ⊣ S) (K : CochainComplex D ℤ) [K.IsKInjective]
    {T : DerivedCategory D} (e : DerivedCategory.Q.obj K ≅ T) (N : DerivedCategory C) :
    Function.Bijective (fun f : N ⟶ DerivedCategory.Q.obj ((S.mapHomologicalComplex (.up ℤ)).obj K) ↦
      I.mapDerivedCategory.map f ≫ resolutionCounit a K ≫ e.hom) := by
  let x := S.rightDerivedFunctorObjQIso K
  let bij := (x.symm.homToEquiv.trans
    (a.mapDerivedCategoryRightDerivedAdjunction.homEquiv N _).symm).trans e.homToEquiv
  have h := a.mapDerivedCategory_map_rightDerivedFunctorObjQIso_inv_counit K
  convert bij.bijective using 1
  funext f
  change _ = (I.mapDerivedCategory.map (f ≫ x.inv) ≫ _) ≫ e.hom
  simp only [Functor.map_comp, Category.assoc, x, reassoc_of% h, resolutionCounit]

end WeilII
