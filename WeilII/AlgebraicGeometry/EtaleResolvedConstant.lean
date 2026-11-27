module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget

open CategoryTheory AlgebraicGeometry

namespace WeilII

universe u

/-- Forgetting the regular module constant in degree zero gives the abelian constant in
degree zero. The comparison first commutes forgetting with the single functor, then with
sheafification of the constant presheaf. -/
public noncomputable def etaleForgetRegularSingleIso
    (R : Type (u+1)) [CommRing R] (X : Scheme.{u}) :
    let F := (constantSheaf X.smallEtaleTopology (ModuleCat.{u+1} R)).obj (ModuleCat.of R R)
    let G := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u+1}).obj (AddCommGrpCat.of R)
    (Etale.moduleAbelianForget R X).mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.singleFunctor _ 0).obj G := by
  intro F G
  let V := Etale.moduleAbelianForget R X
  let c := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u+1}
  let g : (forget₂ (ModuleCat.{u+1} R) AddCommGrpCat.{u+1}).obj (ModuleCat.of R R) ≅
      AddCommGrpCat.of R := Iso.refl _
  let φ : V.obj F ≅ G := ((Etale.constantSheafSheafComposeForget₂Iso R).app (ModuleCat.of R R)) ≪≫
    c.mapIso g
  exact (V.mapDerivedCategorySingleFunctor 0).app F ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso φ

end WeilII
