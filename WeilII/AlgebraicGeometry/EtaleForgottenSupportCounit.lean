module

public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import WeilConjectures.SixFunctors.OpenClosed.Derived

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

namespace WeilII

universe u

/-- Identify termwise abelian closed direct image with forgotten finite lower shriek. -/
@[expose] public noncomputable def closedPushForgetIso
    (R : Type (u+1)) [CommRing R] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (moduleAbelianForget R Z).mapDerivedCategory ⋙ (lowerStar Ab.{u+1} i).mapDerivedCategory ≅
      R(i)_![ModuleCat.{u+1} R] ⋙ (moduleAbelianForget R X).mapDerivedCategory :=
  let A := ModuleCat.{u+1} R
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (moduleAbelianLowerStarIso R i).symm ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerRight ((lowerStar A i).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar A i).symm) _

/-- After forgetting a finite coefficient ring, the exceptional counit on a complex isomorphic
to a sheaf in degree zero still represents maps from abelian closed direct images.
Indeed the bounded-below comparison identifies the open term of the localization triangle
with an abelian derived open direct image. The shifted closed images are orthogonal to it,
and applying Hom to the triangle gives the required bijection. -/
public theorem forgottenSupportCounit_bijective
    (R : Type (u+1)) [CommRing R] [Finite R] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} R)))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u+1} R))
    (m : M ≅ (DerivedCategory.singleFunctor _ 0).obj F) :
    let V := (moduleAbelianForget R X).mapDerivedCategory
    let J := (lowerStar Ab.{u+1} i).mapDerivedCategory
    let H := (rightDerivedUpperShriek R i).obj M
    let c := (closedPushForgetIso R i).hom.app H ≫ V.map ((rightDerivedUpperShriekAdjunction R i).counit.app M)
    ∀ N, Function.Bijective (fun f : N ⟶ (moduleAbelianForget R Z).mapDerivedCategory.obj H ↦
      J.map f ≫ c) := by
  intro V J H c
  let j := i.openComplement.ι
  let hij := i.range_eq_compl_range_openComplement_ι
  let A := ModuleCat.{u+1} R
  let p := upperStar A j
  let r := lowerStar A j
  let p' := upperStar Ab.{u+1} j
  let r' := lowerStar Ab.{u+1} j
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj (p.obj F)
  let e := (leftDerivedUpperStarIsoMapDerivedCategory A j).app M ≪≫
    p.mapDerivedCategory.mapIso m ≪≫ (p.mapDerivedCategorySingleFunctor 0).app F
  let tri := supportedLocalizationTriangle R i j M (supportedLocalizationBoundary R i j hij M)
  let T := V.mapTriangle.obj tri
  have hT : T ∈ distTriang _ := V.map_distinguished _ (supportedLocalizationTriangle_mem_distTriang R i j hij M)
  let oe : T.obj₃ ≅ r'.rightDerivedFunctor.obj _ :=
    V.mapIso (r.rightDerivedFunctor.mapIso e ≪≫ (r.rightDerivedFunctorPlusCompatibility.app K).symm) ≪≫
      ((moduleAbelianForget R X).mapDerivedCategoryPlusCompatibility.app _).symm ≪≫
      DerivedCategory.Plus.ι.mapIso ((moduleAbelianDerivedLowerStarIso R j).app K) ≪≫
      r'.rightDerivedFunctorPlusCompatibility.app _
  have zeroOpen (N) : Limits.IsZero (p'.mapDerivedCategory.obj (J.obj N)) :=
    (isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_of_disjoint_range Ab.{u+1} j i
      (hij ▸ disjoint_compl_right) N).of_iso (p'.mapDerivedCategory.mapIso
      ((lowerStar Ab.{u+1} i).rightDerivedFunctorIsoMapDerivedCategory.app N).symm)
  let ff : J.FullyFaithful :=
    (upperStarLowerStarAdjunction Ab.{u+1} i).mapDerivedCategoryAdjunction.fullyFaithfulROfIsIsoCounit
  have ortho (N) (n : ℤ) : Subsingleton ((J.obj N)⟦n⟧ ⟶ T.obj₃) := by
    have := Pretriangulated.Recollement.subsingleton_hom_shift J p'.mapDerivedCategory
      (upperStarLowerStarAdjunction Ab.{u+1} j).mapDerivedCategoryRightDerivedAdjunction
      zeroOpen N (DerivedCategory.Plus.ι.obj ((moduleAbelianForget R _).mapDerivedCategoryPlus.obj K)) n
    exact (oe.homToEquiv (Z := (J.obj N)⟦n⟧)).subsingleton
  intro N
  let rep := Pretriangulated.representableByOfDistTriang ff hT ortho
    ((closedPushForgetIso R i).app H)
  exact (rep.homEquiv (X := N)).bijective

end WeilII
