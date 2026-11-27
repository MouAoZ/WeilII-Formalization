module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilII.CategoryTheory.ResolutionMateComparison
import WeilII.AlgebraicGeometry.EtaleForgottenSupportCounit

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilII

universe u

/-- Compare exceptional exchange on a degree-zero finite module input with its abelian
support mate on any two K-injective representatives. The change of representative after
pullback need only become invertible under localization. The counits represent maps from
closed direct images, and the two mate identities compare their composites over the base. -/
public theorem etaleSupportMateOfRepresentatives
    (R : Type (u + 1)) [CommRing R] [Finite R] {X Z U X' Z' U' : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range i = (Set.range j)ᶜ)
    (d : Z' ⟶ X') [IsClosedImmersion d] (v : U' ⟶ X') [IsOpenImmersion v]
    (hdv : Set.range d = (Set.range v)ᶜ)
    (p : X' ⟶ X) (s : Z' ⟶ Z) (sq : IsPullback s d i p)
    (e : Etale.lowerStar Ab.{u + 1} i ⋙ Etale.upperStar Ab.{u + 1} p ≅
      Etale.upperStar Ab.{u + 1} s ⋙ Etale.lowerStar Ab.{u + 1} d)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u+1} R))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} R)))
    (m : M ≅ (DerivedCategory.singleFunctor _ 0).obj F)
    (L : CochainComplex (Sheaf X.smallEtaleTopology Ab.{u+1}) ℤ) [L.IsKInjective]
    (x : DerivedCategory.Q.obj L ≅ (Etale.moduleAbelianForget R X).mapDerivedCategory.obj M)
    (K' : CochainComplex (Sheaf X'.smallEtaleTopology Ab.{u+1}) ℤ) [K'.IsKInjective]
    (r : ((Etale.upperStar Ab.{u+1} p).mapHomologicalComplex (.up ℤ)).obj L ⟶ K')
    [IsIso (DerivedCategory.Q.map r)] :
    let S := Etale.closedUpperShriek Ab.{u + 1} i j
    let D := Etale.closedUpperShriek Ab.{u + 1} d v
    let P := Etale.upperStar Ab.{u + 1} p
    let PZ := Etale.upperStar Ab.{u + 1} s
    let β := mateEquiv (Etale.lowerStarClosedUpperShriekAdjunction _ i j hij)
      (Etale.lowerStarClosedUpperShriekAdjunction _ d v hdv)
      (TwoSquare.mk _ _ _ _ e.inv)
    let t := (Functor.mapHomologicalComplexCompIso (F := S) (G := PZ) (Iso.refl _) (.up ℤ)).hom ≫
      β.mapHomologicalComplex (.up ℤ) ≫
      (Functor.mapHomologicalComplexCompIso (F := P) (G := D) (Iso.refl _) (.up ℤ)).inv
    let f := t.app L ≫ (D.mapHomologicalComplex (.up ℤ)).map r
    Nonempty (Arrow.mk (DerivedCategory.Q.map f) ≅
      Arrow.mk ((Etale.moduleAbelianForget R Z').mapDerivedCategory.map
        ((Etale.rightDerivedUpperShriekBaseChangeMap R sq).app M))) := by
  classical
  intro S D P PZ β t f
  let V (Y : Scheme.{u}) := (Etale.moduleAbelianForget R Y).mapDerivedCategory
  let I := Etale.lowerStar AddCommGrpCat.{u+1} i
  let J := Etale.lowerStar AddCommGrpCat.{u+1} d
  let a := Etale.lowerStarClosedUpperShriekAdjunction AddCommGrpCat.{u+1} i j hij
  let b := Etale.lowerStarClosedUpperShriekAdjunction AddCommGrpCat.{u+1} d v hdv
  let pm := Etale.upperStar (ModuleCat.{u+1} R) p
  let pmD := pm.leftDerivedFunctor
  let χ : V X ⋙ P.mapDerivedCategory ≅ pmD ⋙ V X' :=
    Functor.mapDerivedCategoryCompIso (Etale.moduleAbelianForget R X) P ≪≫
      Functor.mapDerivedCategoryNatIso (Etale.moduleAbelianUpperStarIso R p) ≪≫
      (Functor.mapDerivedCategoryCompIso pm (Etale.moduleAbelianForget R X')).symm ≪≫
      Functor.isoWhiskerRight (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u+1} R) p).symm (V X')
  have hi := forgottenSupportCounit_bijective R i M F m
  let m' := (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u+1} R) p).app M ≪≫
    pm.mapDerivedCategory.mapIso m ≪≫ (pm.mapDerivedCategorySingleFunctor 0).app F
  have hd := forgottenSupportCounit_bijective R d (pmD.obj M) (pm.obj F) m'
  have ff : J.mapDerivedCategory.FullyFaithful :=
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u+1} d).mapDerivedCategoryAdjunction.fullyFaithfulROfIsIsoCounit
  let am := Etale.rightDerivedUpperShriekAdjunction R i
  let bm := Etale.rightDerivedUpperShriekAdjunction R d
  let bc := Etale.rightDerivedLowerShriekBaseChangeMap R sq
  have hbc : IsIso bc := Etale.isIso_rightDerivedLowerShriekBaseChangeMap R sq
  have hbase : Etale.rightDerivedUpperShriekBaseChangeMap R sq =
      mateEquiv am bm (TwoSquare.mk _ _ _ _ (asIso bc).inv) := rfl
  rw [hbase]
  exact resolutionMate_compare_of_counit_bijections
    (I := I) (S := S) (J := J) (H := D) (P := P) (U := PZ)
    (W := V Z) (W' := V Z') (V := V X) (V' := V X')
    (Pₘ := pmD) (Uₘ := (Etale.upperStar (ModuleCat.{u+1} R) s).leftDerivedFunctor)
    a b e am bm (asIso bc)
    (closedPushForgetIso R i) (closedPushForgetIso R d) χ ff M L x K' r hi hd

end WeilII
