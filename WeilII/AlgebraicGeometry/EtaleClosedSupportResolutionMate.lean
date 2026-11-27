module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilII.AlgebraicGeometry.EtaleSupportMateRepresentatives
import WeilII.AlgebraicGeometry.EtaleResolvedConstant

/-! # The finite-coefficient closed-support mate on abelian resolutions -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilII

universe u

/-- For a finite constant coefficient, the exceptional base-change arrow after forgetting scalars
is isomorphic to the abelian support mate computed with functorial K-injective resolutions.

Sources: SGA 4, XVI, 3.7 (localization), and the proper comparison in the pinned
`SixFunctors/Etale/Derived/UpperShriekCanonicalMaps`. Forgetting scalar actions is exact and
commutes with inverse image and closed direct image. On bounded-below inputs it also commutes
with the derived open direct image: on each étale slice, cohomology is derived Hom out of the
free sheaf on the slice. Extending that free abelian sheaf to the coefficient ring gives the
free coefficient sheaf without higher Tor. Derived adjunction identifies the two section
complexes, compatibly with restriction. The localization fibre thus identifies the two derived
closed-support functors, with their counits given by the same inclusion of supported sections.
For a closed immersion compactly supported direct image agrees with closed direct image and is
exact. The compact-support exchange becomes the closed direct-image base-change map under this
identification (by proper base change and the adjunction counit). Taking the mate of its inverse
therefore identifies the forgotten finite exceptional exchange with the abelian derived mate.
Represent the source by the indicated resolution of the finite constant. Pull it back and apply
the unit of the geometric K-injective resolution before computing support on the target.
The mate's counit identity now gives exactly the composite below after localization. The source
and target comparison maps are isomorphisms, so invertibility of the finite exchange makes
this composite a quasi-isomorphism. The comparisons of source and target give the asserted
isomorphism in the arrow category. -/
public theorem etaleClosedSupportResolutionMate
    (R : Type (u + 1)) [CommRing R] [Finite R] {X Z U X' Z' U' : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range i = (Set.range j)ᶜ)
    (d : Z' ⟶ X') [IsClosedImmersion d] (v : U' ⟶ X') [IsOpenImmersion v]
    (hdv : Set.range d = (Set.range v)ᶜ)
    (p : X' ⟶ X) (s : Z' ⟶ Z) (sq : IsPullback s d i p)
    (e : Etale.lowerStar Ab.{u + 1} i ⋙ Etale.upperStar Ab.{u + 1} p ≅
      Etale.upperStar Ab.{u + 1} s ⋙ Etale.lowerStar Ab.{u + 1} d)
    (_he : e.hom = Etale.baseChangeMap Ab.{u + 1} sq.toCommSq) :
    let M := (DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R))
    let L := (CochainComplex.kInjectiveResolutionFunctor _).obj
      ((CochainComplex.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj (AddCommGrpCat.of R)))
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
    let η := CochainComplex.toKInjectiveResolution (Sheaf X'.smallEtaleTopology Ab.{u + 1})
    let q := Functor.whiskerLeft (P.mapHomologicalComplex (.up ℤ))
      (Functor.whiskerRight η (D.mapHomologicalComplex (.up ℤ)))
    let f := (t ≫ q).app L
    Nonempty (Arrow.mk (DerivedCategory.Q.map f) ≅
      Arrow.mk ((Etale.moduleAbelianForget R Z').mapDerivedCategory.map
        ((Etale.rightDerivedUpperShriekBaseChangeMap R sq).app M))) := by
  classical
  intro M L S D P PZ β t η q f
  let F := (constantSheaf X.smallEtaleTopology (ModuleCat.{u+1} R)).obj (ModuleCat.of R R)
  let G := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u+1}).obj (AddCommGrpCat.of R)
  let K := (CochainComplex.singleFunctor _ 0).obj G
  let V (Y : Scheme.{u}) := (Etale.moduleAbelianForget R Y).mapDerivedCategory
  let Kp := (P.mapHomologicalComplex (.up ℤ)).obj L
  let K' := (CochainComplex.kInjectiveResolutionFunctor _).obj Kp
  let r := η.app Kp
  have isoRes {Y : Scheme.{u}} (N : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u+1}) ℤ) :
      IsIso (DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution _).app N)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ N).2
  have := isoRes (Y := X) K
  have hr : IsIso (DerivedCategory.Q.map r) := isoRes (Y := X') Kp
  let x : DerivedCategory.Q.obj L ≅ (V X).obj M :=
    (asIso (DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution _).app K))).symm ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app G).symm ≪≫
      (etaleForgetRegularSingleIso R X).symm
  exact etaleSupportMateOfRepresentatives R i j hij d v hdv p s sq e F M (Iso.refl _)
    L x K' r

end WeilII
