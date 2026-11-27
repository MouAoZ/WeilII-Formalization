module

public import WeilConjectures.WeilSheaf.CondensedModelBaseChange
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # The unit equation for an ambient open-extension comparison -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilII

universe u

/-- The ambient unit equation for a proposed open-extension comparison at one object.
The two arrows end in the restriction along the primed open immersion of the lower
horizontal pullback. The pure pullback comparison is oriented from the upper path to
the lower path by passing to the flipped square. -/
@[expose] public def DerivedOpenExtensionUnitEquation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {U Z U' Z' : Scheme.{u}} {j : U ⟶ Z} {j' : U' ⟶ Z'} [IsOpenImmersion j] [IsOpenImmersion j']
    {p : U' ⟶ U} {q : Z' ⟶ Z} (sq : CommSq p j' j q)
    (K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)))
    (s : D((j')_!open⟦Λ⟧).obj (L((p)^*⟦Λ⟧).obj K) ⟶ L((q)^*⟦Λ⟧).obj (D((j)_!open⟦Λ⟧).obj K)) : Prop :=
    let cj := leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j
    let cj' := leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j'
    let a := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j
    let a' := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j'
    (a'.ofNatIsoRight cj'.symm).unit.app (L((p)^*⟦Λ⟧).obj K) ≫
        L((j')^*⟦Λ⟧).map s =
      L((p)^*⟦Λ⟧).map ((a.ofNatIsoRight cj.symm).unit.app K) ≫
        (pullbackSquareComparison Λ sq.flip).hom.app (D((j)_!open⟦Λ⟧).obj K)

end WeilII

