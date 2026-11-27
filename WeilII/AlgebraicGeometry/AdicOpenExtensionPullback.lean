module

public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedBaseChange
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
import WeilConjectures.WeilSheaf.BaseChangeField.Coherence
import WeilConjectures.WeilSheaf.CondensedModelGeometricFiberPullback
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilII.AlgebraicGeometry.AdicSheafOpenExtensionPullback

/-! # Pullback of extension by zero for geometric adic complexes

Katz, *Affine cohomological transforms, perversity, and monodromy*, Appendix A.2–A.3,
pp. 218–220, uses this comparison to restrict an open extension by zero to a parameter fibre.
The coefficients here are native geometric adic sheaves on the small pro-étale site. -/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilII

universe u

/-- The adjunction `D(j_!) ⊣ D(j^*)` for an open immersion, used in Katz A.2–A.3.
Localize the termwise adjunction of exact functors at quasi-isomorphisms. -/
@[expose] public noncomputable def adicDerivedOpenExtensionAdjunction
    (ℓ : ℕ) [Fact ℓ.Prime] {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] :
    (adicOpenImmersionLowerShriek ℓ j).mapDerivedCategory ⊣
      (adicUpperStar ℓ j).mapDerivedCategory := by
  let L := adicOpenImmersionLowerShriek ℓ j
  let R := adicUpperStar ℓ j
  let _ : CatCommSq (L.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q L.mapDerivedCategory := ⟨L.mapDerivedCategoryFactors.symm⟩
  let _ : CatCommSq (R.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q R.mapDerivedCategory := ⟨R.mapDerivedCategoryFactors.symm⟩
  exact ((adicOpenImmersionLowerShriekAdjunction ℓ j).mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    L.mapDerivedCategory R.mapDerivedCategory

/-- The comparison `j′_! a^* ⟶ b^* j_!` in Katz A.2–A.3. Its component at `A` is
adjoint to the pullback of the unit `A ⟶ j^* j_! A` followed by the commutative square
of inverse images. -/
@[expose] public noncomputable def adicOpenExtensionPullbackMap
    (ℓ : ℕ) [Fact ℓ.Prime] {U' U T Y : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ T}
    {j : U ⟶ Y} {b : T ⟶ Y} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : CommSq a j' j b) :
    (adicUpperStar ℓ a).mapDerivedCategory ⋙
        (adicOpenImmersionLowerShriek ℓ j').mapDerivedCategory ⟶
      (adicOpenImmersionLowerShriek ℓ j).mapDerivedCategory ⋙
        (adicUpperStar ℓ b).mapDerivedCategory :=
  (mateEquiv (adicDerivedOpenExtensionAdjunction ℓ j)
    (adicDerivedOpenExtensionAdjunction ℓ j')).symm
      (TwoSquare.mk _ _ _ _ (adicDerivedPullSquare ℓ sq.flip).hom)

/-- In a cartesian square, pullback commutes with open extension by zero on unbounded
geometric adic complexes (Katz, Appendix A.2–A.3, pp. 218–220).

On sheaves take the inverse mate of the pullback square along the two open-extension
adjunctions. Its mate along those adjunctions recovers the pullback square. Taking the
mate again, along the pullback–direct-image adjunctions for `a` and `b`, gives the
ordinary base-change map `j^* b_* ⟶ a_* j′^*`. Indeed, transposing the two pullback
composition isomorphisms and the intervening equality gives the pushforward composition
square that defines ordinary base change. Both open immersions are weakly étale, so
this last map is invertible. The iterated mate is conjugation between the composite
adjunctions. Conjugating the inverse gives the inverse of the open-extension map.

All four functors of the open-extension square are exact. Apply them termwise and
localize at quasi-isomorphisms to obtain an isomorphism. On a complex, transposing it
gives the termwise pullback of the open-extension unit followed by the pullback square.
The localization formula for the unit and faithfulness of precomposition with the
localization identify this transpose on the derived category. Its inverse mate is
precisely `adicOpenExtensionPullbackMap`. -/
public theorem isIso_adicOpenExtensionPullbackMap
    (ℓ : ℕ) [Fact ℓ.Prime] {U' U T Y : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ T}
    {j : U ⟶ Y} {b : T ⟶ Y} [IsOpenImmersion j] (sq : IsPullback a j' j b) :
    letI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq ‹IsOpenImmersion j›
    IsIso (adicOpenExtensionPullbackMap ℓ sq.toCommSq) := by
  letI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq ‹IsOpenImmersion j›
  have := isIso_adicSheafOpenExtensionPullbackMate ℓ sq
  exact (exact_localization_inverse_mate (adicOpenImmersionLowerShriekAdjunction ℓ j)
    (adicOpenImmersionLowerShriekAdjunction ℓ j') (adicUpperStarCompIso ℓ sq.w)).1

end WeilII
