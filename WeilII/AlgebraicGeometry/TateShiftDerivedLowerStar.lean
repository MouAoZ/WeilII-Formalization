module

public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.Localization

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- A derived direct image of Weil complexes commutes with Tate twist and shift. A Tate
twist multiplies the Frobenius datum by a scalar, which commutes with derived direct image
by `ProEtaleWeilSheaf.mapDerivedCategoryConstantTwistCompIso`. Restrict this exchange to
bounded constructible complexes and compose it with shift compatibility. -/
public noncomputable def tateShiftDerivedLowerStarIso
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    (m s : ℤ) :
    (WeilComplex.tateTwist k ℓ X m ⋙ shiftFunctor _ s) ⋙ WeilComplex.derivedLowerStar f ≅
      WeilComplex.derivedLowerStar f ⋙ WeilComplex.tateTwist k ℓ Y m ⋙ shiftFunctor _ s := by
  let D := WeilComplex.derivedLowerStar (k₀ := k) (l := ℓ) f
  let eD : D ⋙ (WeilComplex.objectProperty k ℓ Y).ι ≅
      (WeilComplex.objectProperty k ℓ X).ι ⋙ (ProEtaleWeilSheaf.lowerStar k ℓ f).rightDerivedFunctor :=
    ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _
  let tw : WeilComplex.tateTwist k ℓ X m ⋙ D ≅ D ⋙ WeilComplex.tateTwist k ℓ Y m :=
    ((WeilComplex.objectProperty k ℓ Y).fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ eD ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (WeilComplex.tateTwistCompιIso m) _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
          (ProEtaleWeilSheaf.mapDerivedCategoryConstantTwistCompIso k ℓ f _) ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eD.symm _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
          (WeilComplex.tateTwistCompιIso m).symm ≪≫ (Functor.associator _ _ _).symm)
  exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (D.commShiftIso s) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight tw _ ≪≫ Functor.associator _ _ _

end WeilII
