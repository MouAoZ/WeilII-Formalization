module

public import WeilConjectures.WeilSheaf.SmoothPurityFieldCompactificationExchange

/-! # Compactification exchange in inverse pushforward coordinates -/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII.NativePointShriek

universe u

private theorem convertExchange {A B : Type*} [Category A] [Category B] (R : A ⥤ B)
    {L F G : A ⥤ A} {M H T : B ⥤ B} (x : L ≅ F) (v : F ≅ G)
    (s : M ≅ H) (y : H ≅ T) (b : R ⋙ H ≅ F ⋙ R)
    (field : R ⋙ M ≅ L ⋙ R)
    (hfield : field = Functor.isoWhiskerLeft R s ≪≫ b ≪≫ Functor.isoWhiskerRight x.symm R)
    (K : A) (u : T.obj (R.obj K) ⟶ R.obj (G.obj K))
    (h : y.hom.app (R.obj K) ≫ u = b.hom.app K ≫ R.map (v.hom.app K)) :
    (s ≪≫ y).hom.app (R.obj K) ≫ u = field.hom.app K ≫ R.map ((x ≪≫ v).hom.app K) := by
  subst field
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    Category.assoc, h, ← R.map_comp, x.inv_hom_id_app_assoc]

variable {ℓ : ℕ} [Fact ℓ.Prime]
local notation "Λ" => Profinite.padicAlgClRingObj ℓ
local notation "exactToInv" e => Functor.mapDerivedCategoryNatIso (upperStarIsoLowerStarInv Λ e)
local notation "derivedToInv" e =>
  leftDerivedUpperStarIsoMapDerivedCategory Λ (Iso.hom e) ≪≫ exactToInv e

/-- An exchange identity in exact pullback coordinates gives the corresponding field
compactification exchange identity in left-derived pullback coordinates. -/
theorem fieldExchangeOfExact {κ : Type u} [Field κ] [Fact (ringChar κ).Prime]
    [Fact (ringChar κ ≠ ℓ)] {U V : Over (Spec (.of κ))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (f : U ⟶ V) (c : Compactification f.left) (x : U.left ≅ U.left) (y : V.left ≅ V.left)
    (r : c.Z ⟶ c.Z) [WeaklyEtale r] (hi : IsPullback c.i x.hom r c.i)
    (hg : IsPullback r c.g c.g y.hom)
    (K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u+1})
      (condensedRingObj Λ U.left)))
    (a : (CondensedRing.lowerStar Λ y.inv).mapDerivedCategory.obj
        (Rf_!(c)⟦Λ⟧.obj K) ⟶
      Rf_!(c)⟦Λ⟧.obj ((CondensedRing.lowerStar Λ x.inv).mapDerivedCategory.obj K))
    (h : (exactToInv y).hom.app (Rf_!(c)⟦Λ⟧.obj K) ≫ a =
      (rightDerivedLowerShriekOfCompactificationBaseChangeIso Λ c c hi hg).hom.app K ≫
        Rf_!(c)⟦Λ⟧.map ((exactToInv x).hom.app K)) :
    (derivedToInv y).hom.app (Rf_!(c)⟦Λ⟧.obj K) ≫ a =
      (purityFieldCompactificationAmbientExchange ℓ f f c c hi hg).hom.app K ≫
        Rf_!(c)⟦Λ⟧.map ((derivedToInv x).hom.app K) := by
  exact convertExchange Rf_!(c)⟦Λ⟧
    (leftDerivedUpperStarIsoMapDerivedCategory Λ x.hom) (exactToInv x)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ y.hom) (exactToInv y)
    (rightDerivedLowerShriekOfCompactificationBaseChangeIso Λ c c hi hg)
    (purityFieldCompactificationAmbientExchange ℓ f f c c hi hg) rfl K a h

end WeilII.NativePointShriek
