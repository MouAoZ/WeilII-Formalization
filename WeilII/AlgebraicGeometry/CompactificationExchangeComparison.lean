module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeIndependence

/-! # Compactification comparisons for individually specified cartesian squares -/

public noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilII

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

local notation "Λ" => Profinite.padicAlgClRingObj ℓ
local notation "J" => boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ

/-- The comparison with the ambient compactified functor has identity components:
both restricted functors are lifts along the full-subcategory inclusion. -/
theorem compactificationCompatibility_component (c : Compactification f.left)
    (K : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c).app K = Iso.refl _ := by
  apply Iso.ext
  let P := R((c.g)_*⟦Λ⟧)
  change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ P.map (𝟙 _) ≫ 𝟙 _ = 𝟙 _
  exact (Category.id_comp _).trans ((Category.id_comp _).trans ((Category.id_comp _).trans
    ((Category.comp_id _).trans (P.map_id _))))

/-- Change of compactification on the underlying derived object, in the coordinates of
the ambient open extension followed by the proper direct image. -/
@[expose] def ambientCompactificationComparison (c d : Compactification f.left)
    (K : Dᵇc(X.left)⟦Λ⟧) :
    (rightDerivedLowerShriekOfCompactification Λ c).obj K.obj ≅
      (rightDerivedLowerShriekOfCompactification Λ d).obj K.obj :=
  (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c).symm.app K ≪≫
    (boundedConstructible _).ι.mapIso
      ((boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ c d).app K) ≪≫
    (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ d).app K

/-- The component written in terms of inclusion and the two boundary compatibilities. -/
theorem ambientCompactificationComparison_formula (a b : Compactification f.left)
    (K : Dᵇc(X.left)⟦Λ⟧) :
    (ambientCompactificationComparison ℓ a b K).hom =
      (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ a).inv.app K ≫
        (boundedConstructible _).ι.map
          ((boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ a b).hom.app K) ≫
        (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ b).hom.app K := rfl

/-- In ambient coordinates the compatibility isomorphisms of the middle
compactification cancel, so the comparison still satisfies the cocycle identity. -/
theorem ambientCompactificationComparison_trans (a b c : Compactification f.left)
    (K : Dᵇc(X.left)⟦Λ⟧) :
    (ambientCompactificationComparison ℓ a b K).hom ≫
      (ambientCompactificationComparison ℓ b c K).hom =
        (ambientCompactificationComparison ℓ a c K).hom := by
  have h := congr_app (congrArg Iso.hom
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans ℓ a b c)) K
  simp only [Iso.trans_hom, NatTrans.comp_app] at h
  simp only [ambientCompactificationComparison, boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_eq',
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, h]

/-- Forgetting the bounded comparison gives the ambient comparison in the coordinates
of the open extension and the proper direct image. -/
theorem ambientCompactificationComparison_hom (a b : Compactification f.left)
    (K : Dᵇc(X.left)⟦Λ⟧) :
    (ambientCompactificationComparison ℓ a b K).hom = ((J a b).hom.app K).hom := by
  have ha := congrArg Iso.inv (compactificationCompatibility_component ℓ a K)
  have hb := congrArg Iso.hom (compactificationCompatibility_component ℓ b K)
  change (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ a).inv.app K = 𝟙 _ at ha
  change (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ b).hom.app K = 𝟙 _ at hb
  simp only [ambientCompactificationComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, ha, hb, ObjectProperty.ι_map, boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_eq']
  exact (Category.id_comp _).trans (Category.comp_id _)

variable {X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Exchange intertwines both comparisons for arbitrary cartesian representatives.
The fixed BaseChangeIndependence theorem gives this for the chosen pullbacks.
For each given representative, append its comparison to the chosen pullback
exchange. The comparison cocycle identifies the two resulting composites. -/
theorem compactificationExchange_comparison (sq : IsPullback g' f' f g)
    (a b : Compactification f.left) (a' b' : Compactification f'.left)
    (r : a'.overObj ⟶ a.overObj) (s : b'.overObj ⟶ b.overObj)
    (hi : IsPullback g' a'.overI a.overI r) (hp : IsPullback r a'.overG a.overG g)
    (ji : IsPullback g' b'.overI b.overI s) (jp : IsPullback s b'.overG b.overG g) :
    Functor.whiskerRight (J a b).hom (boundedConstructibleUpperStar Λ ℓ g) ≫
      boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ b b' s ji jp =
    boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ a a' r hi hp ≫
      Functor.whiskerLeft (boundedConstructibleUpperStar Λ ℓ g') (J a' b').hom := by
  rw [boundedConstructibleLowerShriekOfCompactificationBaseChange_padicAlgCl_eq ℓ sq b b' s ji jp,
    boundedConstructibleLowerShriekOfCompactificationBaseChange_padicAlgCl_eq ℓ sq a a' r hi hp,
    ← Category.assoc,
    boundedConstructibleLowerShriekOfCompactificationBaseChange_padicAlgCl_iso' ℓ sq a b]
  simp only [Category.assoc, ← Functor.whiskerLeft_comp, ← Iso.trans_hom,
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans]

end WeilII
