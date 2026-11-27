module

public import WeilConjectures.WeilSheaf.SmoothPurityFieldPastedExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.OpenImmersionBaseChange
import WeilII.AlgebraicGeometry.BoundedOpenExchangeComponent
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # The open factor of compactification base change -/

public noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (c : Compactification f.left) (d : Compactification f'.left) (r : d.overObj ⟶ c.overObj)
  (hi : IsPullback g' d.overI c.overI r) (hp : IsPullback r d.overG c.overG g)

/-- The inverse open comparison in the slice descends to the inverse derived sheaf
exchange.  Source: SmoothPurityFieldPastedExchange and OpenImmersionBaseChange. -/
theorem compactification_open_factor [@WeaklyEtale d.Z c.Z r.left] :
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso (Profinite.padicAlgClRingObj ℓ)
      ℓ hi).hom = (purityFieldOpenRestrictedExchange ℓ f f' c d hi.overLeft.flip).hom := by
  let Λ := Profinite.padicAlgClRingObj ℓ
  let z : d.Z ⟶ c.Z := r.left
  have : WeaklyEtale z := ‹@WeaklyEtale d.Z c.Z r.left›
  let si : IsPullback d.i g'.left z c.i := hi.overLeft.flip
  let eo := boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ hi
  let ef := purityFieldOpenRestrictedExchange ℓ f f' c d si
  apply NatTrans.ext
  funext K
  have hopen : eo.inv.app K = ef.inv.app K := by
    apply ObjectProperty.hom_ext
    have : WeaklyEtale g'.left := MorphismProperty.of_isPullback si ‹WeaklyEtale z›
    let J' := D((d.i)_!open⟦Λ⟧)
    let E := purityFieldOpenAmbientExchange ℓ f f' c d si
    have hf : (ef.inv.app K).hom = E.inv.app K.obj := by
      have he := ObjectProperty.preimageIso_liftSquareWithComparisons_inv_app_hom
        (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ c.overI)
        (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ d.overI)
        (fun M ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g'.left M.obj M.property)
        (fun M ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ z M.obj M.property)
        E K
      refine he.trans ?_
      change 𝟙 _ ≫ E.inv.app K.obj ≫ L((z)^*⟦Λ⟧).map (𝟙 _) = _
      exact (Category.id_comp _).trans ((congrArg (E.inv.app K.obj ≫ ·)
        (L((z)^*⟦Λ⟧).map_id _)).trans (Category.comp_id _))
    have he : E.inv.app K.obj = J'.map
        ((leftDerivedUpperStarIsoMapDerivedCategory Λ g'.left).hom.app K.obj) ≫
        (openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ si).inv.app K.obj ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ z).inv.app (D((c.i)_!open⟦Λ⟧).obj K.obj) := by
      simp only [E, purityFieldOpenAmbientExchange, Iso.trans_inv, NatTrans.comp_app,
        Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Iso.symm_inv, Category.assoc]
      rfl
    exact (boundedOpenExchange_inv_app_hom Λ ℓ hi K).trans (hf.trans he).symm
  have ho : eo.hom.app K = ef.hom.app K :=
    congrArg Iso.inv (Iso.ext hopen : (eo.app K).symm = (ef.app K).symm)
  exact ho

end WeilII
