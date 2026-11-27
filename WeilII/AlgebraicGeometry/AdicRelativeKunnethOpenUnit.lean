module

public import WeilII.AlgebraicGeometry.AdicOpenExtensionPullback
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.TraceFormula.KunnethVerdierOpen
import WeilII.AlgebraicGeometry.AdicOpenUnitProductRealization
import WeilII.AlgebraicGeometry.AdicProductProjectionBaseChange
import WeilII.CategoryTheory.TransposeCompMate
import WeilII.CategoryTheory.MateEssentialImage
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedExchangeComparison
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.Adic.BoundedConstructibleCondensedComparison
import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedTriangle
import WeilConjectures.TraceFormula.GenericBaseChange
import WeilConjectures.TraceFormula.OrdinaryKunnethOpen

/-! # Relative Künneth with an open extension of the unit

Katz, *Affine cohomological transforms, perversity, and monodromy*, Appendix A.2, p. 219.
On a product chart, the second coefficient is the constant unit on an open subscheme,
extended by zero. Pullback along the first projection realizes external product with the unit.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilII

universe u

/-- The comparison on the product chart of Katz A.2, p. 219. For `H_W = h × 𝟙 W`
and `j_X = 𝟙 X × j`, its transpose along `H_S^* ⊣ RH_{S*}` first pulls back the
open extension, then applies `j_{X!} p_{X,V}^*` to the counit `h^* Rh_* A ⟶ A`. -/
@[expose] public noncomputable def adicRelativeKunnethOpenUnitMap
    {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] {X Y V S : Over (Spec (.of k))}
    (h : X ⟶ Y) (j : V ⟶ S) [IsOpenImmersion j.left] (A : DerivedCategory (AdicSheaf ℓ X.left)) :
    (adicOpenImmersionLowerShriek ℓ (prod.map (𝟙 Y) j).left).mapDerivedCategory.obj
        ((adicUpperStar ℓ (prod.fst : Y ⨯ V ⟶ Y).left).mapDerivedCategory.obj
          ((adicLowerStar ℓ h.left).rightDerivedFunctor.obj A)) ⟶
      (adicLowerStar ℓ (prod.map h (𝟙 S)).left).rightDerivedFunctor.obj
        ((adicOpenImmersionLowerShriek ℓ (prod.map (𝟙 X) j).left).mapDerivedCategory.obj
          ((adicUpperStar ℓ (prod.fst : X ⨯ V ⟶ X).left).mapDerivedCategory.obj A)) := by
  have sq : IsPullback (prod.map h (𝟙 V)).left (prod.map (𝟙 X) j).left
      (prod.map (𝟙 Y) j).left (prod.map h (𝟙 S)).left :=
    (CondensedRing.isPullback_prodMap_prodMap h j).map (Over.forget _)
  let pr := (IsPullback.of_prod_fst_with_id h V).map (Over.forget _)
  let B := (adicLowerStar ℓ h.left).rightDerivedFunctor.obj A
  haveI := isIso_adicOpenExtensionPullbackMap ℓ sq
  exact (adicDerivedUpperStarLowerStarAdjunction ℓ (prod.map h (𝟙 S)).left).homEquiv _ _
    ((asIso (adicOpenExtensionPullbackMap ℓ sq.toCommSq)).inv.app
        ((adicUpperStar ℓ (prod.fst : Y ⨯ V ⟶ Y).left).mapDerivedCategory.obj B) ≫
      (adicOpenImmersionLowerShriek ℓ (prod.map (𝟙 X) j).left).mapDerivedCategory.map
        ((adicDerivedPullSquare ℓ pr.toCommSq).hom.app B ≫
          (adicUpperStar ℓ (prod.fst : X ⨯ V ⟶ X).left).mapDerivedCategory.map
            ((adicDerivedUpperStarLowerStarAdjunction ℓ h.left).counit.app A)))

/-- Relative ordinary Künneth with second factor the extension by zero of the unit,
for a constructible geometric adic sheaf in degree zero. Katz A.2, p. 219, uses the
ordinary and compact-support Künneth formulas on this product chart, citing
SGA 4, XVII 5.4.3, and SGA 4½, *Théorèmes de finitude*, 4.3.

Proof. Put M = K[0] and H_W = h × 1_W. Product base change over V identifies
the pullback of Rh_*M with RH_{V*} of the pullback of M. The bounded Künneth
boundary-vanishing theorem, transported through the coefficient equivalence, shows
that RH_{S*} of the open extension on X × S lies in the essential image of the
open extension on Y × S. Both open extensions are fully faithful. Consequently
the mate of the pullback square is invertible at the pullback of M to X × V.
Composing this mate with the open extension of product base change gives the
specified arrow: transposition and the mate–counit identity give exactly the
displayed pullback of the counit of h. -/
public theorem isIso_adicRelativeKunnethOpenUnitMap
    (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k₀ ≠ ℓ)]
    {X Y V S : Over (Spec (.of (AlgebraicClosure k₀)))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    (h : X ⟶ Y) [LocallyOfFiniteType h.left] [QuasiCompact h.left] [IsSeparated h.left]
    (j : V ⟶ S) [IsOpenImmersion j.left] [QuasiCompact j.left]
    (K : AdicSheaf ℓ X.left) (hK : IsAdicConstructibleSheaf K) :
    IsIso (adicRelativeKunnethOpenUnitMap ℓ h j ((DerivedCategory.singleFunctor _ 0).obj K)) := by
  classical
  let k := AlgebraicClosure k₀
  have : Fact (ringChar k).Prime := ⟨Algebra.ringChar_eq k₀ k ▸ CharP.prime_ringChar k₀⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨Algebra.ringChar_eq k₀ k ▸ (Fact.out : ringChar k₀ ≠ ℓ)⟩
  have : LocallyOfFiniteType V.hom := by rw [← Over.w j]; infer_instance
  have : QuasiCompact V.hom := by rw [← Over.w j]; infer_instance
  have : IsSeparated V.hom := by rw [← Over.w j]; infer_instance
  let M := (DerivedCategory.singleFunctor _ 0).obj K
  let pr := (IsPullback.of_prod_fst_with_id h V).map (Over.forget _)
  let sq : IsPullback (prod.map h (𝟙 V)).left (prod.map (𝟙 X) j).left
      (prod.map (𝟙 Y) j).left (prod.map h (𝟙 S)).left :=
    (CondensedRing.isPullback_prodMap_prodMap h j).map (Over.forget _)
  let a := adicDerivedUpperStarLowerStarAdjunction ℓ (prod.map h (𝟙 V)).left
  let b := adicDerivedUpperStarLowerStarAdjunction ℓ (prod.map h (𝟙 S)).left
  let c := adicDerivedUpperStarLowerStarAdjunction ℓ h.left
  let p := (adicUpperStar ℓ (prod.fst : X ⨯ V ⟶ X).left).mapDerivedCategory
  let J := (adicOpenImmersionLowerShriek ℓ (prod.map (𝟙 Y) j).left).mapDerivedCategory
  let J' := (adicOpenImmersionLowerShriek ℓ (prod.map (𝟙 X) j).left).mapDerivedCategory
  let P := (adicDerivedBaseChange ℓ pr.toCommSq).app M
  have hP : IsIso P := isIso_adicProductProjectionBaseChange ℓ V h K hK
  have := isIso_adicOpenExtensionPullbackMap ℓ sq
  let θ := (asIso (adicOpenExtensionPullbackMap ℓ sq.toCommSq)).symm
  let N := p.obj M
  let m := (mateEquiv a b θ.hom).app N
  let ff {U T : Scheme.{u}} (i : U ⟶ T) [IsOpenImmersion i] :
      (adicOpenImmersionLowerShriek ℓ i).mapDerivedCategory.FullyFaithful := by
    have := (Adjunction.Triple.isIso_unit_iff_isIso_counit
      ⟨adicDerivedOpenExtensionAdjunction ℓ i, adicDerivedUpperStarLowerStarAdjunction ℓ i⟩).2
      (isIso_adicDerivedUpperStarLowerStarAdjunction_counit_of_isOpenImmersion i)
    exact (adicDerivedOpenExtensionAdjunction ℓ i).fullyFaithfulLOfIsIsoUnit
  have hm : IsIso m := isIso_mate_app_of_essImage a b (ff _) (ff _) θ N
    (adicOpenUnitProduct_essImage ℓ h j K hK)
  suffices adicRelativeKunnethOpenUnitMap ℓ h j M = J.map P ≫ m by
    rw [show (DerivedCategory.singleFunctor _ 0).obj K = M from rfl, this]
    infer_instance
  have htrans : (a.homEquiv _ _).symm P =
      (adicDerivedPullSquare ℓ pr.toCommSq).hom.app ((adicLowerStar ℓ h.left).rightDerivedFunctor.obj M) ≫
        p.map (c.counit.app M) := mateEquiv_counit c a (adicDerivedPullSquare ℓ pr.toCommSq).hom M
  change b.homEquiv _ _ (θ.hom.app _ ≫ J'.map _) = _
  rw [← htrans]
  exact homEquiv_comp_mate a b θ.hom P

end WeilII
