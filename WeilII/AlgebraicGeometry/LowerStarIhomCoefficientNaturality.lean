module

import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
public import WeilConjectures.WeilSheaf.DerivedHom
public import WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerStar

/-! # Coefficient naturality for the direct image of internal Hom -/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

set_option maxHeartbeats 650000 in
/-- Precomposition by a map of lisse source sheaves commutes with the underived projection
isomorphism for direct image. Transpose both composites by pullback–pushforward adjunction.
The projection then becomes the pullback comparison followed by internal Hom applied to the
counit. The two squares are geometric source naturality of the comparison and target
naturality of precomposition at the counit. -/
public theorem lowerStarIhomCoefficientNaturality
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Z : Scheme.{u}} [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    (i : Z ⟶ X) [i.IsOver (Spec (.of k))]
    {A A' : ProEtaleWeilSheaf k ℓ X} (f : A ⟶ A')
    (hA : ProEtale.IsAdicLisseSheaf A.carrier) (hA' : ProEtale.IsAdicLisseSheaf A'.carrier)
    (N : ProEtaleWeilSheaf k ℓ Z) :
    let L := ProEtaleWeilSheaf.upperStar k ℓ i
    let J := ProEtaleWeilSheaf.lowerStar k ℓ i
    (ProEtaleWeilSheaf.lowerStarCompIhomFunctorIso i A' hA').hom.app N ≫
        J.map (((ProEtaleWeilSheaf.ihomBifunctor k ℓ Z).map (L.map f).op).app N) =
      ((ProEtaleWeilSheaf.ihomBifunctor k ℓ X).map f.op).app (J.obj N) ≫
        (ProEtaleWeilSheaf.lowerStarCompIhomFunctorIso i A hA).hom.app N := by
  intro L J
  let adj : L ⊣ J := ProEtaleWeilSheaf.upperStarLowerStarAdjunction k ℓ i
  let s : ProEtaleWeilSheaf.ihomFunctor k ℓ X A' ⟶ ProEtaleWeilSheaf.ihomFunctor k ℓ X A := (ProEtaleWeilSheaf.ihomBifunctor k ℓ X).map f.op
  let t : ProEtaleWeilSheaf.ihomFunctor k ℓ Z (L.obj A') ⟶
      ProEtaleWeilSheaf.ihomFunctor k ℓ Z (L.obj A) := (ProEtaleWeilSheaf.ihomBifunctor k ℓ Z).map (L.map f).op
  let comp (B : ProEtaleWeilSheaf k ℓ X) (hB : ProEtale.IsAdicLisseSheaf B.carrier) :=
    ProEtaleWeilSheaf.ihomFunctorCompUpperStarIso i B hB
  have hs (M : ProEtaleWeilSheaf k ℓ X) :
      L.map (s.app M) ≫ (comp A hA).hom.app M =
        (comp A' hA').hom.app M ≫ t.app (L.obj M) :=
    Endofunctor.IsoAlgebra.hom_ext
      (ProEtale.adicUpperStarIhomComparison_ihomMap
        (Scheme.Hom.geometricFiberMap i (comp_over i (Spec (.of k)))) f.hom.f M.carrier)
  have square : Functor.whiskerRight s L ≫ (comp A hA).hom =
      (comp A' hA').hom ≫ Functor.whiskerLeft L t :=
    NatTrans.ext (funext hs)
  have mates := (mateEquiv_comp_whiskerLeft adj adj
      (TwoSquare.mk _ _ _ _ (comp A' hA').hom) t).symm.trans
    ((congrArg (mateEquiv adj adj) square.symm).trans
      (mateEquiv_whiskerRight_comp adj adj s (TwoSquare.mk _ _ _ _ (comp A hA).hom)))
  exact NatTrans.congr_app mates N

end WeilII
