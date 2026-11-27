module

public import WeilConjectures.PoincareDuality.CompactSupportKunneth
public import WeilConjectures.WeilSheaf.SmoothPurityFieldCompactificationExchange
public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale
import WeilII.AlgebraicGeometry.CondensedSchemePullbackBraiding
import WeilII.AlgebraicGeometry.ExceptionalProjectionSchemeIso
import WeilII.AlgebraicGeometry.ShriekBaseChangeUnderSchemeIsomorphisms
import WeilII.AlgebraicGeometry.ShriekCompositionUnderSchemeIsomorphisms
import WeilII.CategoryTheory.KunnethComparisonIso
meta import WeilConjectures.Tactic.ExactByKernel
meta import WeilII.Tactic.StructuralDefEq

/-! # Action of scheme automorphisms on the compact-support Künneth map -/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- The inverse compact-support Künneth map commutes with a system of scheme automorphisms
on the four vertices, and with arbitrary changes of coefficients. The automorphisms need
only respect the four edges as maps of underlying schemes.

Proof. Use the factorization of the specified map in the pinned
`PoincareDuality/CompactSupportKunneth.lean`. Apply projection base change to both projection
morphisms, the base-change cube to the product square, braided pullback to the two braidings,
and vertical pasting to the comparison for the composite. For the coefficient square take
the identity endofunctors and identity exchanges in the same categorical calculation. -/
public theorem compactSupportKunneth_underSchemeAutomorphisms
    {Ω : Type u} [Field Ω] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar Ω).Prime] [Fact (ringChar Ω ≠ ℓ)]
    {P X Y S : Over (Spec (.of Ω))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    {p : P ⟶ X} {s : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} (sq : IsPullback s p g f)
    (tP : P.left ≅ P.left) (tX : X.left ≅ X.left)
    (tY : Y.left ≅ Y.left) (tS : S.left ≅ S.left)
    (hp : CommSq tP.hom p.left p.left tX.hom) (hs : CommSq tP.hom s.left s.left tY.hom)
    (hf : IsPullback tX.hom f.left f.left tS.hom) (hg : IsPullback tY.hom g.left g.left tS.hom)
    (hh : IsPullback tP.hom (p ≫ f).left (p ≫ f).left tS.hom)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    letI := (monoidalCategory_boundedConstructible (ℓ := ℓ) P).toMonoidalCategoryStruct
    letI := (monoidalCategory_boundedConstructible (ℓ := ℓ) S).toMonoidalCategoryStruct
    let F := boundedConstructibleUpperStarOfMap ℓ (X := S) (Y := S) tS.hom
    let FP := boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P) tP.hom
    let FX := boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X) tX.hom
    let FY := boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y) tY.hom
    let ef := purityFieldLowerShriekBaseChange ℓ f f hf
    let eg := purityFieldLowerShriekBaseChange ℓ g g hg
    let eh := purityFieldLowerShriekBaseChange ℓ (p ≫ f) (p ≫ f) hh
    let dp := boundedConstructibleUpperStarOfMapSquareIso ℓ p p hp.w
    let ds := boundedConstructibleUpperStarOfMapSquareIso ℓ s s hs.w
    let ps := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p
    let ss := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ s
    let h := boundedConstructibleLowerShriek ℓ (p ≫ f)
    let τtgt := eh.hom.app (ps.obj K ⊗ ss.obj L) ≫
      h.map (Functor.OplaxMonoidal.δ FP _ _ ≫ (dp.hom.app K ⊗ₘ ds.hom.app L))
    let τsrc := Functor.OplaxMonoidal.δ F ((boundedConstructibleLowerShriek ℓ f).obj K)
      ((boundedConstructibleLowerShriek ℓ g).obj L) ≫ (ef.hom.app K ⊗ₘ eg.hom.app L)
    F.map (compactSupportKunnethIso ℓ sq K L).inv ≫ τtgt =
        τsrc ≫ (compactSupportKunnethIso ℓ sq (FX.obj K) (FY.obj L)).inv ∧
      ∀ {K' L'} (x : K ⟶ K') (y : L ⟶ L'),
        (compactSupportKunnethIso ℓ sq K L).inv ≫ h.map (ps.map x ⊗ₘ ss.map y) =
          ((boundedConstructibleLowerShriek ℓ f).map x ⊗ₘ (boundedConstructibleLowerShriek ℓ g).map y) ≫
            (compactSupportKunnethIso ℓ sq K' L').inv := by
  intro F FP FX FY ef eg eh dp ds ps ss h τtgt τsrc
  let := monoidalCategory_boundedConstructible (ℓ := ℓ) P
  let := monoidalCategory_boundedConstructible (ℓ := ℓ) X
  let := monoidalCategory_boundedConstructible (ℓ := ℓ) S
  let := boundedConstructibleBraiding (ℓ := ℓ) P
  let := boundedConstructibleBraiding (ℓ := ℓ) X
  let assemble := KunnethComparison.pasteIso (boundedConstructibleLowerShriek ℓ p)
    (boundedConstructibleLowerShriek ℓ f) (boundedConstructibleLowerShriek ℓ g) h ps ss
    (boundedConstructibleUpperStar _ ℓ f)
    (boundedConstructibleExceptionalProjection ℓ p) (boundedConstructibleExceptionalProjection ℓ f)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ p f)
    (fun A B ↦ (compactSupportKunnethIso ℓ sq A B).inv) (fun _ _ ↦ rfl)
  let ep := purityFieldLowerShriekBaseChange ℓ p p (IsPullback.of_horiz_isIso hp)
  let df := boundedConstructibleUpperStarOfMapSquareIso ℓ f f hf.w
  refine assemble FP FX FY F ep ef eg eh
    dp ds df ?_ ?_ ?_ ?_ ?_ ?_ K L τsrc τtgt ?_ ?_
  · dsimp +zetaDelta +instances only []
    as_aux_lemma =>
      exact_by_kernel exceptionalProjection_underSchemeIsomorphisms ℓ p p tP tX hp
  · dsimp +zetaDelta +instances only []
    as_aux_lemma =>
      exact_by_kernel exceptionalProjection_underSchemeIsomorphisms ℓ f f tX tS hf.toCommSq
  · intro B
    structural_exact shriekBaseChangeUnderSchemeIsomorphisms ℓ sq sq tP tX tY tS hs hp
      hg.toCommSq hf.toCommSq B
  · dsimp +zetaDelta +instances only []
    as_aux_lemma =>
      intro N
      exact_by_kernel shriekCompositionUnderSchemeIsomorphisms ℓ p f p f tP tX tS
        (IsPullback.of_horiz_isIso hp) hf N hh
  · dsimp +zetaDelta +instances only []
    as_aux_lemma =>
      exact_by_kernel boundedConstructibleUpperStarOfMap_braiding ℓ P P tP.hom
  · dsimp +zetaDelta +instances only []
    as_aux_lemma =>
      exact_by_kernel boundedConstructibleUpperStarOfMap_braiding ℓ X X tX.hom
  · dsimp +zetaDelta +instances only []
  · structural_rfl

end WeilII
