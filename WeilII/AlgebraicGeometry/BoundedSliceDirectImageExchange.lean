module

public import WeilConjectures.WeilSheaf.SmoothPurityProperTraceCoordinates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedExchangeAmbient
import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste

/-! # Ordinary base change in a field slice and on the underlying schemes -/

public noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilII

universe u

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar
  residueExchangeAdjunction residueExchangeUpperStarComp

private theorem residueExchange_eq_baseChangeMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {p' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (s : CommSq g' p' p g) : residueExchangeBaseChange Λ s = baseChangeMap Λ s := by
  simp only [CondensedRing.baseChangeMap, Adjunction.exchangeRight_eq_mateEquiv, residueExchangeBaseChange,
    residueExchangeSquare, transportedCompositeIso_eq, pullbackSquareComparison]
  rfl

private theorem boundedSliceResidue
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)] {X Y X' Y' : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    {p : X ⟶ Y} {p' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' p' p g)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleBaseChange ℓ sq).app K).hom =
      (residueExchangeBaseChange (Profinite.padicAlgClRingObj ℓ)
        (⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩ : CommSq g'.left p'.left p.left g.left)).app K.obj := by
  let s : CommSq g'.left p'.left p.left g.left := ⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  have : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  have : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y.hom›
  have : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
  have : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
  have : LocallyOfFiniteType (X'.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X'.hom›
  have : QuasiCompact (X'.left ↘ Spec (.of k)) := ‹QuasiCompact X'.hom›
  have : IsSeparated (X'.left ↘ Spec (.of k)) := ‹IsSeparated X'.hom›
  have : LocallyOfFiniteType (Y'.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y'.hom›
  have : QuasiCompact (Y'.left ↘ Spec (.of k)) := ‹QuasiCompact Y'.hom›
  have : IsSeparated (Y'.left ↘ Spec (.of k)) := ‹IsSeparated Y'.hom›
  exact boundedConstructibleBaseChange_hom_eq_ambient ℓ k s K

section
variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (f' : X' ⟶ Y') {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}

private theorem forget_field_map [IsProper f.left] (sq : IsPullback πX f'.left f.left πY)
    [WeaklyEtale πX] [WeaklyEtale πY]
    (P : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj l⟧) :
    ((boundedConstructibleBaseChangeOfMap l sq.toCommSq).app P).hom =
      (baseChangeMap (Profinite.padicAlgClRingObj l) sq.toCommSq).app P.obj := by
  have := isIso_boundedConstructibleBaseChangeOfMap l sq
  have := isIso_baseChangeMap_of_weaklyEtale (Profinite.padicAlgClRingObj l) sq
  let β := (asIso (boundedConstructibleBaseChangeOfMap l sq.toCommSq)).app P
  let γ := (asIso (baseChangeMap (Profinite.padicAlgClRingObj l) sq.toCommSq)).app P.obj
  apply Functor.map_iso_inv_eq_of_map_hom_eq (boundedConstructible _).ι β.symm γ.symm
  exact boundedConstructibleBaseChangeOfMap_inv_app_hom l f f' sq P

end

/-- Forgetting the field structure preserves ordinary base change on bounded constructible
complexes. Both exchanges restrict the right mate of the same ambient pullback square. -/
theorem boundedSliceDirectImageExchange_eq_ofMap
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)] {X Y X' Y' : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    {p : X ⟶ Y} {p' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsProper p.left] [WeaklyEtale g.left] [WeaklyEtale g'.left]
    (sq : IsPullback g' p' p g) :
    boundedConstructibleBaseChange ℓ sq.toCommSq =
      boundedConstructibleBaseChangeOfMap ℓ (f := p) (f' := p') sq.overLeft.toCommSq := by
  apply NatTrans.ext
  funext K
  have hs := boundedSliceResidue ℓ sq.toCommSq K
  have ht := congr_app (residueExchange_eq_baseChangeMap
    (Profinite.padicAlgClRingObj ℓ) sq.overLeft.toCommSq) K.obj
  have hf := forget_field_map ℓ p p' sq.overLeft K
  apply ObjectProperty.hom_ext
  exact hs.trans (ht.trans hf.symm)

end WeilII
