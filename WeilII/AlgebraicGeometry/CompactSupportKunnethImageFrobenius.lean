module

public import WeilII.AlgebraicGeometry.CompactSupportExteriorClassProduct
public import WeilII.AlgebraicGeometry.GeometricCompactSupportKunnethFrobenius

import WeilII.AlgebraicGeometry.CompactSupportImageFrobeniusInclusion
import WeilII.AlgebraicGeometry.KunnethSchemeAutomorphisms
import WeilII.AlgebraicGeometry.CompactSupportKunnethNaturality
import WeilII.CategoryTheory.NormalizedKunnethImage
meta import WeilII.Tactic.StructuralDefEq
meta import WeilII.Tactic.SchemeComponentCongruence
meta import WeilConjectures.Tactic.ExactByKernel

/-! # The Weil structure on the compact-support Künneth comparison -/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII

open CompactSupportClasses

attribute [local instance] instOverLeftSchemeSpecOf_weilII instIsOverLeftSchemeSpecOf_weilII
  instIsSeparatedOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII
  instQuasiCompactOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII
  instLocallyOfFiniteTypeOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII

set_option backward.isDefEq.respectTransparency.types false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

universe u
variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
local notation "Ω" => AlgebraicClosure k
local notation "Λ" => Profinite.padicAlgClRingObj ℓ
private instance : Fact (ringChar Ω).Prime := ⟨Algebra.ringChar_eq k Ω ▸ CharP.prime_ringChar k⟩
private instance : Fact (ringChar Ω ≠ ℓ) := ⟨Algebra.ringChar_eq k Ω ▸ (Fact.out : ringChar k ≠ ℓ)⟩

/-- The normalized comparison from the tensor of two compact-support images to the
image on their product commutes with the Weil structures (SGA 4, XVII, 5.4.3.2 for
the underlying compact-support base-change square).

Proof. Apply the bounded inclusion to the comparison on compact-support images.
Specialize the Künneth square for scheme automorphisms to the given product square
and the geometric Galois automorphisms. Each terminal map has its cartesian square
by uniqueness of maps to the point. For the
composite structure map h, naturality of shriek base change moves the pullback of
h_!(e) past the base-change component. Functoriality of h_! then identifies the next
composite with the image of the pullback of e followed by the product Weil structure.
The normalized coefficient square expresses it as the oplax tensor comparison,
the two projection comparisons, the tensor of the two carrier structures, and e.
The Frobenius square for inverse Künneth absorbs the first two comparisons. Its
coefficient naturality moves the two carrier structures across the remaining inverse
Künneth map. Compose the two tensor maps using bifunctoriality. Their components are
exactly the base changes followed by the shriek images of the two carrier structures,
hence the image Weil structures. Finally, transport from h to the canonical structure
map of P commutes with the image structure by induction on their equality. -/
public theorem compactSupportKunnethImage_frobenius
    {X Y P : Over (Spec (.of k))}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated P.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    (p : P ⟶ X) (s : P ⟶ Y) (product : IsPullback s.left p.left Y.hom X.hom)
    (L : WeilSheaf k ℓ X.left) (M : WeilSheaf k ℓ Y.left) (hL : L.IsLisse) :
    letI := (monoidalCategory_boundedConstructible (ℓ := ℓ) (geometricFiberOver P)).toMonoidalCategoryStruct
    letI := (monoidalCategory_boundedConstructible (ℓ := ℓ) (point Ω)).toMonoidalCategoryStruct
    let p' := geometricFiberOverMap p
    let s' := geometricFiberOverMap s
    let f := toPoint (geometricFiberOver X)
    let g := toPoint (geometricFiberOver Y)
    let h := p' ≫ f
    let K := carrier.obj L
    let J := carrier.obj M
    let N := ((WeilSheaf.upperStar p.left).obj L).tensorObj ((WeilSheaf.upperStar s.left).obj M)
      (hL.upperStar p.left)
    let img := fun t : geometricFiberOver P ⟶ point Ω ↦ (boundedConstructibleLowerShriek ℓ t).obj (carrier.obj N)
    let σ := (specGeometricFrobenius k).asIso.hom
    let F := pull (ℓ := ℓ) σ
    letI : F.Monoidal := monoidal_leftDerivedUpperStar Λ σ
    ∀ (sq : IsPullback s' p' g f) (e), ExternalProduct.EvaluationNormalized p s L M hL e →
      let γ := (compactSupportKunnethIso ℓ sq K J).inv ≫ (boundedConstructibleLowerShriek ℓ h).map e.hom ≫
        eqToHom (congrArg img (comp_toPoint p'))
      F.map γ.hom ≫ (imageFrobenius N).hom = Functor.OplaxMonoidal.δ F _ _ ≫
        ((imageFrobenius L).hom ⊗ₘ (imageFrobenius M).hom) ≫ γ.hom := by
  let := (monoidalCategory_boundedConstructible (ℓ := ℓ) (geometricFiberOver P)).toMonoidalCategoryStruct
  let := (monoidalCategory_boundedConstructible (ℓ := ℓ) (point Ω)).toMonoidalCategoryStruct
  intro p' s' f g h K J N img σ F sq e he γ
  let G := boundedConstructibleUpperStarOfMap ℓ (X := point Ω) (Y := point Ω) σ
  let GP := boundedConstructibleUpperStarOfMap ℓ (X := geometricFiberOver P)
    (Y := geometricFiberOver P) P.hom.geometricGaloisFrobenius.asIso.hom
  let H := boundedConstructibleLowerShriek ℓ h
  have hf := isPullback_frobenius_terminalMap (Z := X) f
  have hg := isPullback_frobenius_terminalMap (Z := Y) g
  have sqh := isPullback_frobenius_terminalMap (Z := P) h
  let Ef := purityFieldLowerShriekBaseChange ℓ f f hf
  let Eg := purityFieldLowerShriekBaseChange ℓ g g hg
  let Eh := purityFieldLowerShriekBaseChange ℓ h h sqh
  let ps := boundedConstructibleUpperStar Λ ℓ p'
  let ss := boundedConstructibleUpperStar Λ ℓ s'
  let Dp := boundedConstructibleUpperStarOfMapSquareIso ℓ p' p'
    (Scheme.Hom.commSq_geometricGaloisFrobenius p.left (Over.w p)).w
  let Ds := boundedConstructibleUpperStarOfMapSquareIso ℓ s' s'
    (Scheme.Hom.commSq_geometricGaloisFrobenius s.left (Over.w s)).w
  let kmap := (compactSupportKunnethIso ℓ sq K J).inv
  let c := eqToHom (congrArg img (comp_toPoint p'))
  let iL := (carrierFrobenius L).hom
  let iM := (carrierFrobenius M).hom
  let iN := (carrierFrobenius N).hom
  let α := Functor.OplaxMonoidal.δ GP (ps.obj K) (ss.obj J) ≫ (Dp.hom.app K ⊗ₘ Ds.hom.app J)
  let β := ps.map iL ⊗ₘ ss.map iM
  -- Use the same evaluation witness in the normalized coefficient square.
  let raw := ExternalProduct.normalizedSingleTensor_frobenius p s L M hL
  let rawAt := raw e
  let premise {A B : Prop} (_ : A → B) := A
  let normalized : premise rawAt := by
    obtain ⟨j, hj, hj'⟩ := he
    exact ⟨j, by structural_exact hj, by structural_exact hj'⟩
  let rawOut := rawAt normalized
  let coefficient : GP.map e.hom ≫ iN =
      Functor.OplaxMonoidal.δ GP (ps.obj K) (ss.obj J) ≫
        (Dp.hom.app K ⊗ₘ Ds.hom.app J) ≫ β ≫ e.hom := by
    scheme_component_exact rawOut using he
  let eq₁ : GP.map e.hom ≫ iN = α ≫ β ≫ e.hom :=
    coefficient.trans (Category.assoc _ _ (β ≫ e.hom)).symm
  let K' := (boundedConstructibleUpperStarOfMap ℓ (X := geometricFiberOver X) (Y := geometricFiberOver X)
    X.hom.geometricGaloisFrobenius.asIso.hom).obj K
  let J' := (boundedConstructibleUpperStarOfMap ℓ (X := geometricFiberOver Y) (Y := geometricFiberOver Y)
    Y.hom.geometricGaloisFrobenius.asIso.hom).obj J
  let kmap' := (compactSupportKunnethIso ℓ sq K' J').inv
  let fH := boundedConstructibleLowerShriek ℓ f
  let gH := boundedConstructibleLowerShriek ℓ g
  let u := Ef.hom.app K
  let v := Eg.hom.app J
  let x := fH.map iL
  let y := gH.map iM
  -- The geometric square is already stated for the terminal maps f, g and h.
  let geom : G.map kmap ≫ Eh.hom.app _ ≫ H.map α =
      (Functor.OplaxMonoidal.δ G (fH.obj K) (gH.obj J) ≫ (u ⊗ₘ v)) ≫ kmap' := by
    have square := compactSupportKunneth_underSchemeAutomorphisms ℓ sq
      P.hom.geometricGaloisFrobenius.asIso X.hom.geometricGaloisFrobenius.asIso
      Y.hom.geometricGaloisFrobenius.asIso (specGeometricFrobenius k).asIso
      (Scheme.Hom.commSq_geometricGaloisFrobenius p.left (Over.w p))
      (Scheme.Hom.commSq_geometricGaloisFrobenius s.left (Over.w s))
      hf hg sqh K J
    scheme_component_exact square.1 using hf
  let nat : kmap' ≫ H.map β = (x ⊗ₘ y) ≫ kmap :=
    compactSupportKunneth_inv_naturality ℓ sq iL iM
  let a := toPoint (geometricFiberOver P)
  -- Expand the image structure at h after transporting along the terminal-map equality.
  let z := (imageFrobeniusAt (Z := P) N a).hom
  let zh := (imageFrobeniusAt (Z := P) N h).hom
  let ht₀ : G.map c ≫ z = zh ≫ c := by
    have tr := imageFrobeniusAt_transport (Z := P) N h a (comp_toPoint p')
    dsimp only at tr
    scheme_component_exact tr using hf
  let atH : imageFrobeniusAt (Z := P) N h = Eh.app (carrier.obj N) ≪≫ H.mapIso (carrierFrobenius N) := rfl
  let expand : zh = Eh.hom.app (carrier.obj N) ≫ H.map iN := by
    have proj := congrArg Iso.hom atH
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at proj
    scheme_component_exact proj using hf
  let ht := ht₀.trans (congrArg (· ≫ c) expand)
  let full := normalizedKunnethImage_of_squares G GP H Eh.hom kmap kmap' e.hom c iN
    (imageFrobeniusAt (Z := P) N a).hom α β u v x y
    (by scheme_component_exact ht using hf)
    (by scheme_component_exact eq₁ using hf)
    (by scheme_component_exact geom using hf)
    (by scheme_component_exact nat using hf)
  let ambient := compactSupportImageFrobenius_of_boundedSquare (X := X) (Y := Y) (P := P) L M N γ
    (by scheme_component_exact full using hf)
  exact_by_kernel ambient

end WeilII
