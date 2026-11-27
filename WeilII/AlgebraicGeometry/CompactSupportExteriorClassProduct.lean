module

public import WeilII.AlgebraicGeometry.GeometricPointGradedTensorKunneth
public import WeilII.AlgebraicGeometry.WeilLisseExternalProductCondensed
public import WeilConjectures.PoincareDuality.CompactSupportKunneth
public import WeilConjectures.WeilSheaf.StalkTensorTrace

/-! # The exterior product of compactly supported Weil cohomology classes

SGA 4, XVII, (5.4.2.2) and (5.4.3.4), constructs the compact-support exterior product.
Here the condensed Künneth isomorphism gives the comparison for the coefficients used
in Zhang's deduction of Theorem 1.1 from Proposition 1.5 on p. 2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII

open CompactSupportClasses

universe u

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]

local notation "Ω" => AlgebraicClosure k
local notation "Λ" => Profinite.padicAlgClRingObj ℓ

attribute [local instance] instOverLeftSchemeSpecOf_weilII instIsOverLeftSchemeSpecOf_weilII
  instIsSeparatedOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII
  instQuasiCompactOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII
  instLocallyOfFiniteTypeOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII

variable {X Y P : Over (Spec (.of k))}
  [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated P.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]

/-- Evaluation normalization of the coefficient isomorphism, as in
`weilLisseExternalProductCondensedComparison`. On the native relative tensor product the
map sends a pure tensor of sections to evaluation against a dual section. -/
def ExternalProduct.EvaluationNormalized (p : P ⟶ X) (s : P ⟶ Y)
    (L : WeilSheaf k ℓ X.left) (M : WeilSheaf k ℓ Y.left) (hL : L.IsLisse) :=
  letI : Fact (ringChar Ω).Prime := ⟨Algebra.ringChar_eq k Ω ▸ CharP.prime_ringChar k⟩
  letI : Fact (ringChar Ω ≠ ℓ) := ⟨Algebra.ringChar_eq k Ω ▸ (Fact.out : ringChar k ≠ ℓ)⟩
  letI := (monoidalCategory_boundedConstructible (ℓ := ℓ)
    (geometricFiberOver P)).toMonoidalCategoryStruct
  let p' := geometricFiberOverMap p
  let s' := geometricFiberOverMap s
  let pStar := boundedConstructibleUpperStar Λ ℓ p'
  let sStar := boundedConstructibleUpperStar Λ ℓ s'
  let K := carrier.obj L
  let J := carrier.obj M
  let F := (WeilSheaf.upperStar p.left).obj L
  let G := (WeilSheaf.upperStar s.left).obj M
  let N := F.tensorObj G (hL.upperStar p.left)
  let A := F.obj.carrier
  let B := G.obj.carrier
  let E := (adicSheafEquivCondensedMod ℓ P.hom.geometricFiber).functor
  let S := DerivedCategory.singleFunctor (Coeff ℓ P.hom.geometricFiber) 0
  let flatTensor :=
    (IsAdicLisseSheaf.isLocallyFree (hL.upperStar p.left)).singleFunctorTensorObjIso (E.obj B) 0
  let sourceSingle := tensorIso (ExternalProduct.pullCarrierSingle p.left L)
      (ExternalProduct.pullCarrierSingle s.left M) ≪≫
    flatTensor ≪≫ S.mapIso (condensedRelativeTensorIso ℓ _ A B).symm
  fun e : pStar.obj K ⊗ sStar.obj J ≅ carrier.obj N ↦
    ∃ j : (Mod.tensorLeft B).obj A ⟶ N.obj.carrier,
      Mod.tensorπ A B ≫ j.hom = Mod.toIhomDual A B ∧
      e.hom.hom ≫ (ExternalProduct.carrierSingle N).hom = sourceSingle.hom ≫ S.map (E.map j)

-- Keep the local definitions in the coefficient comparison when extracting its witness.
set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The bilinear exterior product in arbitrary integer bidegree, as in SGA 4, XVII,
(5.4.2.2), (5.4.3.4). Read the two native classes as shifted-unit maps. In bidegree
`(a,b)`, the point Künneth comparison tensors these maps after splitting the shifted
unit by `1 ↦ 1 ⊗ 1`. Postcompose with the inverse compact-support Künneth isomorphism
and the shriek image of the evaluation-normalized coefficient comparison. The inverse
shifted-unit comparison reads the result as a native class on the product. -/
def compactSupportExteriorClassProduct (p : P ⟶ X) (s : P ⟶ Y)
    (product : IsPullback s.left p.left Y.hom X.hom)
    (L : WeilSheaf k ℓ X.left) (M : WeilSheaf k ℓ Y.left) (hL : L.IsLisse) (hM : M.IsLisse)
    (a b : ℤ) :
    let N := ((WeilSheaf.upperStar p.left).obj L).tensorObj ((WeilSheaf.upperStar s.left).obj M)
      (hL.upperStar p.left)
    (L.compactlySupportedCohomology a).carrier →ₗ[PadicAlgCl ℓ]
      (M.compactlySupportedCohomology b).carrier →ₗ[PadicAlgCl ℓ]
        (N.compactlySupportedCohomology (a + b)).carrier := by
  classical
  letI : Fact (ringChar Ω).Prime := ⟨Algebra.ringChar_eq k Ω ▸ CharP.prime_ringChar k⟩
  letI : Fact (ringChar Ω ≠ ℓ) := ⟨Algebra.ringChar_eq k Ω ▸ (Fact.out : ringChar k ≠ ℓ)⟩
  let p' := geometricFiberOverMap p
  let f := toPoint (geometricFiberOver X)
  let g := toPoint (geometricFiberOver Y)
  letI := (monoidalCategory_boundedConstructible (ℓ := ℓ)
    (geometricFiberOver P)).toMonoidalCategoryStruct
  letI := (monoidalCategory_boundedConstructible (ℓ := ℓ) (point Ω)).toMonoidalCategoryStruct
  let K := carrier.obj L
  let J := carrier.obj M
  let N := ((WeilSheaf.upperStar p.left).obj L).tensorObj ((WeilSheaf.upperStar s.left).obj M)
    (hL.upperStar p.left)
  let A := (boundedConstructibleLowerShriek ℓ f).obj K
  let B := (boundedConstructibleLowerShriek ℓ g).obj J
  -- The uniqueness clause in the comparison identifies any such witness with the Weil one.
  have comparison : ∃ e, ExternalProduct.EvaluationNormalized p s L M hL e := by
    have witness := weilLisseExternalProductCondensedComparison p s L M hL hM
    extract_lets -descend at witness
    obtain ⟨e, he, _⟩ := witness
    exact ⟨e, he⟩
  let e := comparison.choose
  have sq : IsPullback (geometricFiberOverMap s) p' g f := by
    apply IsPullback.of_map_of_faithful (Over.forget _)
    simp only [Over.forget_map, f, g, toPoint_left]
    change IsPullback (Scheme.Hom.geometricFiberMap s.left (Over.w s))
      (Scheme.Hom.geometricFiberMap p.left (Over.w p))
      Y.hom.geometricFiberToAlgebraicClosure X.hom.geometricFiberToAlgebraicClosure
    have right : IsPullback Y.hom.geometricFiberProj Y.hom.geometricFiberToAlgebraicClosure
        Y.hom (Scheme.specAlgebraicClosure k).hom := IsPullback.of_hasPullback _ _
    apply IsPullback.of_right _ _ right
    · erw [Scheme.Hom.geometricFiberMap_comp_geometricFiberProj, ← X.hom.geometricFiber_condition]
      exact (isPullback_geometricFiberOverMap p).paste_horiz product
    · exact (Over.w (geometricFiberOverMap s)).trans (Over.w (geometricFiberOverMap p)).symm
  let κ := (compactSupportKunnethIso ℓ sq K J).inv
  let h' := p' ≫ f
  let geometricTarget := fun t : geometricFiberOver P ⟶ point Ω ↦
    (boundedConstructibleLowerShriek ℓ t).obj ((carrier (X := P.left)).obj N)
  let toCanonical := eqToHom (congrArg geometricTarget (comp_toPoint p'))
  let γ := κ ≫ (boundedConstructibleLowerShriek ℓ h').map e.hom ≫ toCanonical
  let post : (gradedHom ℓ Ω (-(a + b))).obj (A.obj ⊗ B.obj) →ₗ[PadicAlgCl ℓ]
      (gradedHom ℓ Ω (-(a + b))).obj (shriekImage.obj N) :=
    ((gradedHom ℓ Ω (-(a + b))).map γ.hom).hom
  let ρL := (exists_natural_equiv (X := X.left) a).choose L hL
  let ρM := (exists_natural_equiv (X := Y.left) b).choose M hM
  let ρN := (exists_natural_equiv (X := P.left) (a + b)).choose N
    ((hL.upperStar p.left).tensorObj (hM.upperStar s.left))
  let grade := (geometricPointGradedTensorKunneth ℓ Ω A B (a + b)).choose
  let i : {q : ℤ × ℤ // q.1 + q.2 = a + b} := ⟨(a, b), rfl⟩
  let component := grade.toLinearMap.comp (DirectSum.lof (PadicAlgCl ℓ) _ _ i)
  exact ((TensorProduct.curry component).compl₁₂ ρL.toLinearMap ρM.toLinearMap).compr₂
    (ρN.symm.toLinearMap.comp post)

end WeilII
