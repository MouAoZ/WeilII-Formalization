module

public import WeilII.AlgebraicGeometry.CompactSupportExteriorClassProduct
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Tensor
import WeilII.AlgebraicGeometry.GeometricCompactSupportKunnethFrobenius
import WeilII.AlgebraicGeometry.CompactSupportExteriorClassProductFrobenius

/-!
# Binary Künneth decomposition for compactly supported Weil cohomology

Zhang uses the Frobenius-equivariant Künneth summand on p. 2 in the deduction of Theorem 1.1
from Proposition 1.5. The compact-support exterior product and its compatibility with base
change are constructed for torsion coefficients in SGA 4, XVII, 5.4.2–5.4.4. Here the
condensed Künneth isomorphism gives the corresponding decomposition over the ℓ-adic field.
-/

open AlgebraicGeometry CategoryTheory Limits
open scoped DirectSum TensorProduct

namespace WeilII

attribute [local instance] instOverLeftSchemeSpecOf_weilII instIsOverLeftSchemeSpecOf_weilII
  instIsSeparatedOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII
  instQuasiCompactOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII
  instLocallyOfFiniteTypeOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII

/-- In each total degree the exterior product identifies the direct sum of the ordered
bidegree summands with compactly supported cohomology of the product. Geometric Frobenius
acts on each summand by the tensor product of the two Frobenius automorphisms.

Proof (Zhang, p. 2, and SGA 4, XVII, Theorem 5.4.3 and Lemma 5.4.3.2). Base change the
product square to the algebraic closure. Pullback preserves lissity, so the external tensor
product of the two coefficients is lisse. Identify the native cohomology groups in each
degree with maps from the corresponding shifted unit to the geometric compact-support
direct images. Tensor the two identifications in each bidegree and take their direct sum.
The graded Künneth equivalence on the geometric point identifies this sum with shifted-unit
maps into the tensor of the two direct images. Postcompose with the inverse derived
compact-support Künneth isomorphism and the shriek image of the evaluation-normalized
coefficient comparison. Applying the inverse shifted-unit identification for the product
gives a linear equivalence. On a pure tensor these steps are precisely the defining
operations of the compact-support exterior product.

The base-change square for Künneth commutes with geometric Frobenius. By naturality in
the coefficients, their two Weil isomorphisms act on the product by its Weil isomorphism.
The monoidal pullback identifies the shifted-unit splitting with itself since it sends the
unit generator to the ordered tensor of the two unit generators. The shifted-unit Frobenius
formula therefore carries the exterior product of two classes to the exterior product of
their Frobenius images. Pure tensors span each summand and every direct-sum element has
finite support, giving the stated identity on the entire direct sum. -/
public theorem compactSupportBinaryKunnethDecomposition
    {k : Type*} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y P : Over (Spec (.of k))}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated P.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    (p : P ⟶ X) (s : P ⟶ Y) (product : IsPullback s.left p.left Y.hom X.hom)
    (L : WeilSheaf k ℓ X.left) (M : WeilSheaf k ℓ Y.left) (hL : L.IsLisse) (hM : M.IsLisse)
    (d : ℤ) :
    let N := ((WeilSheaf.upperStar p.left).obj L).tensorObj ((WeilSheaf.upperStar s.left).obj M)
      (hL.upperStar p.left)
    let T := fun i : {q : ℤ × ℤ // q.1 + q.2 = d} ↦
      (L.compactlySupportedCohomology i.1.1).tensor (M.compactlySupportedCohomology i.1.2)
    let W := N.compactlySupportedCohomology d
    ∃ e : (⨁ i, (T i).carrier) ≃ₗ[PadicAlgCl ℓ] W.carrier,
      (∀ (i : {q : ℤ × ℤ // q.1 + q.2 = d})
          (x : (L.compactlySupportedCohomology i.1.1).carrier)
          (y : (M.compactlySupportedCohomology i.1.2).carrier),
        e (DirectSum.lof (PadicAlgCl ℓ) _ _ i (x ⊗ₜ[PadicAlgCl ℓ] y)) =
          cast (congrArg (fun n ↦ (N.compactlySupportedCohomology n).carrier) i.2)
            (compactSupportExteriorClassProduct p s product L M hL hM i.1.1 i.1.2 x y)) ∧
      ∀ z, e (DirectSum.lmap (fun i ↦ (T i).frobeniusEnd) z) = W.frobenius (e z) :=
  open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing CompactSupportClasses in
  open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  intro N T W
  suffices linear : ∃ e : (⨁ i, (T i).carrier) ≃ₗ[PadicAlgCl ℓ] W.carrier,
      ∀ (i : {q : ℤ × ℤ // q.1 + q.2 = d}) x y,
        e (DirectSum.lof (PadicAlgCl ℓ) _ _ i (x ⊗ₜ[PadicAlgCl ℓ] y)) =
          cast (congrArg (fun n ↦ (N.compactlySupportedCohomology n).carrier) i.2)
            (compactSupportExteriorClassProduct p s product L M hL hM i.1.1 i.1.2 x y) by
    obtain ⟨e, he⟩ := linear
    refine ⟨e, he, ?_⟩
    have onComponents (t : ℤ) (i : {q : ℤ × ℤ // q.1 + q.2 = t}) x y :
        cast (congrArg (fun n ↦ (N.compactlySupportedCohomology n).carrier) i.2)
          (compactSupportExteriorClassProduct p s product L M hL hM i.1.1 i.1.2
            ((L.compactlySupportedCohomology i.1.1).frobenius x)
            ((M.compactlySupportedCohomology i.1.2).frobenius y)) =
        (N.compactlySupportedCohomology t).frobenius
          (cast (congrArg (fun n ↦ (N.compactlySupportedCohomology n).carrier) i.2)
            (compactSupportExteriorClassProduct p s product L M hL hM i.1.1 i.1.2 x y)) := by
      rcases i with ⟨⟨a, b⟩, rfl⟩
      dsimp only [Subtype.coe_mk, cast_eq, Prod.fst, Prod.snd]
      exact (compactSupportExteriorClassProduct_frobenius p s product L M hL hM a b x y).symm
    have eqMaps : e.toLinearMap ∘ₗ DirectSum.lmap (fun i ↦ (T i).frobeniusEnd) =
        W.frobeniusEnd ∘ₗ e.toLinearMap := by
      apply DirectSum.linearMap_ext
      intro i
      apply TensorProduct.ext'
      intro x y
      refine (congrArg e (DirectSum.lmap_lof (fun j ↦ (T j).frobeniusEnd) i
        (x ⊗ₜ[PadicAlgCl ℓ] y))).trans ?_
      exact (he i ((L.compactlySupportedCohomology i.1.1).frobenius x)
        ((M.compactlySupportedCohomology i.1.2).frobenius y)).trans
        ((onComponents d i x y).trans (congrArg W.frobenius (he i x y).symm))
    exact LinearMap.congr_fun eqMaps
  -- Use the coefficient isomorphism and geometric Künneth map chosen by the exterior product.
  delta compactSupportExteriorClassProduct
  extract_lets +usedOnly p' f g K J N' A B comparison coeff sq κ h img toCanonical γ
  let : IsIso κ := by dsimp only [κ]; infer_instance
  let : IsIso toCanonical := by dsimp only [toCanonical]; infer_instance
  let : IsIso γ := by dsimp only [γ]; infer_instance
  let γ' := (ObjectProperty.ι _).mapIso (asIso γ)
  let ρL (a : ℤ) := (exists_natural_equiv (X := X.left) a).choose L hL
  let ρM (b : ℤ) := (exists_natural_equiv (X := Y.left) b).choose M hM
  have hN : N.IsLisse := (hL.upperStar p.left).tensorObj (hM.upperStar s.left)
  let ρN := (exists_natural_equiv (X := P.left) d).choose N hN
  let : Fact (ringChar (AlgebraicClosure k)).Prime :=
    ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ CharP.prime_ringChar k⟩
  let : Fact (ringChar (AlgebraicClosure k) ≠ ℓ) :=
    ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ (Fact.out : ringChar k ≠ ℓ)⟩
  let grades := (geometricPointGradedTensorKunneth ℓ (AlgebraicClosure k) A B d).choose
  let post := ((gradedHom ℓ (AlgebraicClosure k) (-d)).mapIso γ').toLinearEquiv
  let components (i : {q : ℤ × ℤ // q.1 + q.2 = d}) :=
    TensorProduct.congr (ρL i.1.1) (ρM i.1.2)
  let e := DirectSum.congrLinearEquiv components ≪≫ₗ grades ≪≫ₗ post ≪≫ₗ ρN.symm
  refine ⟨e, ?_⟩
  rintro ⟨⟨a, b⟩, hab⟩ x y
  subst d
  exact congrArg (fun z ↦ ρN.symm (post (grades z)))
    (DirectSum.lmap_lof (fun j ↦ (components j).toLinearMap) ⟨(a, b), rfl⟩ (x ⊗ₜ[PadicAlgCl ℓ] y))

end WeilII
