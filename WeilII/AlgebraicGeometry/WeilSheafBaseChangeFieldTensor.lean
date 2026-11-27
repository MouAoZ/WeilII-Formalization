module

public import WeilConjectures.WeilSheaf.BaseChangeField.Restriction
public import WeilConjectures.WeilSheaf.Tensor
import WeilConjectures.WeilSheaf.BaseChangeField.Comparison
import WeilConjectures.WeilSheaf.DerivedHom
import WeilConjectures.WeilSheaf.StalkInternalHom
import WeilII.AlgebraicGeometry.WeilSheafBaseChangeFieldInternalHom

/-!
# Tensor products of lisse Weil sheaves after a finite extension of constants

Zhang, *On an elementary proof of Weil II*, p. 2 and Construction 2.5, uses the same external
tensor power after extending the finite field. This is the comparison for its binary tensor step.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The binary tensor product of lisse Weil sheaves commutes with the finite extension of
constants used in Zhang, *On an elementary proof of Weil II*, pp. 2–4.

Write R for extension of constants, C and C' for the constant coefficient lines, and d for
the extension degree. Since the cardinality of K is the d-th power of that of k, the
geometric fiber isomorphism intertwines the new Frobenius with the d-th power of the old one.
Thus R uses the transport to which `adicConstantTransportIso` applies. Its inverse gives
R(C) ≅ C' in the constructible full subcategory.

The dual of A is the internal Hom [A,C]. Apply the internal-Hom comparison for extension of
constants with lisse source A, then postcompose with R(C) ≅ C'. This gives a Weil isomorphism
δ from R(A∨) to (RA)∨. The dual A∨ is lisse, so the same internal-Hom comparison applied to
A∨ and B identifies R([A∨,B]) with [R(A∨),RB]. Precomposition with the inverse of δ identifies
the latter with [(RA)∨,RB]. Both changes of variable are induced by the Weil internal-Hom
bifunctor and lift to the constructible full subcategory. By the definition of `tensorObj`,
the composite has the stated source and target. -/
public theorem weilSheaf_baseChangeField_tensorObj
    {k : Type u} [Field k] [Finite k] (K : Type u) [Field K] [Finite K] [Algebra k K]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    (A B : WeilSheaf k ℓ X) (hA : A.IsLisse) (_hB : B.IsLisse) :
    letI : Fact (ringChar K ≠ ℓ) := ⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩
    Nonempty ((WeilSheaf.baseChangeField K).obj (A.tensorObj B hA) ≅
      ((WeilSheaf.baseChangeField K).obj A).tensorObj ((WeilSheaf.baseChangeField K).obj B)
        (hA.baseChangeField K)) := by
  let : Fact (ringChar K ≠ ℓ) := ⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩
  let R := WeilSheaf.baseChangeField (k₀ := k) (l := ℓ) (X := X) K
  let X' := X.baseChangeField k K
  let C := WeilSheaf.adicConstant k ℓ X
  let sq := WeilSheaf.isPullback_baseChangeField (k₀ := k) X K
  let θ := Scheme.Hom.geometricFiberBaseChangeIso sq
  have hθ := Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius
    sq (Module.finrank k K) Module.natCard_eq_pow_finrank
  let unit : (R.obj C).obj ≅ ProEtaleWeilSheaf.adicConstant K ℓ X' :=
    (ProEtaleWeilSheaf.adicConstantTransportIso (l := ℓ) θ _ hθ).symm
  obtain ⟨compareDual⟩ := weilSheaf_baseChangeField_ihom K A hA C
  let incl := (WeilSheaf.objectProperty K ℓ X').ι
  let hom := ProEtaleWeilSheaf.ihomBifunctor K ℓ X'
  let dual : (R.obj (A.dual hA)).obj ≅ ((R.obj A).dual (hA.baseChangeField K)).obj :=
    incl.mapIso compareDual ≪≫ (hom.obj (Opposite.op (R.obj A).obj)).mapIso unit
  obtain ⟨compareTensor⟩ := weilSheaf_baseChangeField_ihom K (A.dual hA) hA.dual B
  let precompose := (hom.mapIso dual.symm.op).app (R.obj B).obj
  exact ⟨compareTensor ≪≫ ObjectProperty.isoMk _ precompose⟩

end WeilII
