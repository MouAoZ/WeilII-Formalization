module

public import WeilII.AlgebraicGeometry.WeilSheafBaseChangeFieldTensor
import WeilConjectures.WeilSheaf.ArtinSchreierNormalization
import WeilConjectures.WeilSheaf.StalkTensorTrace

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The binary tensor step of Zhang's Proposition 1.5 after changing constants
and pulling back to a scheme over the new field. Pull back the binary comparison
for extension of constants, distribute pullback over the lisse tensor, and
tensor the given comparisons on its two factors. -/
public theorem weilSheaf_baseChangeField_tensorObj_pullback
    {k : Type u} [Field k] [Finite k] (K : Type u) [Field K] [Finite K] [Algebra k K]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] [hK : Fact (ringChar K ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of K))]
    (x : Z ⟶ X.baseChangeField k K) [x.IsOver (Spec (CommRingCat.of K))]
    (A T : WeilSheaf k ℓ X) (hA : A.IsLisse) (hT : T.IsLisse) :
    ∀ (C U : WeilSheaf K ℓ Z) (hC : C.IsLisse),
      Nonempty ((WeilSheaf.upperStar x).obj ((WeilSheaf.baseChangeField K).obj A) ≅ C) →
      Nonempty ((WeilSheaf.upperStar x).obj ((WeilSheaf.baseChangeField K).obj T) ≅ U) →
      Nonempty ((WeilSheaf.upperStar x).obj ((WeilSheaf.baseChangeField K).obj (A.tensorObj T hA)) ≅
        C.tensorObj U hC) := by
  have charProof : hK = (⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩ : Fact (ringChar K ≠ ℓ)) :=
    Subsingleton.elim _ _
  subst hK
  let : Fact (ringChar K ≠ ℓ) := ⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩
  have lift {B V W : WeilSheaf K ℓ (X.baseChangeField k K)} {hV : V.IsLisse}
      (c : Nonempty (B ≅ V.tensorObj W hV)) (C U : WeilSheaf K ℓ Z) (hC : C.IsLisse)
      (first : Nonempty ((WeilSheaf.upperStar x).obj V ≅ C))
      (second : Nonempty ((WeilSheaf.upperStar x).obj W ≅ U)) :
      Nonempty ((WeilSheaf.upperStar x).obj B ≅ C.tensorObj U hC) := by
    obtain ⟨c⟩ := c
    obtain ⟨a⟩ := first
    obtain ⟨t⟩ := second
    let dist := WeilSheaf.upperStarTensorObjIso x V W hV
    let pair := WeilSheaf.tensorObjIsoOfIso a t (hV.upperStar x) hC
    exact ⟨(WeilSheaf.upperStar x).mapIso c ≪≫ dist ≪≫ pair⟩
  exact lift (weilSheaf_baseChangeField_tensorObj K A T hA hT)

end WeilII
