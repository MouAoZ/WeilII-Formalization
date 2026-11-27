module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseWeilSheafTensor
public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCreatesLimits
import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorDualToIhom
import WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris
import WeilConjectures.WeilSheaf.Native.NativeForgetTotalTensor
import WeilII.AlgebraicGeometry.LisseAdicTensorDualToIhom
import WeilII.AlgebraicGeometry.ProEtaleWeilDualTensorEvaluationFrobenius

/-! # Tensoring with the dual of a lisse Weil sheaf

On pro-étale Weil sheaves, ordinary tensor with the dual computes internal Hom from a lisse
coefficient. The comparison uses geometric evaluation from `Monoidal/Mod/TensorDualToIhom.lean`
and the tensor action on coefficient morphisms from `WeilSheaf/Native/NativeForgetTotalTensor.lean`.
-/

open AlgebraicGeometry CategoryTheory ProEtaleWeilSheaf

namespace WeilII

universe u

/-- For each lisse constructible Weil sheaf `A`, evaluation identifies tensoring with `A∨`
with internal Hom from `A` on all pro-étale Weil sheaves. These isomorphisms are natural
under precomposition in the coefficient.

At a Weil sheaf `B`, take the geometric evaluation `b ⊗ λ ↦ (a ↦ λ(a)b)`. Its compatibility
with the Frobenius structures lifts it to a Weil morphism. Naturality of geometric evaluation
in `B` lifts through the faithful forgetful functor. On a pro-étale cover trivializing `A`,
the inverse to evaluation sends `f` to the sum of `f(eᵢ) ⊗ eᵢ∨` over a local basis.
The weakly étale pullback comparison identifies this evaluation with the pullback of the
original map up to isomorphism. The cover detects isomorphisms, as does the functor forgetting
the Weil structure. Thus the components form a natural isomorphism. For a coefficient
morphism `f : A ⟶ A'`, both composites in the square send `b ⊗ λ'` to
`a ↦ λ'(f(a))b` on the underlying sheaves, by the precomposition identity for geometric
evaluation and the underlying map formula for `nativeTensorMap`. Faithfulness gives the
equality of Weil natural transformations for this same family.

Sources are `Mod.tensorDualToIhomNatTrans`, `Mod.isIso_tensorDualToIhom_of_iso_biproduct`,
`Mod.tensorLeftMap_app_comp_tensorDualToIhom` and `ProEtaleWeilSheaf.nativeTensorMap_app_hom_f`. -/
public theorem exists_proEtaleWeilLisseDualTensorEvaluationIso
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] :
    ∃ c : ∀ (A : WeilSheaf k ℓ X) (hA : A.IsLisse),
        tensorFunctor k ℓ X (A.dual hA).obj ≅ (ihomBifunctor k ℓ X).obj (Opposite.op A.obj),
      ∀ (A A' : WeilSheaf k ℓ X) (f : A ⟶ A') (hA : A.IsLisse) (hA' : A'.IsLisse),
        (c A' hA').hom ≫ (ihomBifunctor k ℓ X).map f.hom.op =
          nativeTensorMap k ℓ X (WeilSheaf.dualMap f hA hA').hom ≫ (c A hA).hom :=
  open Endofunctor ProEtale in
  set_option backward.isDefEq.respectTransparency.types false in by
  let fiber := (X ↘ Spec (CommRingCat.of k)).geometricFiber
  let coeff := Sheaf (Scheme.ProEt.topology fiber) (WeilCoefficients.{u} ℓ)
  let : SymmetricCategory coeff := Sheaf.symmetricCategory _ _
  let : BraidedCategory coeff := SymmetricCategory.toBraidedCategory
  let : IsCommMonObj (adicConstantSheaf ℓ fiber) := adicConstantSheaf.isCommMonObj fiber
  let component (A : WeilSheaf k ℓ X) (hA : A.IsLisse) (B : ProEtaleWeilSheaf k ℓ X) :
      (tensorFunctor k ℓ X (A.dual hA).obj).obj B ≅
        ((ihomBifunctor k ℓ X).obj (Opposite.op A.obj)).obj B :=
    IsoAlgebra.isoMk
      (@asIso _ _ _ _ _ (isIso_lisseAdicTensorDualToIhom A.obj.carrier B.carrier hA))
      (proEtaleWeilDualTensorEvaluation_frobenius A hA B)
  refine ⟨fun A hA ↦ NatIso.ofComponents (component A hA) (fun f ↦
    IsoAlgebra.hom_ext ((Mod.tensorDualToIhomNatTrans A.obj.carrier).naturality f.hom.f)), ?_⟩
  intro A A' f hA hA'
  refine NatTrans.ext (funext fun B ↦ IsoAlgebra.hom_ext ?_)
  change Mod.tensorDualToIhom A'.obj.carrier B.carrier ≫ (Mod.ihomMap f.hom.hom.f).app _ =
    ((nativeTensorMap k ℓ X (WeilSheaf.dualMap f hA hA').hom).app B).hom.f ≫
      Mod.tensorDualToIhom A.obj.carrier B.carrier
  rw [nativeTensorMap_app_hom_f]
  exact (Mod.tensorLeftMap_app_comp_tensorDualToIhom B.carrier f.hom.hom.f).symm

end WeilII
