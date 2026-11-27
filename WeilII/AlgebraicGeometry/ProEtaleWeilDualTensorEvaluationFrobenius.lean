module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorDualToIhomMap
public import WeilConjectures.WeilSheaf.TensorHomAdjunction
import WeilConjectures.WeilSheaf.DerivedHom

/-! # Frobenius equivariance of tensor-dual evaluation

The module comparison in `Monoidal/Mod/TensorDualToIhomMap.lean` applies to the Frobenius
structures on tensor and internal Hom defined in `WeilSheaf/Dual.lean`.
-/

public section

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory

namespace WeilII

universe u

attribute [local instance] Sheaf.symmetricCategory
attribute [local instance 25000] SymmetricCategory.toBraidedCategory

/-- Commutativity of the adic coefficient ring for the chosen sheaf braiding, from
`Adic/Hom.lean`. -/
local instance frobeniusEvaluationCoefficientsComm {ℓ : ℕ} [Fact ℓ.Prime] (T : Scheme.{u}) :
    IsCommMonObj (adicConstantSheaf ℓ T) :=
  adicConstantSheaf.isCommMonObj T

/-- The geometric evaluation `e : B ⊗ A∨ ⟶ [A,B]` intertwines the tensor and internal Hom
Weil structures for a lisse constructible coefficient `A` and any pro-étale Weil sheaf `B`.

Write `F` for direct image along inverse geometric Frobenius, `R` for the coefficient unit,
and `D = [A,R]`. The comparison `ψ_N : F[A,N] ≅ [FA,FN]` preserves evaluation. At `N = R`,
postcompose with internal Hom applied to the unit structure `σ_R : FR ≅ R` to obtain
`δ : FD ≅ [FA,R]`. Naturality of evaluation makes this dual pairing compatible with the
underlying map of `σ_R`, which is inverse to the ring map defining `F`. The transport
formula for balanced tensor evaluation therefore identifies `F(e)`, after the tensor
comparison and `ψ_B`, with tensoring by `δ` followed by evaluation at `FA, FB`.

The structure of `[A,B]` follows `ψ_B` by precomposition with `σ_A.inv` and postcomposition
with `σ_B.hom`. By naturality of geometric evaluation in both variables, these two actions
on the target act on the tensor source by the dual of `σ_A.inv` and by `σ_B.hom`,
respectively. The composite of `δ` with that dual is the structure of `D`, since
precomposition commutes with postcomposition by `σ_R.hom`. The resulting tensor composite
is precisely the structure of `B ⊗ D` followed by `e`.

Sources are `Mod.tensorLeftCompMapModComapIso_inv_app_map_tensorDualToIhom`,
`Mod.μ_comp_map_evaluation`, the two naturality formulas in `Mod/TensorDualToIhom.lean`,
and the Weil structures in `WeilSheaf/Dual.lean`. -/
theorem proEtaleWeilDualTensorEvaluation_frobenius
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (A : WeilSheaf k ℓ X) (hA : A.IsLisse) (B : ProEtaleWeilSheaf k ℓ X) :
    let P := ProEtaleWeilSheaf.tensor k ℓ X (A.dual hA).obj B
    let Q := ProEtaleWeilSheaf.ihom k ℓ X A.obj B
    let e : P.carrier ⟶ Q.carrier := Mod.tensorDualToIhom A.obj.carrier B.carrier
    (WeilSheaf.frobeniusPullback k ℓ X).map e ≫ Q.str.hom = P.str.hom ≫ e :=
  open MonoidalCategory in
  set_option backward.isDefEq.respectTransparency.types false in by
  let g := (X ↘ Spec (CommRingCat.of k)).geometricGaloisFrobenius.asIso.inv
  let _ : (g)_*[WeilCoefficients.{u} ℓ].LaxBraided := laxBraided_lowerStar _ g
  let F := WeilSheaf.frobeniusPullback k ℓ X
  let M := A.obj.carrier
  let N := B.carrier
  let R := ProEtaleWeilSheaf.adicConstant k ℓ X
  let D := (A.dual hA).obj
  let ψ := (adicLowerStarCompIhomIso ℓ g M).inv
  let δ := ψ.app R.carrier ≫ (Mod.ihom (F.obj M)).map R.str.hom
  let c := (adicLowerStarTensorLeftIso ℓ g D.carrier).app N
  let v := Mod.ihomMap A.obj.str.inv
  have : (Mod.mapModComap (G := (g)_*[WeilCoefficients.{u} ℓ])
      (adicConstantSheafToLowerStar ℓ g)).IsEquivalence := isEquivalence_adicLowerStar ℓ g
  -- Transport evaluation along Frobenius before using the Weil structures of A and B.
  have square : c.inv ≫ F.map (Mod.tensorDualToIhom M N) ≫ ψ.app N =
      (Mod.tensorLeftMap δ).app _ ≫ Mod.tensorDualToIhom (F.obj M) (F.obj N) := by
    apply Mod.tensorLeftCompMapModComapIso_inv_app_map_tensorDualToIhom
      (adicConstantSheafToLowerStar ℓ g) (fun _ _ ↦ Functor.LaxBraided.braided _ _)
      M N (ψ.app N) (Mod.μ_comp_map_evaluation (adicConstantSheafToLowerStar ℓ g)
        (fun _ _ ↦ Functor.LaxBraided.braided _ _) M N).symm δ R.str.hom.hom
    · exact (adicConstantSheafLowerStarIso ℓ
        (X ↘ Spec (CommRingCat.of k)).geometricGaloisFrobenius.asIso.symm).hom_inv_id
    · dsimp only [δ]
      erw [Mod.comp_hom', comp_whiskerRight_assoc, Mod.evaluation_naturality (F.obj M) R.str.hom]
      exact (reassoc_of% (Mod.μ_comp_map_evaluation (adicConstantSheafToLowerStar ℓ g)
        (fun _ _ ↦ Functor.LaxBraided.braided _ _) M R.carrier).symm) _
  have dualStr : D.str.hom = δ ≫ v.app R.carrier := by
    change ψ.app R.carrier ≫ v.app _ ≫ (Mod.ihom M).map R.str.hom = _
    erw [← v.naturality R.str.hom]
    exact (Category.assoc _ _ _).symm
  have tensorDualStr : (Mod.tensorLeftMap D.str.hom).app (F.obj N) =
      (Mod.tensorLeftMap δ).app _ ≫ (Mod.tensorLeftMap (v.app R.carrier)).app _ := by
    rw [dualStr]
    exact NatTrans.congr_app (Mod.tensorLeftMap_comp δ (v.app R.carrier)) _
  change F.map (Mod.tensorDualToIhom M N) ≫ ψ.app N ≫ v.app _ ≫ (Mod.ihom M).map B.str.hom =
    (c.hom ≫ (Mod.tensorLeftMap D.str.hom).app _ ≫ (Mod.tensorLeft D.carrier).map B.str.hom) ≫ _
  erw [reassoc_of% (c.inv_comp_eq.mp square)]
  erw [tensorDualStr]
  simp only [Category.assoc]
  erw [Mod.tensorDualToIhom_naturality M B.str.hom]
  apply congrArg (c.hom ≫ ·)
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  apply congrArg ((Mod.tensorLeftMap δ).app (F.obj N) ≫ ·)
  exact (Mod.tensorLeftMap_app_comp_tensorDualToIhom_assoc (F.obj N) A.obj.str.inv
    ((Mod.ihom M).map B.str.hom)).symm

end WeilII
