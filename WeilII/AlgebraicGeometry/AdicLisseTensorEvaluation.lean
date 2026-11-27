module

public import WeilII.AlgebraicGeometry.LisseAdicTensorDualToIhom
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.CategoryTheory.Monoidal.Mod.IhomDual

/-! # The native evaluation isomorphism for a lisse coefficient

The ordered tensor of adic sheaves maps to internal Hom out of the dual of its first
factor. Its normalization uses the pairing of `CategoryTheory/Monoidal/Mod/IhomDual.lean`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory MonoidalCategory Limits

namespace WeilII

universe v u

section Modules

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  {R : C} [MonObj R] [IsCommMonObj R] [Abelian C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]

  (A B : Mod C R)

private def swapHom : (Mod.tensorLeft B).obj A ⟶ (Mod.tensorLeft A).obj B :=
  Mod.tensorDesc _ (Mod.isBilinear_tensorπ B A).braiding

private theorem swap_fac :
    Mod.tensorπ A B ≫ (swapHom A B).hom = (β_ A.X B.X).hom ≫ Mod.tensorπ B A :=
  Mod.tensorπ_tensorDesc _ _

private theorem swap_involutive : swapHom A B ≫ swapHom B A = 𝟙 _ := by
  apply Mod.tensorLeft_obj_hom_ext
  rw [Mod.comp_hom', reassoc_of% swap_fac, swap_fac, SymmetricCategory.symmetry_assoc,
    Mod.id_hom', Category.comp_id]

private def swapIso : (Mod.tensorLeft B).obj A ≅ (Mod.tensorLeft A).obj B :=
  ⟨swapHom A B, swapHom B A, swap_involutive A B, swap_involutive B A⟩

variable [MonoidalPreadditive C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

private theorem evaluation_fac :
    Mod.tensorπ A B ≫ (swapHom A B ≫ (Mod.tensorLeftMap (Mod.bidual A (Mod.regular R))).app B ≫
      Mod.tensorDualToIhom ((Mod.ihom A).obj (Mod.regular R)) B).hom = Mod.toIhomDual A B := by
  let D := (Mod.ihom A).obj (Mod.regular R)
  apply Mod.hom_ext_of_evaluation (D := D)
  rw [Mod.comp_hom', Mod.comp_hom', reassoc_of% swap_fac, Mod.tensorπ_tensorLeftMap_assoc,
    Mod.tensorπ_tensorDualToIhom, comp_whiskerRight_assoc, comp_whiskerRight_assoc,
    Mod.tensorDualToIhomCurry_evaluation, Mod.toIhomDual_evaluation]
  unfold Mod.tensorDualToIhomAux Mod.toIhomDualAux Mod.rightAct
  erw [associator_naturality_middle_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
  change _ ≫ _ ≫ B.X ◁ Mod.uncurryHom (Mod.bidual A (Mod.regular R)) ≫ _ = _
  erw [Mod.uncurryHom_bidual, BraidedCategory.braiding_naturality_right_assoc]
  simp only [comp_whiskerRight]
  rw [BraidedCategory.braiding_tensor_right_hom, BraidedCategory.braiding_tensor_left_hom]
  dsimp only [D]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  erw [← comp_whiskerRight_assoc (β_ A.X B.X).hom (β_ B.X A.X).hom,
    SymmetricCategory.symmetry, id_whiskerRight, Category.id_comp]
  erw [Category.assoc]

end Modules

attribute [local instance] Sheaf.symmetricCategory
attribute [local instance 25000] SymmetricCategory.toBraidedCategory

local instance {ℓ : ℕ} [Fact ℓ.Prime] (X : Scheme.{u}) : IsCommMonObj (adicConstantSheaf ℓ X) :=
  adicConstantSheaf.isCommMonObj X

/-- The quotient evaluation map is an isomorphism for a lisse first factor. Interchange
the tensor factors, apply the lisse biduality isomorphism to the first sheaf, and evaluate
its dual. On generators this sends `(a,b)` to `φ ↦ φ(a)b` by the biduality and tensor-dual
evaluation identities. Sources: `Adic/LisseBidual.lean`, `Monoidal/Mod/TensorDualToIhom.lean`
and `Monoidal/Mod/IhomDual.lean`. -/
theorem adicLisseTensorEvaluation {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}}
    (A B : AdicSheaf ℓ X) (hA : IsAdicLisseSheaf A) :
    ∃ j : (Mod.tensorLeft B).obj A ≅ (Mod.ihom ((Mod.ihom A).obj (AdicSheaf.unit ℓ X))).obj B,
      Mod.tensorπ A B ≫ j.hom.hom = Mod.toIhomDual A B := by
  let U := AdicSheaf.unit ℓ X
  let D := (Mod.ihom A).obj U
  have : IsIso (Mod.bidual A U) := hA.isIso_bidual
  have hD : IsAdicLisseSheaf D := hA.ihom (isAdicLisseSheaf_adicConstantSheaf _)
  have := isIso_lisseAdicTensorDualToIhom D B hD
  refine ⟨swapIso A B ≪≫ (Mod.tensorLeftMapIso (asIso (Mod.bidual A U))).app B ≪≫
    asIso (Mod.tensorDualToIhom D B), evaluation_fac A B⟩

end WeilII
