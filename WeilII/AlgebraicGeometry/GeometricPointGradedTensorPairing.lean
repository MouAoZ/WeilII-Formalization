module

public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.TraceFormula.DualizableShift
public import WeilConjectures.TraceFormula.PointTrace
public import Mathlib.LinearAlgebra.BilinearMap
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory

/-! # Bilinearity of tensoring shifted-unit classes -/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

set_option backward.isDefEq.respectTransparency.types false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 800000

namespace WeilII

universe u
variable (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
  [Fact (ringChar Ω ≠ ℓ)]

/-- Tensoring morphisms and precomposing with a map out of the unit in total degree gives
a bilinear pairing. Tensor with a shifted unit is naturally a shift. After this
identification, scalar compatibility in each variable is commutativity of scalar
endomorphisms of one shifted unit. -/
theorem exists_geometricPointGradedTensorPairing (A B : DerivedCategory (PointMod ℓ Ω))
    (a b d : ℤ) (h : a + b = d)
    (m : shiftedUnit ℓ Ω (-d) ⟶ shiftedUnit ℓ Ω (-a) ⊗ shiftedUnit ℓ Ω (-b)) :
    ∃ β : (gradedHom ℓ Ω (-a)).obj A →ₗ[PadicAlgCl ℓ]
        (gradedHom ℓ Ω (-b)).obj B →ₗ[PadicAlgCl ℓ] (gradedHom ℓ Ω (-d)).obj (A ⊗ B),
      ∀ x y, gradedHomHom ℓ Ω (β x y) = m ≫ (gradedHomHom ℓ Ω x ⊗ₘ gradedHomHom ℓ Ω y) := by
  let D := DerivedCategory (PointMod ℓ Ω)
  have comm := isCommMonObj_condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point Ω).left
  let : MonoidalClosed (PointMod ℓ Ω) := @Mod.monoidalClosed _ _ _ _ _ _ _ _ _ comm
  let : SymmetricCategory (PointMod ℓ Ω) := @Mod.symmetricCategory _ _ _ _ _ _ _ _ _ comm
  let : (curriedTensor D).CommShift₂Int := DerivedCategory.commShift₂CurriedTensor (PointMod ℓ Ω)
  let (X : D) : ((curriedTensor D).obj X).CommShift ℤ := Functor.CommShift₂.commShiftObj (h := .int) X
  let (X : D) : ((curriedTensor D).flip.obj X).CommShift ℤ := Functor.CommShift₂.commShiftFlipObj (h := .int) X
  have : MonoidalPreadditive D := DerivedCategory.monoidalPreadditive (A := PointMod ℓ Ω)
  let U := 𝟙_ D
  let S (n : ℤ) := shiftFunctor D n
  have scalar (F : D ⥤ D) (e : F ≅ S (-d)) (z : shiftedUnit ℓ Ω (-d) ⟶ F.obj U)
      (c : PadicAlgCl ℓ) :
      z ≫ F.map (pointScalar ℓ Ω c).asHom = (S (-d)).map (pointScalar ℓ Ω c).asHom ≫ z := by
    apply (cancel_mono (e.hom.app U)).1
    obtain ⟨t, ht⟩ := (shiftedUnitEquiv ℓ Ω (-d)).surjective (gradedHomMk ℓ Ω (z ≫ e.hom.app U))
    have ht' := congrArg (gradedHomHom ℓ Ω) ht
    rw [gradedHomHom_shiftedUnitEquiv] at ht'
    change (S (-d)).map (pointScalar ℓ Ω t).asHom = z ≫ e.hom.app U at ht'
    let f : U ⟶ U := (pointScalar ℓ Ω c).asHom
    let g : U ⟶ U := (pointScalar ℓ Ω t).asHom
    have hgf : g ≫ f = f ≫ g := congrArg End.asHom (show
      pointScalar ℓ Ω c * pointScalar ℓ Ω t = pointScalar ℓ Ω t * pointScalar ℓ Ω c by
      rw [← map_mul, ← map_mul, mul_comm])
    have hmap : (S (-d)).map g ≫ (S (-d)).map f = (S (-d)).map f ≫ (S (-d)).map g :=
      ((S (-d)).map_comp g f).symm.trans ((congrArg (S (-d)).map hgf).trans ((S (-d)).map_comp f g))
    calc
      (z ≫ F.map f) ≫ e.hom.app U = z ≫ (F.map f ≫ e.hom.app U) := Category.assoc _ _ _
      _ = z ≫ (e.hom.app U ≫ (S (-d)).map f) := z ≫= e.hom.naturality f
      _ = (z ≫ e.hom.app U) ≫ (S (-d)).map f := (Category.assoc _ _ _).symm
      _ = (S (-d)).map f ≫ (z ≫ e.hom.app U) := (ht'.symm =≫ _).trans (hmap.trans (_ ≫= ht'))
      _ = ((S (-d)).map f ≫ z) ≫ e.hom.app U := (Category.assoc _ _ _).symm
  let rightShift : tensorRight (shiftedUnit ℓ Ω (-b)) ≅ S (-b) :=
    (NatIso.ofComponents (F := tensorRight (shiftedUnit ℓ Ω (-b)))
      (G := tensorUnitRight D ⋙ S (-b))
      (fun X ↦ (((curriedTensor D).obj X).commShiftIso (-b)).app U) (by
        intro X Y f
        have := Functor.CommShift₂.commShift_map (G := curriedTensor D) (h := .int) f
        exact (NatTrans.shift_app_comm ((curriedTensor D).map f) (-b) U).symm)) ≪≫
      Functor.isoWhiskerRight (rightUnitorNatIso D) _ ≪≫ Functor.leftUnitor _
  let leftShift : tensorLeft (shiftedUnit ℓ Ω (-a)) ≅ S (-a) :=
    (NatIso.ofComponents (F := tensorLeft (shiftedUnit ℓ Ω (-a)))
      (G := tensorUnitLeft D ⋙ S (-a))
      (fun X ↦ (((curriedTensor D).flip.obj X).commShiftIso (-a)).app U) (by
        intro X Y f
        have := Functor.CommShift₂.commShift_flip_map (G := curriedTensor D) (h := .int) f
        exact (NatTrans.shift_app_comm ((curriedTensor D).flip.map f) (-a) U).symm)) ≪≫
      Functor.isoWhiskerRight (leftUnitorNatIso D) _ ≪≫ Functor.leftUnitor _
  have hl (c : PadicAlgCl ℓ) := scalar _ (Functor.isoWhiskerLeft (S (-a)) rightShift ≪≫
    (shiftFunctorAdd' D (-a) (-b) (-d) (by omega)).symm) m c
  have hr (c : PadicAlgCl ℓ) := scalar _ (Functor.isoWhiskerLeft (S (-b)) leftShift ≪≫
    (shiftFunctorAdd' D (-b) (-a) (-d) (by omega)).symm) m c
  change ∀ c, m ≫ ((S (-a)).map (pointScalar ℓ Ω c).asHom ▷ shiftedUnit ℓ Ω (-b)) =
    (S (-d)).map (pointScalar ℓ Ω c).asHom ≫ m at hl
  change ∀ c, m ≫ (shiftedUnit ℓ Ω (-a) ◁ (S (-b)).map (pointScalar ℓ Ω c).asHom) =
    (S (-d)).map (pointScalar ℓ Ω c).asHom ≫ m at hr
  refine ⟨LinearMap.mk₂ _ (fun x y ↦ gradedHomMk ℓ Ω (m ≫ (gradedHomHom ℓ Ω x ⊗ₘ gradedHomHom ℓ Ω y)))
    ?_ ?_ ?_ ?_, fun _ _ ↦ rfl⟩
  · intro x x' y
    change m ≫ ((gradedHomHom ℓ Ω x + gradedHomHom ℓ Ω x') ⊗ₘ _) = _
    rw [MonoidalPreadditive.add_tensor, Preadditive.comp_add]
    rfl
  · intro c x y
    change m ≫ (gradedHomHom ℓ Ω (c • x) ⊗ₘ gradedHomHom ℓ Ω y) = gradedHomHom ℓ Ω (c • _)
    rw [gradedHomHom_smul, gradedHomHom_smul]
    rw [← Category.id_comp (gradedHomHom ℓ Ω y), ← tensorHom_comp_tensorHom, tensorHom_id,
      ← Category.assoc, hl c, Category.assoc, Category.id_comp]
    rfl
  · intro x y y'
    change m ≫ (_ ⊗ₘ (gradedHomHom ℓ Ω y + gradedHomHom ℓ Ω y')) = _
    rw [MonoidalPreadditive.tensor_add, Preadditive.comp_add]
    rfl
  · intro c x y
    change m ≫ (gradedHomHom ℓ Ω x ⊗ₘ gradedHomHom ℓ Ω (c • y)) = gradedHomHom ℓ Ω (c • _)
    rw [gradedHomHom_smul, gradedHomHom_smul]
    rw [← Category.id_comp (gradedHomHom ℓ Ω x), ← tensorHom_comp_tensorHom, id_tensorHom,
      ← Category.assoc, hr c, Category.assoc, Category.id_comp]
    rfl

end WeilII
