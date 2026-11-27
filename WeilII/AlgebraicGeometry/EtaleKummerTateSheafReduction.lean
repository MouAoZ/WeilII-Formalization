module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionKummerClass

/-! # The coefficient quotient on Kummer and positive Tate sheaves -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] {ρ : A →+* B}
  {V : Scheme.{u}} {C : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}}
  (φ : C ⟶ V.gmSheaf) {d : ℕ} (hd : ringChar A = ringChar B * d)

/-- In the adjunction for extension of coefficients, the first Kummer component
transposes to the extension-of-scalars transitivity map followed by the power map. -/
theorem kummerFirstTranspose_pow :
    ((Sheaf.extendScalarsAdjunction _ ρ).homEquiv _ _).symm
        (kummerSequenceReductionMap ρ φ hd).τ₁ =
      (extendScalarsCompSheafExtendScalarsIso ρ V).hom.app _ ≫
        (extendScalars B V).map (rootsOfUnityPow _ d _ hd) := by
  let f := rootsOfUnityPow (X := V) _ d _ hd
  apply ((Sheaf.extendScalarsAdjunction _ ρ).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp]
  change (extendScalars A V).map f ≫ (extendScalarsToRestrictScalars ρ V).app _ = _
  rw [(extendScalarsToRestrictScalars ρ V).naturality f]
  simp [extendScalarsToRestrictScalars]
  rfl

variable [NeZero (ringChar A)] [NeZero (ringChar B)]
  [HasInvertibleExponent A V] [HasInvertibleExponent B V]

omit [NeZero (ringChar A)] in
/-- The positive Tate sheaf comparison uses the specified exponent in the Kummer map. -/
theorem tateSheafReduction_eq_pow :
    (sheafExtendScalarsTateSheafIso ρ V).hom =
      (extendScalarsCompSheafExtendScalarsIso ρ V).hom.app _ ≫
        (extendScalars B V).map (rootsOfUnityPow _ d _ hd) := by
  have hb : 0 < ringChar B := Nat.pos_of_ne_zero (NeZero.ne _)
  have hdiv : ringChar A / ringChar B = d := by rw [hd, Nat.mul_div_cancel_left _ hb]
  simp only [sheafExtendScalarsTateSheafIso, extendScalarsRootsOfUnityIsoTateTwistSheaf,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  congr 1
  rw [← Functor.map_comp]
  congr 1
  have aux {a b c e : ℕ} (h : a = b * c) (h' : c = e) :
      eqToHom (show V.rootsOfUnitySheaf a = _ from congrArg V.rootsOfUnitySheaf h) ≫
        rootsOfUnityPow b c (b * c) rfl =
      rootsOfUnityPow b e a (h' ▸ h) := by
    subst a e
    simp
  exact aux (hdiv.symm ▸ hd : ringChar A = ringChar B * (ringChar A / ringChar B)) hdiv

/-- In tensor degree one, the comparison for a monoidal functor agrees with
the original comparison after removing the right unit factors. -/
theorem tensorPowNatMapIso_one_unitor {D E : Type*} [Category* D] [Category* E]
    [MonoidalCategory D] [MonoidalCategory E] (F : D ⥤ E) [F.Monoidal]
    {L : D} {L' : E} (h : F.obj L ≅ L') :
    (TensorInverse.tensorPowNatMapIso F h 1).hom ≫ (ρ_ L').hom =
      F.map (ρ_ L).hom ≫ h.hom := by
  rw [Functor.Monoidal.map_rightUnitor]
  simp only [TensorInverse.tensorPowNatMapIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Functor.Monoidal.μIso_inv, Functor.Monoidal.εIso_inv, tensorHom_def', Category.assoc,
    tensorPowNat, rightUnitor_naturality]

/-- Changing to the tensor model of the one-fold twist preserves the sheaf comparison. -/
theorem tateTwistSheafOne_reduction :
    (sheafExtendScalarsTateTwistSheafIso ρ V 1).hom ≫ (tateTwistSheafOneIso V B).hom =
      (Sheaf.extendScalars _ ρ).map (tateTwistSheafOneIso V A).hom ≫
        (sheafExtendScalarsTateSheafIso ρ V).hom := by
  let tA := (toInvertibleExponentBase (Λ := A) V)^*[ModuleCat.{u + 1} A]
  let tB := (toInvertibleExponentBase (Λ := B) V)^*[ModuleCat.{u + 1} B]
  let E := Sheaf.extendScalars V.smallEtaleTopology ρ
  let L := tateSheaf B (invertibleExponentBase.{u} B)
  let LX := tateSheaf A (invertibleExponentBase.{u} A)
  let h := sheafExtendScalarsUpperStarTateSheafIso ρ V
  have hA := tensorPowNatMapIso_one_unitor (tA ⋙ E) h
  have hB := tensorPowNatMapIso_one_unitor tB (Iso.refl (tB.obj L))
  rw [show (tateTwistSheafOneIso V B).hom = tB.map (ρ_ L).hom ≫
      (upperStarTateSheafIso B V).hom by rfl,
    show (tateTwistSheafOneIso V A).hom = tA.map (ρ_ LX).hom ≫
      (upperStarTateSheafIso A V).hom by rfl]
  change ((TensorInverse.tensorPowNatMapIso (tA ⋙ E) h 1).hom ≫
      (TensorInverse.tensorPowNatMapIso tB (Iso.refl _) 1).inv) ≫ _ = _
  simp only [Category.comp_id, Iso.refl_hom] at hB
  rw [Category.assoc, ← hB, Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hA, Functor.map_comp]
  simp only [h, sheafExtendScalarsUpperStarTateSheafIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.comp_map]
  rfl

variable (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})
/-- The derived first Kummer transpose is the flat comparison followed by the degree-zero
map of the positive Tate sheaf comparison. -/
theorem kummerFirstTranspose_flat :
    let E := Sheaf.extendScalars V.smallEtaleTopology ρ
    letI := preservesKFlatQuasiIso_extendScalars hρ ha V
    let hQ := ObjectProperty.prop_of_iso ObjectProperty.flat (tateTwistSheafOneIso V A)
      (flat_tateTwistSheaf A V 1)
    ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars _ ρ)
        (derivedExtendScalarsAdjunction hρ ha V) (kummerSequenceReductionMap ρ φ hd).τ₁ =
      (E.leftDerivedFunctorSingleFunctorIsoOfFlat hQ).hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map
        (sheafExtendScalarsTateSheafIso ρ V).hom := by
  dsimp only
  let E := Sheaf.extendScalars V.smallEtaleTopology ρ
  have := preservesKFlatQuasiIso_extendScalars hρ ha V
  have hQ := ObjectProperty.prop_of_iso ObjectProperty.flat (tateTwistSheafOneIso V A)
    (flat_tateTwistSheaf A V 1)
  have ht := (Sheaf.extendScalarsAdjunction _ ρ).singleTranspose_derivedAdjunctionMapDerivedCategory
    hQ (kummerSequenceReductionMap ρ φ hd).τ₁
  exact ht.trans (congrArg (fun z ↦ (E.leftDerivedFunctorSingleFunctorIsoOfFlat hQ).hom ≫
    (_root_.DerivedCategory.singleFunctor _ 0).map z)
    ((kummerFirstTranspose_pow (ρ := ρ) φ hd).trans (tateSheafReduction_eq_pow hd).symm))

end WeilII
