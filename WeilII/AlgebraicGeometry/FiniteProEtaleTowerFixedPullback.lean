module

public import WeilII.AlgebraicGeometry.FiniteProEtaleTowerGeometry
public import WeilII.AlgebraicGeometry.CoherentIntegralReductionEvaluation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.Adjunction.MateVCompIsIso
public import WeilConjectures.CategoryTheory.InverseMateEquivalence
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering

/-! # Fixed finite module coefficients in geometric pullback of the quotient tower -/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor

namespace WeilII.FiniteProEtaleTowerGeometry

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The chosen residue equivalences on two sites agree. Every residue lifts to an
integral element, and the two integral identifications both send it to its universe lift. -/
theorem residueEquiv_eq (S T : Scheme.{u}) (n : ℕ) :
    CoherentIntegralEvaluation.residueEquiv ℓ S n = CoherentIntegralEvaluation.residueEquiv ℓ T n := by
  let hS := exists_coherentIntegralQuotientComparison ℓ S
  let hT := exists_coherentIntegralQuotientComparison ℓ T
  ext ⟨x⟩
  obtain ⟨a, rfl⟩ := PadicAlgCl.integersModPowMk_surjective ℓ ℚ_[ℓ] (n+1) x
  have h : hS.choose a = hT.choose a := Subtype.ext
    ((hS.choose_spec.choose_spec.2.1 a).trans (hT.choose_spec.choose_spec.2.1 a).symm)
  exact (hS.choose_spec.choose_spec.2.2.choose_spec.1 n a).trans
    ((congrArg _ h).trans (hT.choose_spec.choose_spec.2.2.choose_spec.1 n a).symm)

abbrev fixed (V : Scheme.{u}) (n : ℕ) :=
  ConstantScalarRestriction.restriction (Scheme.ProEt.topology V) (FiniteProEtaleSystem.Coeff ℓ n) ⋙
  Sheaf.restrictScalars (Scheme.ProEt.topology V) (CoherentIntegralEvaluation.residueEquiv ℓ V n).toRingHom

abbrev mods (n : ℕ) := ModuleCat.{u+1} (ULift.{u+1} (PadicAlgCl.integersModPow ℓ ℚ_[ℓ] (n+1)))

theorem fixed_equivalence (V : Scheme.{u}) (n : ℕ) : (fixed ℓ V n).IsEquivalence := by
  have : (Sheaf.restrictScalars (Scheme.ProEt.topology V)
      (CoherentIntegralEvaluation.residueEquiv ℓ V n).toRingHom).IsEquivalence :=
    isEquivalence_sheafCompose_of_isEquivalence _ _
  unfold fixed
  infer_instance

private theorem unit_fac (V : Scheme.{u}) (A : Type (u+1)) [CommRing A] :
    realizationRingUnit (Scheme.ProEt.topology V) A ≫
        (realizationRingIso (Scheme.ProEt.topology V) A).hom.hom =
      toSheafify (Scheme.ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj (RingCat.of A)) := by
  dsimp only [realizationRingIso, Iso.app_hom]
  rw [constantCommuteCompose_hom_app_hom]
  unfold realizationRingUnit
  rw [← Category.assoc, sheafComposeIso_inv_fac]
  exact (toSheafify_naturality _ (Functor.constComp V.ProEtᵒᵖ (CommRingCat.of A)
    (forget₂ CommRingCat RingCat)).hom).symm.trans (by rfl)

theorem fixed_smul (V : Scheme.{u}) (n : ℕ)
    (M : realizationModules (Scheme.ProEt.topology V) (FiniteProEtaleSystem.Coeff ℓ n))
    (U : V.ProEtᵒᵖ) (r : ULift.{u+1} (PadicAlgCl.integersModPow ℓ ℚ_[ℓ] (n+1))) (x : M.val.obj U) :
    r • (show ((fixed ℓ V n).obj M).obj.obj U from x) =
      (realizationRingUnit (Scheme.ProEt.topology V) _).app U
        (CoherentIntegralEvaluation.residueEquiv ℓ V n r) • x := by
  let J := Scheme.ProEt.topology V
  let A := FiniteProEtaleSystem.Coeff.{u} ℓ n
  let b := CoherentIntegralEvaluation.residueEquiv ℓ V n r
  have h := congrArg (fun z ↦ z.app U b) (unit_fac V A)
  have hi := congrArg (fun z ↦ z.hom.app U) (realizationRingIso J A).hom_inv_id
  change (realizationRingIso J A).inv.hom.app U
    ((toSheafify J ((Functor.const V.ProEtᵒᵖ).obj (RingCat.of A))).app U b) • x = _
  erw [← h]
  exact congrArg (fun a ↦ a • x) (ConcreteCategory.congr_hom hi _)

theorem direct_constant {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (b : FiniteProEtaleSystem.Coeff.{u} ℓ n) :
    (levelRing ℓ f n).hom.app U ((realizationRingUnit (Scheme.ProEt.topology T) _).app U b) =
      (realizationRingUnit (Scheme.ProEt.topology S) _).app ((Scheme.proEtaleBaseChange f).op.obj U) b := by
  let A := CommRingCat.of (FiniteProEtaleSystem.Coeff.{u} ℓ n)
  let target := ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{u+1}
    (Scheme.ProEt.topology T) (Scheme.ProEt.topology S)).obj
      ((constantSheaf (Scheme.ProEt.topology S) CommRingCat.{u+1}).obj A)
  have h := ((sheafificationAdjunction _ CommRingCat.{u+1}).homEquiv
    ((Functor.const T.ProEtᵒᵖ).obj A) target).apply_symm_apply
    (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
      (toSheafify (Scheme.ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj A)))
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun z ↦ (z.app U).hom b) h

/-- Rewriting constant scalars on both sides of geometric direct image identifies
the two module structures on the very same additive sections. -/
def fixedPush {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :
    Scheme.coefficientProEtaleModuleDirectImage.{u,u} f
        (CommRingCat.of (FiniteProEtaleSystem.Coeff.{u} ℓ n)) ⋙ fixed ℓ T n ≅
      fixed ℓ S n ⋙ ProEtale.lowerStar (mods ℓ n) f := by
  refine NatIso.ofComponents (fun M ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun U ↦ ?_) ?_)) ?_
  · let L := ((fixed ℓ T n).obj ((Scheme.coefficientProEtaleModuleDirectImage.{u,u} f
        (CommRingCat.of (FiniteProEtaleSystem.Coeff.{u} ℓ n))).obj M)).obj.obj U
    let R := ((fixed ℓ S n).obj M).obj.obj ((Scheme.proEtaleBaseChange f).op.obj U)
    change L ≅ R
    let e : L ≃ₗ[ULift.{u+1} (PadicAlgCl.integersModPow ℓ ℚ_[ℓ] (n+1))] R :=
      { toFun := fun x ↦ x, invFun := fun x ↦ x, left_inv := fun _ ↦ rfl,
        right_inv := fun _ ↦ rfl, map_add' := fun _ _ ↦ rfl, map_smul' := by
          intro r x
          change r • (show ((fixed ℓ T n).obj _).obj.obj U from x) =
            r • (show ((fixed ℓ S n).obj M).obj.obj ((Scheme.proEtaleBaseChange f).op.obj U) from x)
          refine (fixed_smul ℓ T n _ U r x).trans ?_
          refine Eq.trans ?_ (fixed_smul ℓ S n M ((Scheme.proEtaleBaseChange f).op.obj U) r x).symm
          let U' := (Scheme.proEtaleBaseChange f).op.obj U
          let z : M.val.obj U' := x
          let t := CoherentIntegralEvaluation.residueEquiv ℓ T n r
          let uT := (realizationRingUnit (Scheme.ProEt.topology T) (FiniteProEtaleSystem.Coeff.{u} ℓ n)).app U
          let uS := (realizationRingUnit (Scheme.ProEt.topology S) (FiniteProEtaleSystem.Coeff.{u} ℓ n)).app U'
          change (levelRing ℓ f n).hom.app U (uT t) • z =
            uS (CoherentIntegralEvaluation.residueEquiv ℓ S n r) • z
          have e : t = CoherentIntegralEvaluation.residueEquiv ℓ S n r :=
            DFunLike.congr_fun (residueEquiv_eq ℓ T S n) r
          exact congrArg (fun a ↦ a • z) ((direct_constant ℓ f n U t).trans (congrArg uS e)) }
    exact e.toModuleIso
  · intros
    ext x
    rfl
  · intros
    ext U x
    rfl

/-- The left square is the inverse mate of the sectionwise identity. The vertical
functors are equivalences of coefficient models, so this inverse mate is invertible. -/
def atFixed {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :
    pull ℓ f ⋙ (ev ℓ S n ⋙ fixed ℓ S n) ≅
      (ev ℓ T n ⋙ fixed ℓ T n) ⋙ ProEtale.upperStar (mods ℓ n) f := by
  let ad := ProEtale.upperStarLowerStarAdjunction (mods ℓ n) f
  let d := fixedPush ℓ f n
  let a := (mateEquiv (adj ℓ f) (levelAdj ℓ f n)).symm (pushEval ℓ f n).hom
  let b := (mateEquiv (levelAdj ℓ f n) ad).symm d.hom
  have : IsIso a := (pullEval ℓ f n).isIso_inv
  have := fixed_equivalence ℓ T n
  have := fixed_equivalence ℓ S n
  have : IsIso b := isIso_inverseMate_of_equivalences (levelAdj ℓ f n) ad d
  have : IsIso (a.hComp b) := TwoSquare.isIso_hComp a b
  exact (asIso (a.hComp b)).symm

set_option maxHeartbeats 600000 in
/-- The geometric mate evaluates on sections as the identity at the base-changed test object.
This also fixes the normalization for derived evaluation. -/
theorem atFixed_mate {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    (M : WeilConjectures.SemilinearSections.Systems.{u+1,u,u+1} (Scheme.ProEt.topology S)
      (FiniteProEtaleSystem.rings ℓ S) (FiniteProEtaleSystem.steps ℓ S))
    (U : T.ProEtᵒᵖ) (x : _) :
    (((mateEquiv (adj ℓ f) (ProEtale.upperStarLowerStarAdjunction (mods ℓ n) f)
      (TwoSquare.mk _ _ _ _ (atFixed ℓ f n).inv)).app M).hom.app U) x = x := by
  let a := (mateEquiv (adj ℓ f) (levelAdj ℓ f n)).symm (pushEval ℓ f n).hom
  let ad := ProEtale.upperStarLowerStarAdjunction (mods ℓ n) f
  let b := (mateEquiv (levelAdj ℓ f n) ad).symm (fixedPush ℓ f n).hom
  change (((mateEquiv (adj ℓ f) ad (a.hComp b)).app M).hom.app U) x = x
  rw [mateEquiv_vcomp (adj ℓ f) (levelAdj ℓ f n) ad a b]
  have ha : mateEquiv (adj ℓ f) (levelAdj ℓ f n) a = (pushEval ℓ f n).hom :=
    (mateEquiv (adj ℓ f) (levelAdj ℓ f n)).apply_symm_apply _
  have hb : mateEquiv (levelAdj ℓ f n) ad b = (fixedPush ℓ f n).hom :=
    (mateEquiv (levelAdj ℓ f n) ad).apply_symm_apply _
  rw [ha, hb]
  rfl

end WeilII.FiniteProEtaleTowerGeometry
