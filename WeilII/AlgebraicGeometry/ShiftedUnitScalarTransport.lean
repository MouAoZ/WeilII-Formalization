module

public import WeilConjectures.TraceFormula.PointTrace
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
public import WeilConjectures.WeilSheaf.SmoothPurityFieldCompactificationExchange
import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelGaloisTrace

/-! # Scalar transport from a native single regular module to a shifted unit -/

public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

set_option backward.isDefEq.respectTransparency.types false
set_option maxSynthPendingDepth 10
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

namespace WeilII

universe u

/-- Every isomorphism from the single native regular module to the pullback of the shifted
unit intertwines constant scalars. This is independent of the target of any class. -/
theorem shiftedUnitScalarTransport (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [Field Ω]
    [Fact (ringChar Ω).Prime] [Fact (ringChar Ω ≠ ℓ)] {T : Scheme.{u}}
    (p : T ⟶ Spec (.of Ω)) (i : ℤ) (c : PadicAlgCl ℓ)
    (e : (adicSheafDerivedEquivCondensedMod ℓ T).functor.obj
        ((DerivedCategory.singleFunctor _ i).obj (AdicSheaf.unit ℓ T)) ≅
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) p).leftDerivedFunctor.obj
        (shiftedUnit ℓ Ω (-i))) :
    (adicSheafDerivedEquivCondensedMod ℓ T).functor.map ((DerivedCategory.singleFunctor _ i).map
        (AdicSheaf.smul (ULift.up c) (AdicSheaf.unit ℓ T))) ≫ e.hom =
      e.hom ≫ (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) p).leftDerivedFunctor.map
        ((shiftFunctor _ (-i)).map (pointScalar ℓ Ω c).asHom) := by
  let S := Spec (.of Ω)
  let A := (adicSheafEquivCondensedMod ℓ T).functor
  let B := (adicSheafEquivCondensedMod ℓ S).functor
  let Q := CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) p
  let P := Q.leftDerivedFunctor
  let R := adicUpperStar ℓ p
  let U := AdicSheaf.unit ℓ S
  let V := AdicSheaf.unit ℓ T
  let a := AdicSheaf.smul (ULift.up c) U
  let b := AdicSheaf.smul (ULift.up c) V
  let s := pointUnitEndRingHom ℓ Ω c
  let d := adicSheafEquivCondensedModUnitIso ℓ S
  have h₁ : CommSq b (adicUpperStarUnitIso ℓ p).inv (adicUpperStarUnitIso ℓ p).inv
      (R.map a) := by
    constructor
    rw [show R.map a = _ from adicUpperStar_map_smul p _ U]
    exact AdicSheaf.smul_comp _ _
  have h₂ := (adicUpperStarCompCondensedModIso ℓ p).hom.naturality a
  have h₃ : CommSq (B.map a) d.hom d.hom s.asHom := by
    constructor
    exact ((d.eq_inv_comp).mp
      (adicSheafEquivCondensedModUnitIso_inv_comp_map_smul_comp_hom S c).symm).symm
  let z := A.mapIso (adicUpperStarUnitIso ℓ p).symm ≪≫
    (adicUpperStarCompCondensedModIso ℓ p).app U ≪≫ Q.mapIso d
  have hz : CommSq (A.map b) z.hom z.hom (Q.map s.asHom) :=
    (A.map_commSq h₁).vert_comp (CommSq.vert_comp ⟨h₂⟩ (Q.map_commSq h₃))
  let L := DerivedCategory.singleFunctor (PointMod ℓ Ω) 0 ⋙ shiftFunctor _ (-i)
  let I := DerivedCategory.singleFunctor
    (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T)) i
  let J : L ⋙ P ≅ Q ⋙ I :=
    Functor.isoWhiskerRight ((DerivedCategory.singleFunctors _).shiftIso (-i) i 0 (by lia)) P ≪≫
      Functor.isoWhiskerLeft _ (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory _ p) ≪≫
      Q.mapDerivedCategorySingleFunctor i
  let H := DerivedCategory.singleFunctor (AdicSheaf ℓ T) i ⋙
    (adicSheafDerivedEquivCondensedMod ℓ T).functor
  let α := A.mapDerivedCategorySingleFunctor i
  let e₀ := α.app V ≪≫ I.mapIso z ≪≫ (J.app (𝟙_ (PointMod ℓ Ω))).symm
  have h₀ : CommSq (H.map b) e₀.hom e₀.hom (P.map (L.map s.asHom)) :=
    CommSq.vert_comp ⟨α.hom.naturality b⟩
      ((I.map_commSq hz).vert_comp ⟨J.inv.naturality s.asHom⟩)
  have hc (h : H.obj V ⟶ H.obj V) : CommSq (H.map b) h h (H.map b) := by
    obtain ⟨v, rfl⟩ := H.map_surjective h
    exact H.map_commSq ⟨AdicSheaf.smul_comp _ v⟩
  let C := PointMod ℓ Ω
  let F := HomologicalComplex.single C (ComplexShape.up ℤ) 0 ⋙
    HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let κ : DerivedCategory.singleFunctor C 0 ≅ F :=
    DerivedCategory.singleFunctorIsoCompQ C 0 ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso C).symm
  let D := shiftFunctor (DerivedCategory C) (-i) ⋙ P
  let e₁ := e₀ ≪≫ D.mapIso (κ.app (𝟙_ C))
  have h₁' := h₀.vert_comp (D.map_commSq ⟨κ.hom.naturality s.asHom⟩)
  have hn := ((hc (e.hom ≫ e₁.inv)).vert_comp h₁').w
  change H.map b ≫ (e.hom ≫ e₁.inv) ≫ e₁.hom = ((e.hom ≫ e₁.inv) ≫ e₁.hom) ≫
    D.map (F.map s.asHom) at hn
  have he : (e.hom ≫ e₁.inv) ≫ e₁.hom = e.hom :=
    (Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·) e₁.inv_hom_id).trans (Category.comp_id _))
  have hn' : H.map b ≫ e.hom = e.hom ≫ D.map (F.map s.asHom) :=
    (congrArg (H.map b ≫ ·) he.symm).trans
      (hn.trans (congrArg (· ≫ D.map (F.map s.asHom)) he))
  have hs : F.map s.asHom = (pointScalar ℓ Ω c).asHom := by
    let W := 𝟙_ (Dᵇc((point Ω).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    let K := (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (point Ω).left)).ι
    have hb : Function.Bijective (K.mapEndRingHom W) :=
      ((ObjectProperty.fullyFaithfulι _).mulEquivEnd _).bijective
    refine Eq.symm ((congrArg End.asHom ((RingEquiv.ofBijective _ hb).apply_symm_apply _)).trans ?_)
    have hε : Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := C)) = 𝟙 _ := rfl
    erw [Iso.conjRingEquiv_apply]
    simp only [Iso.symm_hom, Iso.symm_inv, asIso_hom, asIso_inv]
    let ε := Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := C))
    have : IsIso ε := inferInstanceAs (IsIso (𝟙 _))
    have hεinv : inv ε = 𝟙 _ := IsIso.inv_id
    exact (congrArg₂ (· ≫ ·) hε (congrArg (F.map s.asHom ≫ ·) hεinv)).trans
      ((Category.id_comp _).trans (Category.comp_id _))
  exact hn'.trans (congrArg (fun y ↦ e.hom ≫ D.map y) hs)

end WeilII
