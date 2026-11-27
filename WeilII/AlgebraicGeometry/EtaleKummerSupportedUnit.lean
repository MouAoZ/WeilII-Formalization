module

public import WeilII.AlgebraicGeometry.EtaleKummerFreeBasisPullback
public import WeilII.AlgebraicGeometry.EtaleKummerUnitPresentation
public import WeilII.AlgebraicGeometry.EtaleSingleModelReductionPullback
public import WeilII.AlgebraicGeometry.EtaleKummerPowerPullback

/-! # Terminal pullback of the free integral coefficient map -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Etale
open CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

/-- The supported coefficient comparison is computed by the free integral presentations:
transport the monoidal coefficient unit on the terminal scheme in those presentations. -/
theorem etaleKummer_supported_freePresentation {A B : Type (u+1)} [CommRing A] [CommRing B]
    {ρ : A →+* B} (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})
    (X : Scheme.{u}) :
    (derivedExtendScalarsConstantComplexIso hρ ha X).hom =
      (derivedExtendScalars hρ ha X).map (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit X A).hom ≫
        ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars _ ρ)
          (derivedExtendScalarsAdjunction hρ ha X) ((extendScalarsToRestrictScalars ρ X).app X.constantSheafInt) ≫
        (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit X B).inv := by
  let S := ⊤_ Scheme.{u}
  let f : X ⟶ S := terminal.from X
  let α (T : Scheme.{u}) := (extendScalarsToRestrictScalars ρ T).app T.constantSheafInt
  let v : (f)^*[AddCommGrpCat.{u+1}].obj S.constantSheafInt ⟶ X.constantSheafInt :=
    (upperStarConstantSheafIso AddCommGrpCat.{u+1} f).hom.app (AddCommGrpCat.of (ULift.{u+1} (ZMod 0)))
  let q (R : Type (u+1)) [CommRing R] := (upperStarExtendScalarsConstantSheafIntIso R f).hom
  have hs := freeSheafReduction_pullback ρ f S.constantSheafInt
  have hn := (extendScalarsToRestrictScalars ρ X).naturality v
  dsimp only [Functor.comp_map] at hn
  have hsheaf : (f)^*[ModuleCat.{u+1} A].map (α S) ≫ (upperStarRestrictScalarsIso ρ f).hom.app _ ≫
      (Sheaf.restrictScalars _ ρ).map (q B) = q A ≫ α X := by
    dsimp only [q, upperStarExtendScalarsConstantSheafIntIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    rw [Functor.map_comp, reassoc_of% hs, Category.assoc, hn]
  let o (R : Type (u+1)) [CommRing R] (T : Scheme.{u}) := constantComplexIsoSingleFunctorExtendScalarsIntOfUnit T R
  let e := leftDerivedUpperStarConstantComplexIso A f
  let F := derivedExtendScalars hρ ha X
  let t := ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars _ ρ) (derivedExtendScalarsAdjunction hρ ha X) (α X)
  let b := F.map (o A X).hom ≫ t ≫ (o B X).inv
  have h := etaleReductionPullback_of_singleModels (A := A) (B := B) (ρ := ρ) f hρ ha
    (T := constantComplex A S) (U := constantComplex B S) (T' := constantComplex A X) (U' := constantComplex B X)
    (M := (extendScalars A S).obj S.constantSheafInt) (M' := (extendScalars A X).obj X.constantSheafInt)
    (N := (extendScalars B S).obj S.constantSheafInt) (N' := (extendScalars B X).obj X.constantSheafInt)
    (α S) (α X) (q A) (q B) hsheaf (o A S) (o B S) (o A X) (o B X)
    e.hom (leftDerivedUpperStarConstantComplexIso B f).hom
    (derivedExtendScalarsConstantComplexEtaIso hρ ha S).hom b (etaleKummer_eta_freePresentation hρ ha S) rfl
    (etaleKummer_unitPresentation_pullback A f) (etaleKummer_unitPresentation_pullback B f)
  change F.map e.inv ≫ _ ≫ _ ≫ _ = b
  exact (congrArg (F.map e.inv ≫ ·) h).trans ((F.mapIso e).inv_hom_id_assoc b)

end WeilII
