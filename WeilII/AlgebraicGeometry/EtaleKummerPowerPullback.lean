module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionKummerClass

/-! # Pullback of the semilinear power map on roots of unity -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] (ρ : A →+* B)
  {X Y : Scheme.{u}} (f : X ⟶ Y)

private abbrev forgetMod (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :=
  sheafCompose T.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})

private theorem scalarUnit (T : Scheme.{u}) (M : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (extendScalarsAdjunction A T).unit.app M ≫
      (forgetMod A T).map ((extendScalarsToRestrictScalars ρ T).app M) =
      (extendScalarsAdjunction B T).unit.app M := by
  let a := extendScalarsAdjunction A T
  let e := Sheaf.extendScalarsAdjunction T.smallEtaleTopology ρ
  let b := (extendScalarsAdjunction B T).ofNatIsoRight
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl) :
      forgetMod B T ≅ Sheaf.restrictScalars T.smallEtaleTopology ρ ⋙ forgetMod A T)
  have h := Adjunction.unit_leftAdjointUniq_hom_app (a.comp e) b M
  simpa [a, b, e, Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    extendScalarsToRestrictScalars, forgetMod, extendScalarsCompSheafExtendScalarsIso] using h

private theorem pullUnit (R : Type (u + 1)) [CommRing R]
    (M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (extendScalarsAdjunction R Y).unit.app M ≫
      (forgetMod R Y).map ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app _ ≫
        (f)_*[ModuleCat.{u + 1} R].map ((upperStarExtendScalarsIso R f).hom.app M)) =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app M ≫
        (f)_*[AddCommGrpCat.{u + 1}].map ((extendScalarsAdjunction R X).unit.app _) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((extendScalarsAdjunction R Y).comp (upperStarLowerStarAdjunction _ f))
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).comp
      (extendScalarsAdjunction R X)).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))) M
  simp [upperStarExtendScalarsIso, Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    forgetMod] at h ⊢
  exact h

/-- Geometric pullback respects the coefficient unit on a free sheaf of modules. -/
theorem freeSheafReduction_pullback (M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (f)^*[ModuleCat.{u + 1} A].map ((extendScalarsToRestrictScalars ρ Y).app M) ≫
        (upperStarRestrictScalarsIso ρ f).hom.app _ ≫
        (Sheaf.restrictScalars _ ρ).map ((upperStarExtendScalarsIso B f).hom.app M) =
      (upperStarExtendScalarsIso A f).hom.app M ≫
        (extendScalarsToRestrictScalars ρ X).app _ := by
  let YR := Sheaf.restrictScalars Y.smallEtaleTopology ρ
  let XR := Sheaf.restrictScalars X.smallEtaleTopology ρ
  let pA := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let pB := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let pZ := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  let a := extendScalarsAdjunction A Y
  let α := (extendScalarsToRestrictScalars ρ Y).app M
  let qA := (upperStarExtendScalarsIso A f).hom.app M
  let qB := (upperStarExtendScalarsIso B f).hom.app M
  let β := (extendScalarsToRestrictScalars ρ X).app ((f)^*[AddCommGrpCat.{u + 1}].obj M)
  let PA := (f)_*[ModuleCat.{u + 1} A]
  let PB := (f)_*[ModuleCat.{u + 1} B]
  let PZ := (f)_*[AddCommGrpCat.{u + 1}]
  apply (pA.homEquiv _ _).injective
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (a.unit.app M ≫ (forgetMod A Y).map α) ≫ (forgetMod A Y).map
      (pA.unit.app _ ≫ PA.map ((upperStarRestrictScalarsIso ρ f).hom.app _ ≫ XR.map qB)) =
    (a.homEquiv _ _) ((pA.homEquiv _ _) (qA ≫ β))
  rw [scalarUnit ρ, Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  erw [pullUnit f A M]
  have hσ := restrictScalars_map_unit_app ρ f ((extendScalars B Y).obj M)
  have hleft : pA.unit.app _ ≫ PA.map ((upperStarRestrictScalarsIso ρ f).hom.app _ ≫ XR.map qB) =
      YR.map (pB.unit.app _ ≫ PB.map qB) := by
    rw [Functor.map_comp, ← Category.assoc]
    erw [← hσ, Functor.map_comp]
    rfl
  rw [hleft]
  change (extendScalarsAdjunction B Y).unit.app M ≫ (forgetMod B Y).map
      (pB.unit.app _ ≫ PB.map qB) = (pZ.unit.app M ≫ PZ.map
      ((extendScalarsAdjunction A X).unit.app _)) ≫ PZ.map ((forgetMod A X).map β)
  refine (pullUnit f B M).trans ?_
  rw [Category.assoc, ← PZ.map_comp]
  exact congrArg (fun z ↦ pZ.unit.app M ≫ PZ.map z) (scalarUnit ρ X _).symm

/-- The geometric comparison on roots of unity commutes with powering for every
scheme morphism. Both composites have the same image in the multiplicative group. -/
theorem rootsOfUnityPow_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (a b c : ℕ) (h : c = a * b) :
    (upperStar AddCommGrpCat.{u + 1} f).map (rootsOfUnityPow a b c h) ≫
        upperStarRootsOfUnitySheafToRootsOfUnitySheaf a f =
      upperStarRootsOfUnitySheafToRootsOfUnitySheaf c f ≫ rootsOfUnityPow a b c h := by
  let F := upperStar AddCommGrpCat.{u + 1} f
  have hi (n : ℕ) : upperStarRootsOfUnitySheafToRootsOfUnitySheaf n f ≫ X.rootsOfUnityι n =
      F.map (Y.rootsOfUnityι n) ≫ upperStarGmSheafToGmSheaf f :=
    upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι n f
  have hg : F.map (b • 𝟙 Y.gmSheaf) ≫ upperStarGmSheafToGmSheaf f =
      upperStarGmSheafToGmSheaf f ≫ (b • 𝟙 X.gmSheaf) := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Preadditive.nsmul_comp,
      Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]
  apply (cancel_mono (X.rootsOfUnityι a)).1
  change (F.map _ ≫ _) ≫ _ = _
  rw [Category.assoc, Category.assoc, hi, rootsOfUnityPow_ι, ← F.map_comp_assoc, rootsOfUnityPow_ι,
    F.map_comp, Category.assoc, hg, ← Category.assoc, ← hi]
  exact Category.assoc _ _ _

/-- The semilinear power map between positive Tate sheaves. This is the first
component of every coefficient-reduction map of pulled-back Kummer sequences. -/
noncomputable def kummerRootsReduction (T : Scheme.{u}) {d : ℕ}
    (hd : ringChar A = ringChar B * d) :
    tateSheaf A T ⟶ (Sheaf.restrictScalars _ ρ).obj (tateSheaf B T) :=
  (extendScalars A T).map (rootsOfUnityPow _ d _ hd) ≫ (extendScalarsToRestrictScalars ρ T).app _

/-- The semilinear Kummer power map on positive Tate sheaves commutes with geometric pullback. -/
theorem kummerRootsReduction_pullback {d : ℕ} (hd : ringChar A = ringChar B * d) :
    (f)^*[ModuleCat.{u + 1} A].map (kummerRootsReduction ρ Y hd) ≫
        (upperStarRestrictScalarsIso ρ f).hom.app _ ≫
        (Sheaf.restrictScalars _ ρ).map (upperStarTateSheafToTateSheaf B f) =
      upperStarTateSheafToTateSheaf A f ≫ kummerRootsReduction ρ X hd := by
  let RP := Sheaf.restrictScalars X.smallEtaleTopology ρ
  let F := (f)^*[ModuleCat.{u + 1} A]
  let EA := extendScalars A X
  let EB := extendScalars B X
  let powY := rootsOfUnityPow (X := Y) _ d _ hd
  let powX := rootsOfUnityPow (X := X) _ d _ hd
  let u := upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar A) f
  let v := upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar B) f
  have hs := freeSheafReduction_pullback ρ f (Y.rootsOfUnitySheaf (ringChar B))
  have hn := (upperStarExtendScalarsIso A f).hom.naturality powY
  have ht := (extendScalarsToRestrictScalars ρ X).naturality v
  dsimp only [Functor.comp_map] at hn ht
  let G := (f)^*[AddCommGrpCat.{u + 1}]
  let EAY := extendScalars A Y
  let hi := (upperStarExtendScalarsIso A f).hom.app (Y.rootsOfUnitySheaf (ringChar A))
  let lo := (upperStarExtendScalarsIso A f).hom.app (Y.rootsOfUnitySheaf (ringChar B))
  let low := (upperStarExtendScalarsIso B f).hom.app (Y.rootsOfUnitySheaf (ringChar B))
  let α := (extendScalarsToRestrictScalars ρ Y).app (Y.rootsOfUnitySheaf (ringChar B))
  let β := (extendScalarsToRestrictScalars ρ X).app (G.obj (Y.rootsOfUnitySheaf (ringChar B)))
  let γ := (extendScalarsToRestrictScalars ρ X).app (X.rootsOfUnitySheaf (ringChar B))
  let σ := (upperStarRestrictScalarsIso ρ f).hom.app (tateSheaf B Y)
  have square : F.map α ≫ σ ≫ RP.map low = lo ≫ β := hs
  have n : F.map (EAY.map powY) ≫ lo = hi ≫ EA.map (G.map powY) := hn
  have m : EA.map v ≫ γ = β ≫ RP.map (EB.map v) := ht
  have p : G.map powY ≫ v = u ≫ powX := rootsOfUnityPow_pullback f _ _ _ hd
  change F.map (EAY.map powY ≫ α) ≫ σ ≫ RP.map (low ≫ EB.map v) =
      (hi ≫ EA.map u) ≫ EA.map powX ≫ γ
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% square, reassoc_of% n, ← m, ← EA.map_comp_assoc, ← EA.map_comp_assoc, p]

end WeilII
