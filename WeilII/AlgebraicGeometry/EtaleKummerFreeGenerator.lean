module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionKummerClass
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # The generator of the free constant coefficient sheaf -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Etale
open CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

private theorem zmodZeroGenerator (R : Type (u+1)) [CommRing R] :
    ((ModuleCat.extendScalarsAddCommGrpAdj R).homEquiv _ _
      (ModuleCat.extendScalarsAddCommGrpZModIso (Λ := R) (n := 0) (by simp)).hom).hom
        (ULift.up 1) = 1 := by
  let Z := AddCommGrpCat.of (ULift.{u+1} (ZMod 0))
  let R' := (forget₂ (ModuleCat.{u+1} R) AddCommGrpCat.{u+1}).obj (ModuleCat.of R R)
  let e := AddCommGrpCat.zmodHomEquiv (n := 0) R' (by simp)
  let a := ModuleCat.extendScalarsAddCommGrpAdj R
  change e (a.homEquiv Z _ ((a.homEquiv Z _).symm (e.symm (1 : R)))) = 1
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private noncomputable abbrev sectionsAdj (C : Type*) [Category.{u+1} C] (X : Scheme.{u})
    [HasWeakSheafify X.smallEtaleTopology C] :=
  constantSheafAdj X.smallEtaleTopology C terminalIsTerminal

/-- On global sections, the free constant generator maps to the constant section one. -/
theorem etaleKummer_freeGenerator (R : Type (u+1)) [CommRing R] (X : Scheme.{u})
    {N : Sheaf X.smallEtaleTopology (ModuleCat.{u+1} R)}
    (g : (constantSheaf X.smallEtaleTopology (ModuleCat.{u+1} R)).obj (ModuleCat.of R R) ⟶ N) :
    (((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u+1} terminalIsTerminal).comp (extendScalarsAdjunction R X)).homEquiv _ _
      ((extendScalarsConstantZModIso X (Λ := R) (n := 0) (by simp)).hom ≫ g)).hom
        (ULift.up 1) =
      (((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u+1} R) terminalIsTerminal).homEquiv _ _ g).hom 1) := by
  let c := sectionsAdj (ModuleCat.{u+1} R) X
  let a := (sectionsAdj AddCommGrpCat.{u+1} X).comp (extendScalarsAdjunction R X)
  let b := (ModuleCat.extendScalarsAddCommGrpAdj R).comp c
  let k := ModuleCat.extendScalarsAddCommGrpZModIso (Λ := R) (n := 0) (by simp)
  let M := AddCommGrpCat.of (ULift.{u+1} (ZMod 0))
  change (a.homEquiv _ _ (((constantSheafCompExtendScalarsIso R X).hom.app M ≫
    (constantSheaf _ _).map k.hom) ≫ g)).hom (ULift.up 1) = _
  have h (f : _ ⟶ N) : a.homEquiv _ _
      ((constantSheafCompExtendScalarsIso R X).hom.app M ≫ f) = b.homEquiv _ _ f := by
    rw [Adjunction.homEquiv_naturality_right]
    simp only [constantSheafCompExtendScalarsIso, a, sectionsAdj,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.ofNatIsoRight_unit,
      NatTrans.comp_app]
    rfl
  rw [Category.assoc, h]
  change (((ModuleCat.extendScalarsAddCommGrpAdj R).homEquiv _ _ (c.homEquiv _ _
    ((constantSheaf _ _).map k.hom ≫ g))).hom (ULift.up 1)) = _
  rw [c.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  change (c.homEquiv _ _ g).hom
    (((ModuleCat.extendScalarsAddCommGrpAdj R).homEquiv _ _ k.hom).hom (ULift.up 1)) = _
  rw [zmodZeroGenerator]

/-- Ordinary scalar extension carries the free rank-one basis to the coefficient unit. -/
theorem etaleKummer_freeBasis_reduction {A B : Type (u+1)} [CommRing A] [CommRing B]
    (ρ : A →+* B) (X : Scheme.{u}) :
    (extendScalarsToRestrictScalars ρ X).app X.constantSheafInt ≫
        (Sheaf.restrictScalars _ ρ).map (extendScalarsConstantZModIso X (Λ := B) (n := 0) (by simp)).hom =
      (extendScalarsConstantZModIso X (Λ := A) (n := 0) (by simp)).hom ≫
        Functor.LaxMonoidal.ε (Sheaf.restrictScalars X.smallEtaleTopology ρ) := by
  let α := (extendScalarsToRestrictScalars ρ X).app X.constantSheafInt
  let kB := (extendScalarsConstantZModIso X (Λ := B) (n := 0) (by simp)).hom
  let R := Sheaf.restrictScalars X.smallEtaleTopology ρ
  let F := ModuleCat.restrictScalars.{u+1} ρ
  let c := sectionsAdj AddCommGrpCat.{u+1} X
  let cA := sectionsAdj (ModuleCat.{u+1} A) X
  let cB := sectionsAdj (ModuleCat.{u+1} B) X
  let a := extendScalarsAdjunction A X
  let b := extendScalarsAdjunction B X
  have hα : a.homEquiv _ _ α = b.unit.app X.constantSheafInt := by
    rw [Adjunction.homEquiv_unit]
    let e := Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ
    have h := Adjunction.unit_leftAdjointUniq_hom_app (a.comp e)
      (b.ofNatIsoRight (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl) :
        sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u+1} B) AddCommGrpCat.{u+1}) ≅ R ⋙ sheafCompose _ (forget₂ (ModuleCat.{u+1} A) AddCommGrpCat.{u+1}))) X.constantSheafInt
    simpa [α, a, b, e, R, Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
      extendScalarsToRestrictScalars, extendScalarsCompSheafExtendScalarsIso] using h
  have hαk : (c.comp a).homEquiv _ _ (α ≫ R.map kB) = (c.comp b).homEquiv _ _ kB := by
    have hk : a.homEquiv X.constantSheafInt _ (α ≫ R.map kB) =
        b.homEquiv X.constantSheafInt _ kB := by
      rw [a.homEquiv_naturality_right, hα, b.homEquiv_unit]
      rfl
    rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
    exact congrArg (c.homEquiv _ _) hk
  apply ((c.comp a).homEquiv _ _).injective
  apply (AddCommGrpCat.zmodHomEquiv (n := 0) _ (by simp)).injective
  change ((c.comp a).homEquiv _ _ (α ≫ R.map kB)).hom (ULift.up 1) = _
  rw [hαk]
  have hB := etaleKummer_freeGenerator B X (𝟙 ((constantSheaf X.smallEtaleTopology _).obj (ModuleCat.of B B)))
  rw [Category.comp_id, Adjunction.homEquiv_id] at hB
  refine hB.trans ((Eq.trans ?_ (etaleKummer_freeGenerator A X (Functor.LaxMonoidal.ε R)).symm))
  change (cB.unit.app (ModuleCat.of B B)).hom (1 : B) = (cA.homEquiv (ModuleCat.of A A) _ (Functor.LaxMonoidal.ε R)).hom (1 : A)
  rw [Adjunction.homEquiv_unit]
  have h := congr_app (Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose X.smallEtaleTopology F)
    (op (⊤_ X.Etale))
  change ((Functor.LaxMonoidal.ε (sheafToPresheaf _ (ModuleCat.{u+1} A))).app _ ≫
      (Functor.LaxMonoidal.ε R).hom.app _) =
    Functor.LaxMonoidal.ε F ≫ F.map ((Functor.LaxMonoidal.ε (sheafToPresheaf _ (ModuleCat.{u+1} B))).app _) at h
  rw [← constantSheafAdj_unit_app_tensorUnit, ← constantSheafAdj_unit_app_tensorUnit] at h
  have h1 := congrArg (fun g ↦ g.hom (1 : A)) h
  change _ = (cB.unit.app (ModuleCat.of B B)).hom ((Functor.LaxMonoidal.ε (ModuleCat.restrictScalars ρ)) (1 : A)) at h1
  rw [ModuleCat.restrictScalars_η, ρ.map_one] at h1
  exact h1.symm

end WeilII






