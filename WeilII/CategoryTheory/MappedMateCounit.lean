module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates

open CategoryTheory

namespace WeilII

/-- Applying a coefficient functor to a mate and then composing with the target counit
gives the pullback of the transported source counit, up to isomorphism over the input.
The domain isomorphism uses the original invertible left-adjoint square. -/
public theorem mappedMate_overIso
    {C D C' D' A B A' B' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [Category* A] [Category* B] [Category* A'] [Category* B']
    {I : C ⥤ D} {S : D ⥤ C} {J : C' ⥤ D'} {H : D' ⥤ C'} {U : C ⥤ C'} {P : D ⥤ D'}
    (a : I ⊣ S) (b : J ⊣ H) (e : I ⋙ P ≅ U ⋙ J)
    {W : C ⥤ A} {V : D ⥤ B} {W' : C' ⥤ A'} {V' : D' ⥤ B'}
    {I' : A ⥤ B} {J' : A' ⥤ B'} {P' : B ⥤ B'}
    (ci : W ⋙ I' ≅ I ⋙ V) (cj : W' ⋙ J' ≅ J ⋙ V') (cp : V ⋙ P' ≅ P ⋙ V') (M : D) :
    let g := (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).app M
    Nonempty (Over.mk (J'.map (W'.map g) ≫ cj.hom.app _ ≫ V'.map (b.counit.app _)) ≅
      Over.mk (P'.map (ci.hom.app _ ≫ V.map (a.counit.app M)) ≫ cp.hom.app M)) := by
  intro g
  let dom := cj.app (U.obj (S.obj M)) ≪≫ V'.mapIso (e.symm.app _) ≪≫
    cp.symm.app _ ≪≫ P'.mapIso (ci.symm.app _)
  refine ⟨Over.isoMk dom ?_⟩
  change dom.hom ≫ P'.map (ci.hom.app _ ≫ V.map (a.counit.app M)) ≫ cp.hom.app M =
    J'.map (W'.map g) ≫ cj.hom.app _ ≫ V'.map (b.counit.app _)
  have hcp := cp.hom.naturality (a.counit.app M)
  have hcj := cj.hom.naturality g
  dsimp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hcp hcj
  simp only [dom, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  rw [← P'.map_comp_assoc, ci.inv_hom_id_app]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  erw [P'.map_id, Category.id_comp, hcp, cp.inv_hom_id_app_assoc, reassoc_of% hcj,
    ← V'.map_comp, ← V'.map_comp, mateEquiv_counit a b (TwoSquare.mk _ _ _ _ e.inv) M]

end WeilII
