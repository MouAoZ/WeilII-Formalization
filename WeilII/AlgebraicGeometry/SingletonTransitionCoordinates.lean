module

public import WeilConjectures.CategoryTheory.Adjunction.UniversalArrowMate
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.Adjunction.MateCounitIsIso

/-! # Transporting the universal arrow of free evaluation along coefficient equivalences -/

public section
open CategoryTheory

namespace WeilII

set_option backward.isDefEq.respectTransparency false in
/-- A square of coefficient equivalences carrying one transition to another transports the
universal property of the singleton unit followed by that transition. -/
theorem singletonTransition_bijective_of_equivalences
    {C A B A' B' : Type*} [Category* C] [Category* A] [Category* B]
    [Category* A'] [Category* B'] (E : A ≌ B) (E' : A' ≌ B')
    {e : C ⥤ A} {f : C ⥤ B} {e' : C ⥤ A'} {f' : C ⥤ B'}
    {u : A' ⥤ A} {v : B' ⥤ B}
    (i : e ⋙ E.functor ≅ f) (j : e' ⋙ E'.functor ≅ f')
    (β : u ⋙ E.functor ≅ E'.functor ⋙ v)
    (s : e ⟶ e' ⋙ u) (t : f ⟶ f' ⋙ v)
    (square : ∀ X, E.functor.map (s.app X) ≫ β.hom.app (e'.obj X) ≫ v.map (j.hom.app X) =
      i.hom.app X ≫ t.app X)
    {L : A ⥤ C} {M : B ⥤ C} (a : L ⊣ e) (b : M ⊣ f) (P : B)
    (hs : ∀ N, Function.Bijective fun g : e'.obj (L.obj (E.inverse.obj P)) ⟶ N ↦
      (a.unit.app (E.inverse.obj P) ≫ s.app _) ≫ u.map g)
    (N : B') : Function.Bijective fun g : f'.obj (M.obj P) ⟶ N ↦
      (b.unit.app P ≫ t.app _) ≫ v.map g := by
  let X := L.obj (E.inverse.obj P)
  let a₀ := (E.symm.toAdjunction.comp a).ofNatIsoRight i
  let c : X ≅ M.obj P := (a₀.leftAdjointUniq b).app P
  let k := j.app X ≪≫ f'.mapIso c
  let η := a.unit.app (E.inverse.obj P) ≫ s.app X
  let γ := E.functor.map η ≫ β.hom.app (e'.obj X)
  let τ := mateEquiv E'.toAdjunction E.toAdjunction (TwoSquare.mk _ _ _ _ β.hom)
  have : IsIso (τ.app N) := by
    have : IsIso E.toAdjunction.unit := inferInstanceAs (IsIso E.unit)
    exact isIso_mateEquiv_app_of_isIso_map_counit E'.toAdjunction E.toAdjunction
      (TwoSquare.mk _ _ _ _ β.hom) N
      (inferInstanceAs (IsIso (E.inverse.map (v.map (E'.counit.app N)))))
  have hg := E'.toAdjunction.bijective_comp_map_of_unit_comp_map E.toAdjunction β.hom τ
    (fun K ↦ (unit_mateEquiv _ _ β.hom K).symm) η hs N
  have hunit : b.unit.app P = E.counitIso.inv.app P ≫
      E.functor.map (a.unit.app (E.inverse.obj P)) ≫ i.hom.app X ≫ f.map c.hom := by
    rw [← a₀.unit_leftAdjointUniq_hom_app b P]
    simp only [a₀, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Adjunction.comp_unit_app, Category.assoc]
    rfl
  have hcompat : b.unit.app P ≫ t.app (M.obj P) =
      E.counitIso.inv.app P ≫ γ ≫ v.map k.hom := by
    have hn := t.naturality c.hom
    change f.map c.hom ≫ t.app _ = t.app _ ≫ v.map (f'.map c.hom) at hn
    simp only [hunit, k, γ, η, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc]
    erw [hn, ← reassoc_of% (square X)]
  have hb := ((E.counitIso.symm.app P).symm.homFromEquiv (Z := v.obj N)).bijective.comp
    (hg.comp (k.homFromEquiv (Z := N)).symm.bijective)
  convert hb using 1
  funext g
  change (b.unit.app P ≫ t.app _) ≫ v.map g =
    E.counitIso.inv.app P ≫ γ ≫ v.map (k.hom ≫ g)
  rw [hcompat, v.map_comp]
  simp only [Category.assoc]

end WeilII
