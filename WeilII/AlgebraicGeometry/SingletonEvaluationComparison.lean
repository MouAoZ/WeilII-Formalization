module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Adjunction.UniversalArrowMate

/-! # Free evaluation and a square preserving universal arrows -/

public section

open CategoryTheory

namespace WeilII

set_option backward.isDefEq.respectTransparency false in
/-- Suppose the units of two free evaluations, followed by their transitions, are
universal arrows to scalar restriction. If the square of transitions commutes and
the scalar square has invertible right mate, the lower evaluation of the comparison
of free objects is invertible. -/
theorem singletonEvaluationComparison_isIso
    {C D A B A' B' : Type*} [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* A'] [Category* B']
    {F : C ⥤ D} {e : C ⥤ A} {f : D ⥤ B} {e' : C ⥤ A'} {f' : D ⥤ B'}
    {p : A ⥤ B} {p' : A' ⥤ B'} {u : A' ⥤ A} {v : B' ⥤ B}
    {L : A ⥤ C} {M : B ⥤ D} (a : L ⊣ e) (b : M ⊣ f)
    (i : e ⋙ p ⟶ F ⋙ f) (j : e' ⋙ p' ≅ F ⋙ f')
    (s : e ⟶ e' ⋙ u) (t : f ⟶ f' ⋙ v)
    (β : u ⋙ p ⟶ p' ⋙ v)
    (square : ∀ X, p.map (s.app X) ≫ β.app (e'.obj X) ≫ v.map (j.hom.app X) =
      i.app X ≫ t.app (F.obj X))
    {r : B ⥤ A} {r' : B' ⥤ A'} (a' : p' ⊣ r') (b' : p ⊣ r)
    [IsIso (mateEquiv a' b' (TwoSquare.mk _ _ _ _ β))] (P : A)
    (hs : ∀ N, Function.Bijective fun g : e'.obj (L.obj P) ⟶ N ↦
      (a.unit.app P ≫ s.app (L.obj P)) ≫ u.map g)
    (ht : ∀ N, Function.Bijective fun g : f'.obj (M.obj (p.obj P)) ⟶ N ↦
      (b.unit.app (p.obj P) ≫ t.app (M.obj (p.obj P))) ≫ v.map g) :
    IsIso (f'.map (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ i)).app P)) := by
  let α := ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ i)).app P
  let η := a.unit.app P ≫ s.app (L.obj P)
  let θ := b.unit.app (p.obj P) ≫ t.app (M.obj (p.obj P))
  let γ := p.map η ≫ β.app (e'.obj (L.obj P))
  have hγ (N) := a'.bijective_comp_map_of_unit_comp_map b' β (mateEquiv a' b' β)
    (fun K ↦ (unit_mateEquiv a' b' β K).symm) η hs N
  let k := f'.map α ≫ j.inv.app (L.obj P)
  have hk : θ ≫ v.map k = γ := by
    have hn := t.naturality α
    have hu := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ i) P
    change f.map α ≫ t.app _ = t.app _ ≫ v.map (f'.map α) at hn
    change p.map (a.unit.app P) ≫ i.app _ = b.unit.app _ ≫ f.map α at hu
    have hcomp : θ ≫ v.map (f'.map α) = γ ≫ v.map (j.hom.app (L.obj P)) := by
      dsimp only [θ, γ, η]
      erw [p.map_comp, Category.assoc, Category.assoc, Category.assoc, ← hn,
        ← Category.assoc, ← hu, Category.assoc, ← square]
    erw [show v.map k = v.map (f'.map α) ≫ v.map (j.inv.app _) from v.map_comp _ _,
      ← Category.assoc, hcomp, Category.assoc, ← v.map_comp, j.hom_inv_id_app, v.map_id]
    exact Category.comp_id _
  obtain ⟨l, hl⟩ := (hγ (f'.obj (M.obj (p.obj P)))).surjective θ
  change γ ≫ v.map l = θ at hl
  have : IsIso k := ⟨⟨l, (ht _).injective (by
    change θ ≫ v.map (k ≫ l) = θ ≫ v.map (𝟙 _)
    rw [v.map_comp, ← Category.assoc, hk, hl, v.map_id]
    exact (Category.comp_id θ).symm),
    (hγ _).injective (by
      change γ ≫ v.map (l ≫ k) = γ ≫ v.map (𝟙 _)
      rw [v.map_comp, ← Category.assoc, hl, hk, v.map_id]
      exact (Category.comp_id γ).symm)⟩⟩
  exact IsIso.of_isIso_comp_right (f'.map α) (j.inv.app (L.obj P))

end WeilII
