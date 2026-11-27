module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedExactLift
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Exact transport of descent data on a single complex -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

namespace WeilII

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The derived coefficient comparison on a single in any degree carries an ordinary
equivariant map to its derived single. -/
theorem singleWeilDatum {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ C) (H : D ⥤ D) [F.Additive] [H.Additive] [F.IsEquivalence] [H.IsEquivalence]
    (E : C ⥤ D) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (e : E ⋙ H ≅ F ⋙ E) {A : C} {B : D} (u : F.obj A ⟶ A) (v : H.obj B ⟶ B)
    (r : E.obj A ⟶ B) (h : H.map r ≫ v = e.hom.app A ≫ E.map u ≫ r) (i : ℤ) :
    IsWeilEquivariant H.mapDerivedCategory
      (transportWeilDatum E.mapDerivedCategory (IsoAlgebra.derivedExactCommIso e).symm
        ((F.mapDerivedCategorySingleFunctor i).hom.app A ≫ (DerivedCategory.singleFunctor C i).map u))
      ((H.mapDerivedCategorySingleFunctor i).hom.app B ≫ (DerivedCategory.singleFunctor D i).map v)
      ((E.mapDerivedCategorySingleFunctor i).hom.app A ≫ (DerivedCategory.singleFunctor D i).map r) := by
  have hc := Functor.mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategorySingleFunctor_hom_app
    F E A i
  have he := NatTrans.mapDerivedCategory_app_singleFunctor_obj e.hom A i
  change (Functor.mapDerivedCategoryNatIso e).hom.app _ = _ at he
  have hr := (H.mapDerivedCategorySingleFunctor i).hom.naturality r
  have hu := (E.mapDerivedCategorySingleFunctor i).hom.naturality u
  dsimp only [Functor.comp_map] at hr hu
  simp only [IsWeilEquivariant, transportWeilDatum, Iso.symm_inv, IsoAlgebra.derivedExactCommIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hr, reassoc_of% hu, ← reassoc_of% hc, Iso.inv_hom_id_app_assoc, he]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategorySingleFunctor_hom_app_assoc]
  simp only [← Functor.map_comp, h]

/-- The comparison from a single in degree i to a shifted object intertwines the
derived endofunctor datum with the shift of the degree-zero datum. -/
theorem singleWeilDatum_shift {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
    (H : D ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {B : D} (b : H.obj B ⟶ B) {T : DerivedCategory D} (d : H.mapDerivedCategory.obj T ⟶ T)
    (q : (DerivedCategory.singleFunctor D 0).obj B ⟶ T)
    (h : IsWeilEquivariant H.mapDerivedCategory
      ((H.mapDerivedCategorySingleFunctor 0).hom.app B ≫ (DerivedCategory.singleFunctor D 0).map b) d q)
    (i : ℤ) :
    IsWeilEquivariant H.mapDerivedCategory
      ((H.mapDerivedCategorySingleFunctor i).hom.app B ≫ (DerivedCategory.singleFunctor D i).map b)
      ((H.mapDerivedCategory.commShiftIso (-i)).hom.app T ≫ (shiftFunctor _ (-i)).map d)
      ((((DerivedCategory.singleFunctors D).shiftIso (-i) i 0 (by lia)).inv.app B) ≫
        (shiftFunctor _ (-i)).map q) := by
  let a := (DerivedCategory.singleFunctors D).shiftIso (-i) i 0 (by lia)
  have hs := H.mapDerivedCategorySingleFunctor_hom_app_shiftIso (-i) i 0 (by lia) B
  have hn := a.hom.naturality b
  dsimp only [Functor.comp_map] at hn
  unfold IsWeilEquivariant at h ⊢
  change H.mapDerivedCategory.map (a.inv.app B ≫ _) ≫ _ = _
  rw [← cancel_epi (H.mapDerivedCategory.map (a.hom.app B))]
  simp only [Functor.map_comp, Category.assoc]
  rw [← H.mapDerivedCategory.map_comp_assoc, Iso.hom_inv_id_app, H.mapDerivedCategory.map_id, Category.id_comp,
    reassoc_of% H.mapDerivedCategory.commShiftIso_hom_naturality, ← Functor.map_comp, h]
  rw [reassoc_of% hs, ← reassoc_of% hn]
  simp [a, Category.assoc]


/-- Transporting a datum along an isomorphism of functors commutes with shifting it. -/
theorem shiftedDatum_changeFunctor {D : Type*} [Category* D] [HasShift D ℤ]
    {P H : D ⥤ D} [P.CommShift ℤ] [H.CommShift ℤ] (t : P ≅ H) [t.inv.CommShift ℤ]
    {A : D} (d : P.obj A ⟶ A) (n : ℤ) :
    (H.commShiftIso n).hom.app A ≫ (shiftFunctor _ n).map (t.inv.app A ≫ d) =
      t.inv.app ((shiftFunctor _ n).obj A) ≫ (P.commShiftIso n).hom.app A ≫
        (shiftFunctor _ n).map d := by
  rw [Functor.map_comp, ← NatTrans.shift_app_comm_assoc]


/-- Switch the endofunctor of an equivariant single along an ordinary natural
isomorphism and a derived comparison. -/
theorem singleWeilDatum_changeFunctor {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
    {P H : D ⥤ D} [P.Additive] [H.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (j : P ≅ H) {L : DerivedCategory D ⥤ DerivedCategory D} (w : L ≅ P.mapDerivedCategory)
    {B : D} (b : P.obj B ⟶ B) {T : DerivedCategory D} (d : L.obj T ⟶ T)
    (q : (DerivedCategory.singleFunctor D 0).obj B ⟶ T)
    (h : P.mapDerivedCategory.map q ≫ w.inv.app T ≫ d =
      (P.mapDerivedCategorySingleFunctor 0).hom.app B ≫
        (DerivedCategory.singleFunctor D 0).map b ≫ q) :
    IsWeilEquivariant H.mapDerivedCategory
      ((H.mapDerivedCategorySingleFunctor 0).hom.app B ≫
        (DerivedCategory.singleFunctor D 0).map (j.inv.app B ≫ b))
      ((w ≪≫ Functor.mapDerivedCategoryNatIso j).inv.app T ≫ d) q := by
  let a := Functor.mapDerivedCategoryNatIso j
  have hj := NatTrans.mapDerivedCategory_app_singleFunctor_obj j.inv B 0
  change a.inv.app _ = _ at hj
  change H.mapDerivedCategory.map q ≫ (a.inv.app T ≫ w.inv.app T) ≫ d = _
  rw [Category.assoc, reassoc_of% (a.inv.naturality q), h, hj]
  simp [Functor.map_comp, Category.assoc]

end WeilII
