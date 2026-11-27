module

public import WeilConjectures.PoincareDuality.Abstract

/-! # Naturality of relative Verdier exchange in its source -/

open CategoryTheory MonoidalCategory MonoidalClosed

namespace WeilII

/-- The relative Verdier exchange commutes with precomposition in the coefficient complex.
This uses naturality of the projection morphism in both variables. -/
public theorem verdierExchange_naturality
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalClosed C] [MonoidalClosed D] {F : D ⥤ C} {G : C ⥤ D} (a : F ⊣ G)
    {P : C ⥤ D} {S : D ⥤ C} (b : P ⊣ S)
    (pf : curriedTensorInsertFunctor₁ P ⟶
      curriedTensorPost P ⋙ (Functor.whiskeringLeft D C D).obj F)
    {K K' : C} (f : K ⟶ K') (L : D) :
    G.map ((pre f).app (S.obj L)) ≫ Verdier.exchange a b pf K L =
      Verdier.exchange a b pf K' L ≫ (pre (P.map f)).app L := by
  have left (T : C) : P.map f ▷ G.obj T ≫ Verdier.cupProduct a pf K' T =
      Verdier.cupProduct a pf K T ≫ P.map (f ▷ T) := by
    have h : P.map f ▷ G.obj T ≫ (pf.app K').app (G.obj T) =
        (pf.app K).app (G.obj T) ≫ P.map (f ▷ F.obj (G.obj T)) :=
      NatTrans.congr_app (pf.naturality f) _
    simp only [Verdier.cupProduct, Category.assoc, reassoc_of% h, ← P.map_comp,
      whisker_exchange]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app, Verdier.uncurry_exchange, Verdier.uncurry_exchange,
    Verdier.exchangePairing_eq_cupProduct, Verdier.exchangePairing_eq_cupProduct,
    Verdier.cupProduct_natural_right_assoc, reassoc_of% left, ← P.map_comp_assoc,
    ← P.map_comp_assoc, id_tensor_pre_app_comp_ev]

end WeilII
