module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Conjugate transformations of adjoint exact functors on derived categories -/

@[expose] public section

open CategoryTheory Limits Abelian

namespace WeilII

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  {L L' : C ⥤ D} {R R' : D ⥤ C}
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [R'.Additive] [PreservesFiniteLimits R'] [PreservesFiniteColimits R']

noncomputable local instance derivedSquare {F : C ⥤ D} [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    CatCommSq (F.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh
        DerivedCategory.Qh F.rightDerivedFunctor :=
  ⟨asIso F.rightDerivedFunctorUnit⟩

/-- Localize the homotopy-category adjunction along the invertible derivation units. -/
noncomputable def exactRightDerivedAdjunction (a : L ⊣ R) :
    L.rightDerivedFunctor ⊣ R.rightDerivedFunctor :=
  (a.mapHomotopyCategory (.up ℤ)).localization DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ)) DerivedCategory.Qh
    (HomotopyCategory.quasiIso D (.up ℤ)) _ _

private theorem exactRightDerivedAdjunction_unit (a : L ⊣ R) (K : HomotopyCategory C (.up ℤ)) :
    (exactRightDerivedAdjunction a).unit.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K) ≫
        R.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj K) ≫
          R.rightDerivedFunctor.map (L.rightDerivedFunctorUnit.app K) := by
  unfold exactRightDerivedAdjunction
  apply Adjunction.localization_unit_app

omit [HasKInjectiveResolutions D] in
private theorem derivation_naturality {F G : C ⥤ D} [F.Additive] [G.Additive]
    (t : F ⟶ G) (K : HomotopyCategory C (.up ℤ)) :
    F.rightDerivedFunctorUnit.app K ≫
        (Functor.rightDerivedFunctorNatTrans t).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory t (.up ℤ)).app K) ≫
        G.rightDerivedFunctorUnit.app K := by
  apply Functor.rightDerivedNatTrans_app

/-- For conjugate transformations between two exact adjunctions, the transformations of total
right derived functors are again conjugate under transposition. Check the unit equation on the essentially
surjective localization functor. Its factorization maps are the derivation units, which
intertwine each induced transformation with its image from the homotopy category. -/
theorem exactRightDerivedAdjunction_homEquiv (a : L ⊣ R) (a' : L' ⊣ R')
    (s : L' ⟶ L) (t : R ⟶ R')
    (h : ∀ X, a'.unit.app X ≫ R'.map (s.app X) = a.unit.app X ≫ t.app (L.obj X))
    {X : DerivedCategory C} {Y : DerivedCategory D} (x : L.rightDerivedFunctor.obj X ⟶ Y) :
    (exactRightDerivedAdjunction a').homEquiv X Y
        ((Functor.rightDerivedFunctorNatTrans s).app X ≫ x) =
      (exactRightDerivedAdjunction a).homEquiv X Y x ≫ (Functor.rightDerivedFunctorNatTrans t).app Y := by
  suffices hX : (exactRightDerivedAdjunction a').unit.app X ≫
      R'.rightDerivedFunctor.map ((Functor.rightDerivedFunctorNatTrans s).app X) =
      (exactRightDerivedAdjunction a).unit.app X ≫
        (Functor.rightDerivedFunctorNatTrans t).app (L.rightDerivedFunctor.obj X) by
    simp only [Adjunction.homEquiv_unit, Functor.map_comp]
    rw [← Category.assoc, hX, Category.assoc, Category.assoc,
      (Functor.rightDerivedFunctorNatTrans t).naturality]
  suffices e : (exactRightDerivedAdjunction a').unit ≫
      Functor.whiskerRight (Functor.rightDerivedFunctorNatTrans s) R'.rightDerivedFunctor =
      (exactRightDerivedAdjunction a).unit ≫
      Functor.whiskerLeft L.rightDerivedFunctor (Functor.rightDerivedFunctorNatTrans t) from
    NatTrans.congr_app e X
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  intro K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    exactRightDerivedAdjunction_unit, Category.assoc]
  rw [← Functor.map_comp, derivation_naturality s, Functor.map_comp]
  have hs := R'.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory s (.up ℤ)).app K)
  dsimp only [Functor.comp_map] at hs
  rw [← reassoc_of% hs, ← Functor.map_comp_assoc,
    Adjunction.mapHomotopyCategory_unit_app_comp (.up ℤ) a' a s t h, Functor.map_comp_assoc,
    ← reassoc_of% (derivation_naturality t _)]
  congr 1
  congr 1
  exact ((Functor.rightDerivedFunctorNatTrans t).naturality (L.rightDerivedFunctorUnit.app K)).symm

end WeilII
