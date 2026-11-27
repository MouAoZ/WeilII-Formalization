module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.BaseChangeMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedForgetMate
import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareCube
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareIsoSymm

/-! # Changing the horizontal functors in a right-derived exchange square -/

@[expose] public section

open CategoryTheory

namespace WeilII

private theorem directImageMateChange {A B : Type*} [Category A] [Category B]
    {U : B ⥤ A} {R : A ⥤ B} (adj : U ⊣ R)
    {P F : A ⥤ A} {Q G : B ⥤ B} (x : P ≅ F) (y : Q ≅ G)
    (b : Q ⋙ U ≅ U ⋙ P) (e : U ⋙ F ≅ G ⋙ U)
    (h : Functor.whiskerRight y.hom U ≫ e.inv = b.hom ≫ Functor.whiskerLeft U x.hom) :
    Functor.whiskerLeft R y.hom ≫ mateEquiv adj adj e.inv =
      mateEquiv adj adj b.hom ≫ Functor.whiskerRight x.hom R :=
  (mateEquiv_whiskerRight_comp adj adj y.hom e.inv).symm.trans
    ((congrArg (mateEquiv adj adj) h).trans (mateEquiv_comp_whiskerLeft adj adj b.hom x.hom))

private theorem derivePullConjugation {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (U : B ⥤ A) [U.Additive] [Limits.PreservesFiniteLimits U] [Limits.PreservesFiniteColimits U]
    {P F : A ⥤ A} [P.Additive] [F.Additive] [Limits.PreservesFiniteLimits P]
    [Limits.PreservesFiniteColimits P]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    {Q G : B ⥤ B} [Q.Additive] [G.Additive] [Limits.PreservesFiniteLimits Q]
    [Limits.PreservesFiniteColimits Q]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    (x : P ≅ F) (y : Q ≅ G) (b : Q ⋙ U ≅ U ⋙ P) (e : U ⋙ F ≅ G ⋙ U)
    (h : Functor.isoWhiskerRight y U ≪≫ e.symm = b ≪≫ Functor.isoWhiskerLeft U x) :
    Functor.whiskerRight (Functor.mapDerivedCategoryNatIso y).hom U.mapDerivedCategory ≫
        (Functor.mapDerivedCategorySquareIso e).inv =
      (Functor.mapDerivedCategorySquareIso b).hom ≫
        Functor.whiskerLeft U.mapDerivedCategory (Functor.mapDerivedCategoryNatIso x).hom := by
  have hh := congrArg (fun z ↦ (Functor.mapDerivedCategorySquareIso
    (F₁ := Q) (F₂ := U) (G₁ := U) (G₂ := F) z).hom) h
  rw [Functor.mapDerivedCategorySquareIso_trans_hom (H₁ := G) (H₂ := U),
    Functor.mapDerivedCategorySquareIso_trans_hom (H₁ := U) (H₂ := P),
    Functor.mapDerivedCategorySquareIso_isoWhiskerLeft_hom,
    Functor.mapDerivedCategorySquareIso_isoWhiskerRight_hom,
    Functor.mapDerivedCategorySquareIso_symm, Iso.symm_hom] at hh
  exact hh

private theorem mateComponent {A B : Type*} [Category A] [Category B] (R : A ⥤ B)
    {P F : A ⥤ A} {Q G : B ⥤ B} (x : P ⟶ F) (y : Q ⟶ G)
    (b : R ⋙ Q ⟶ P ⋙ R) (e e' : R ⋙ G ⟶ F ⋙ R)
    (h : Functor.whiskerLeft R y ≫ e = b ≫ Functor.whiskerRight x R)
    (he : e = e') (K : A) (v : Q.obj (R.obj K) ⟶ R.obj (P.obj K)) (hv : v = b.app K) :
    y.app (R.obj K) ≫ e'.app K = v ≫ R.map (x.app K) := by
  subst e' v
  exact congr_app h K

private theorem invertPullConjugation {C : Type*} [Category C] {A B D E : C}
    (ex : A ≅ B) (θ : D ≅ A) (ey : D ≅ E) (a : B ≅ E)
    (h : a = ex.symm ≪≫ θ.symm ≪≫ ey) :
    ey ≪≫ a.symm = θ ≪≫ ex := by
  subst a
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.self_symm_id_assoc]

universe v

/-- Conjugating the exact horizontal functors in a pullback square conjugates its
right-derived mate by the same changes of coordinates. -/
theorem rightDerivedExchangeConjugation {A B : Type*} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (U : B ⥤ A) [U.Additive] [Limits.PreservesFiniteLimits U] [Limits.PreservesFiniteColimits U]
    {P F : A ⥤ A} [P.Additive] [F.Additive] [Limits.PreservesFiniteLimits P]
    [Limits.PreservesFiniteColimits P]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    {Q G : B ⥤ B} [Q.Additive] [G.Additive] [Limits.PreservesFiniteLimits Q]
    [Limits.PreservesFiniteColimits Q]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [F.PreservesKInjectiveComplexes] {T : A ⥤ B} [T.Additive] (adj : U ⊣ T)
    (x : P ≅ F) (y : Q ≅ G) (b : Q ⋙ U ≅ U ⋙ P) (e : U ⋙ F ≅ G ⋙ U)
    (f : T ⋙ G ≅ F ⋙ T) (hm : mateEquiv adj adj e.inv = f.hom)
    (h : e = (Functor.isoWhiskerLeft U x).symm ≪≫ b.symm ≪≫ Functor.isoWhiskerRight y U)
    (K : DerivedCategory A)
    (bc : Q.mapDerivedCategory.obj (T.rightDerivedFunctor.obj K) ⟶
      T.rightDerivedFunctor.obj (P.mapDerivedCategory.obj K))
    (hb : bc = (adj.derivedBaseChange adj b).app K) :
    (Functor.mapDerivedCategoryNatIso y).hom.app (T.rightDerivedFunctor.obj K) ≫
        (Functor.rightDerivedFunctorCommIso f).hom.app K =
      bc ≫ T.rightDerivedFunctor.map ((Functor.mapDerivedCategoryNatIso x).hom.app K) := by
  have natural := directImageMateChange adj.mapDerivedCategoryRightDerivedAdjunction
    (Functor.mapDerivedCategoryNatIso x) (Functor.mapDerivedCategoryNatIso y)
    (Functor.mapDerivedCategorySquareIso b) (Functor.mapDerivedCategorySquareIso e)
    (derivePullConjugation U x y b e (invertPullConjugation _ _ _ _ h))
  exact mateComponent T.rightDerivedFunctor (Functor.mapDerivedCategoryNatIso x).hom
    (Functor.mapDerivedCategoryNatIso y).hom _ _ (Functor.rightDerivedFunctorCommIso f).hom
    natural (Adjunction.derived_exact_forget_mate adj adj G F e f hm) K bc hb

end WeilII
