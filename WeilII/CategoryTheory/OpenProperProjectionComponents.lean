module

public import WeilII.CategoryTheory.OpenProperProjectionBaseChange

/-! # Component hypotheses for open–proper projection base change -/

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace WeilII

/-- A projection for a composite factors through the proper adjunction projection, the inverse
open adjunction comparison and the triangle identifying the pullback of the composite. -/
@[expose] public def IsOpenProperProjection
    {X Z Y : Type*} [Category* X] [Category* Z] [Category* Y]
    [MonoidalCategory X] [MonoidalCategory Z] [MonoidalCategory Y]
    {j : X ⥤ Z} {r : Z ⥤ X} [r.Monoidal] {p : Z ⥤ Y} {s : Y ⥤ Z} [s.Monoidal]
    (aj : j ⊣ r) (ap : s ⊣ p) [∀ A B, IsIso (aj.projectionComparison A B)]
    {t : Y ⥤ X} (P : curriedTensorInsertFunctor₁ (j ⋙ p) ⟶
      curriedTensorPost (j ⋙ p) ⋙ (Functor.whiskeringLeft _ _ _).obj t) (u : t ≅ s ⋙ r) : Prop :=
  ∀ A B, (P.app A).app B = ap.projectionMorphism (j.obj A) B ≫
    p.map (inv (aj.projectionComparison A (s.obj B)) ≫ j.map (A ◁ u.inv.app B))

/-- The inverse open exchange transposes to the pullback of the unit followed by the
pullback square. The functors in the comparison are the right adjoints of the two open
extensions. -/
@[expose] public def IsOpenExchangeUnit
    {X Z X' Z' : Type*} [Category* X] [Category* Z] [Category* X'] [Category* Z']
    {j : X ⥤ Z} {r : Z ⥤ X} {j' : X' ⥤ Z'} {r' : Z' ⥤ X'}
    (aj : j ⊣ r) (aj' : j' ⊣ r') (v : Z ⥤ Z') (w : X ⥤ X')
    (O : j ⋙ v ≅ w ⋙ j') (d : v ⋙ r' ≅ r ⋙ w) : Prop :=
  ∀ A, aj'.unit.app (w.obj A) ≫ r'.map (O.inv.app A) =
    w.map (aj.unit.app A) ≫ d.inv.app (j.obj A)

/-- Component identity for a pullback comparison along two composable squares, using
the vertical composition isomorphisms on the source and target. -/
@[expose] public def IsPullbackComparisonPaste
    {X Z Y X' Z' Y' : Type*} [Category* X] [Category* Z] [Category* Y]
    [Category* X'] [Category* Z'] [Category* Y']
    {r : Z ⥤ X} {s : Y ⥤ Z} {r' : Z' ⥤ X'} {s' : Y' ⥤ Z'}
    {t : Y ⥤ X} {t' : Y' ⥤ X'} (q : Y ⥤ Y') (v : Z ⥤ Z') (w : X ⥤ X')
    (dj : v ⋙ r' ≅ r ⋙ w) (dp : q ⋙ s' ≅ s ⋙ v) (df : q ⋙ t' ≅ t ⋙ w)
    (u : t ≅ s ⋙ r) (u' : t' ≅ s' ⋙ r') : Prop :=
  ∀ B, df.inv.app B = w.map (u.hom.app B) ≫ dj.inv.app (s.obj B) ≫
    r'.map (dp.inv.app B) ≫ u'.inv.app (q.obj B)

/-- Apply the adjunction criterion with its component hypotheses bundled. Keeping the exchange
and its functors as variables allows specialization to restricted derived functors. -/
public theorem openProperProjectionBaseChange_of_components
    {X Z Y X' Z' Y' : Type*} [Category* X] [Category* Z] [Category* Y]
    [Category* X'] [Category* Z'] [Category* Y'] [MonoidalCategory X] [MonoidalCategory Z]
    [MonoidalCategory Y] [MonoidalCategory X'] [MonoidalCategory Z'] [MonoidalCategory Y']
    {j : X ⥤ Z} {r : Z ⥤ X} [r.Monoidal] {p : Z ⥤ Y} {s : Y ⥤ Z} [s.Monoidal]
    {j' : X' ⥤ Z'} {r' : Z' ⥤ X'} [r'.Monoidal] {p' : Z' ⥤ Y'} {s' : Y' ⥤ Z'} [s'.Monoidal]
    (aj : j ⊣ r) (ap : s ⊣ p) (aj' : j' ⊣ r') (ap' : s' ⊣ p')
    [∀ A B, IsIso (aj.projectionComparison A B)] [∀ A B, IsIso (aj'.projectionComparison A B)]
    {t : Y ⥤ X} {t' : Y' ⥤ X'}
    (q : Y ⥤ Y') [q.Monoidal] (v : Z ⥤ Z') [v.Monoidal] (w : X ⥤ X') [w.Monoidal]
    (O : j ⋙ v ≅ w ⋙ j') (T : p ⋙ q ≅ v ⋙ p') (E : (j ⋙ p) ⋙ q ≅ w ⋙ (j' ⋙ p'))
    (dj : v ⋙ r' ≅ r ⋙ w) (dp : q ⋙ s' ≅ s ⋙ v) (df : q ⋙ t' ≅ t ⋙ w)
    (P : curriedTensorInsertFunctor₁ (j ⋙ p) ⟶ curriedTensorPost (j ⋙ p) ⋙ (Functor.whiskeringLeft _ _ _).obj t)
    (P' : curriedTensorInsertFunctor₁ (j' ⋙ p') ⟶ curriedTensorPost (j' ⋙ p') ⋙ (Functor.whiskeringLeft _ _ _).obj t')
    (u : t ≅ s ⋙ r) (u' : t' ≅ s' ⋙ r')
    (hC : IsOpenProperProjection aj ap P u) (hC' : IsOpenProperProjection aj' ap' P' u')
    (he : E = Adjunction.compForgetIso O T)
    (hd : IsPullbackComparisonPaste q v w dj dp df u u')
    (hj : IsOpenExchangeUnit aj aj' v w O dj)
    (θj : v ⋙ r' ⟶ r ⋙ w) (θp : q ⋙ s' ⟶ s ⋙ v)
    (hjθ : dj.hom = θj) (hpθ : dp.hom = θp)
    (properBC : p ⋙ q ⟶ v ⋙ p') (hBC : T.hom = properBC)
    (hp : ∀ A, s'.map (properBC.app A) ≫ ap'.counit.app (v.obj A) =
        θp.app (p.obj A) ≫ v.map (ap.counit.app A))
    (hjt : ∀ A B, r'.map (Functor.LaxMonoidal.μ v A B) ≫ θj.app (A ⊗ B) ≫ w.map (δ r A B) =
      δ r' _ _ ≫ (θj.app A ⊗ₘ θj.app B) ≫ Functor.LaxMonoidal.μ w _ _)
    (hpt : ∀ A B, s'.map (Functor.LaxMonoidal.μ q A B) ≫ θp.app (A ⊗ B) ≫ v.map (δ s A B) =
      δ s' _ _ ≫ (θp.app A ⊗ₘ θp.app B) ≫ Functor.LaxMonoidal.μ v _ _) :
    ProjectionBaseChange.PFBaseChange q w E.hom df P P' := by
  exact openProperProjectionBaseChange aj ap aj' ap' q v w O T E dj dp df P P' u u'
    hC hC' he hd hj θj θp hjθ hpθ properBC hBC hp hjt hpt

end WeilII
