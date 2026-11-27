module

public import WeilConjectures.CategoryTheory.Monoidal.ProjectionBaseChangeComp
public import WeilConjectures.CategoryTheory.Adjunction.FreeComparisonComp
import WeilConjectures.CategoryTheory.Adjunction.ExchangeConjugate
import WeilConjectures.CategoryTheory.Adjunction.ProjectionTrivial

/-! # Base change for a projection factored through two adjunctions -/

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace WeilII

private noncomputable def properPf {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
    [MonoidalCategory D] {L : D ⥤ C} {R : C ⥤ D} [L.Monoidal] (a : L ⊣ R) :
    curriedTensorInsertFunctor₁ R ⟶ curriedTensorPost R ⋙ (Functor.whiskeringLeft _ _ _).obj L :=
  { app := fun A ↦ { app := a.projectionMorphism A
                     naturality := fun _ _ h ↦ a.projectionMorphism_natural_right A h }
    naturality := fun _ _ h ↦ NatTrans.ext (funext (a.projectionMorphism_natural_left h)) }

private noncomputable def openPf {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
    [MonoidalCategory D] {J : C ⥤ D} {R : D ⥤ C} [R.Monoidal] (a : J ⊣ R)
    [∀ A B, IsIso (a.projectionComparison A B)] :
    curriedTensorInsertFunctor₁ J ⟶ curriedTensorPost J ⋙ (Functor.whiskeringLeft _ _ _).obj R :=
  { app := fun A ↦ { app := fun B ↦ inv (a.projectionComparison A B)
                     naturality := fun _ _ h ↦ a.inv_projectionComparison_natural_right A h }
    naturality := fun _ _ h ↦ NatTrans.ext (funext (a.inv_projectionComparison_natural_left h ·)) }

private theorem tensorSquareOfMixed
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory D]
    (Q : A ⥤ B) [Q.Monoidal] (S : B ⥤ D) [S.Monoidal]
    (R : A ⥤ C) [R.Monoidal] (P : C ⥤ D) [P.Monoidal]
    (θ φ : Q ⋙ S ⟶ R ⋙ P) (hφ : φ = θ) (K N : A)
    (h : S.map (Functor.LaxMonoidal.μ Q K N) ≫ θ.app (K ⊗ N) ≫ P.map (δ R K N) =
      δ S _ _ ≫ (θ.app K ⊗ₘ θ.app N) ≫ Functor.LaxMonoidal.μ P _ _) :
    φ.app (K ⊗ N) ≫ P.map (δ R K N) ≫ δ P _ _ =
      S.map (δ Q K N) ≫ δ S _ _ ≫ (φ.app K ⊗ₘ φ.app N) := by
  subst φ
  rw [← cancel_epi (S.map (Functor.LaxMonoidal.μ Q K N)), ← cancel_mono (Functor.LaxMonoidal.μ P (R.obj K) (R.obj N))]
  simp only [Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id,
    ← S.map_comp_assoc, Functor.Monoidal.μ_δ]
  rw [S.map_id, Category.id_comp]
  exact h

private theorem factorComponent
    {X Z Y : Type*} [Category* X] [Category* Z] [Category* Y] [MonoidalCategory X]
    (J : X ⥤ Z) (G : Z ⥤ Y) (K : X) {V W : X} (i : V ≅ W)
    {a b c : Y} {z : Z} (π : a ⟶ c) (k : c ⟶ G.obj (J.obj (K ⊗ V)))
    (l : a ⟶ b) (p : b ⟶ G.obj z) (o : z ⟶ J.obj (K ⊗ W))
    (y : b ⟶ G.obj (J.obj (K ⊗ V))) (e : l ≫ y = π ≫ k)
    (d : y = p ≫ G.map (o ≫ J.map (K ◁ i.inv))) :
    π ≫ k ≫ G.map (J.map (K ◁ i.hom)) = l ≫ p ≫ G.map o := by
  rw [← Category.assoc, ← e, d]
  simp only [Category.assoc, ← G.map_comp, ← J.map_comp, ← whiskerLeft_comp,
    Iso.inv_hom_id, whiskerLeft_id]
  rw [J.map_id, Category.comp_id]

/-- Paste the projection of a right adjoint with the inverse projection comparison of a
left adjoint. The proper exchange is specified by its counit equation and the open exchange
by its unit equation. Applying the two adjunction projection base-change lemmas identifies
the small squares, and vertical pasting gives the square for the composite. -/
public theorem openProperProjectionBaseChange
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
    (hC : ∀ A B, (P.app A).app B = ap.projectionMorphism (j.obj A) B ≫
      p.map (inv (aj.projectionComparison A (s.obj B)) ≫ j.map (A ◁ u.inv.app B)))
    (hC' : ∀ A B, (P'.app A).app B = ap'.projectionMorphism (j'.obj A) B ≫
      p'.map (inv (aj'.projectionComparison A (s'.obj B)) ≫ j'.map (A ◁ u'.inv.app B)))
    (he : E = Adjunction.compForgetIso O T)
    (hd : ∀ B, df.inv.app B = w.map (u.hom.app B) ≫ dj.inv.app (s.obj B) ≫
        r'.map (dp.inv.app B) ≫ u'.inv.app (q.obj B))
    (hj : ∀ A, aj'.unit.app (w.obj A) ≫ r'.map (O.inv.app A) =
        w.map (aj.unit.app A) ≫ dj.inv.app (j.obj A))
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
  refine ProjectionBaseChange.pfBaseChange_comp q v w T.hom O.hom E.hom dp dj df
    (properPf ap) (openPf aj) P (properPf ap') (openPf aj') P' (Iso.refl _) (Iso.refl _) u u' ?_ ?_ ?_ hd ?_ ?_
  · intro A B
    exact factorComponent j p A (u.app B) _ _ _ _ _ ((P.app A).app B) (by simp) (hC A B)
  · intro A B
    exact factorComponent j' p' A (u'.app B) _ _ _ _ _ ((P'.app A).app B) (by simp) (hC' A B)
  · intro A
    rw [he]
    simp [Adjunction.compForgetIso]
  · exact ProjectionBaseChange.pfBaseChange_of_counit ap' ap q v T.hom dp _ _
      ap.map_projectionMorphism_comp_counit ap'.map_projectionMorphism_comp_counit (by simpa only [hBC, hpθ] using hp)
      (fun A B ↦ tensorSquareOfMixed q s' s v θp dp.hom hpθ A B (hpt A B))
  · have (A : X') (B : Z') : IsIso (((openPf aj').app A).app B) :=
      inferInstanceAs (IsIso (inv (aj'.projectionComparison A B)))
    refine ProjectionBaseChange.pfBaseChange_of_projectionComparison aj aj'
      (Iso.refl _) (Iso.refl _) v w O.hom dj _ _ ?_ ?_ ?_ (fun A B ↦ tensorSquareOfMixed v r' r w θj dj.hom hjθ A B (hjt A B))
    · intro A B
      change inv _ ≫ 𝟙 _ ≫ aj.projectionComparison A B = 𝟙 _ ▷ B
      simp
    · intro A B
      change inv _ ≫ 𝟙 _ ≫ aj'.projectionComparison A B = 𝟙 _ ▷ B
      simp
    · intro A
      rw [Adjunction.exchangeLeft_eq_of_unit_app_comp aj aj' dj.symm O.inv hj]
      simp

end WeilII
