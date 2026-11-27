module

public import WeilII.CategoryTheory.KunnethComparison
public import WeilConjectures.CategoryTheory.Monoidal.ProjectionBaseChange

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace WeilII.KunnethComparison

/-- Paste the Künneth comparison with the four shriek exchanges and the three pullback
comparisons given as functor isomorphisms. Taking their components gives the hypotheses of
`paste`, with the two projection squares expressed by `PFBaseChange`. -/
public theorem pasteIso
    {P X Y S : Type*} [Category* P] [Category* X] [Category* Y] [Category* S]
    [MonoidalCategory P] [MonoidalCategory X] [MonoidalCategory S]
    [BraidedCategory P] [BraidedCategory X]
    (p : P ⥤ X) (f : X ⥤ S) (g : Y ⥤ S) (h : P ⥤ S)
    (ps : X ⥤ P) (ss : Y ⥤ P) (fs : S ⥤ X)
    (πp : curriedTensorInsertFunctor₁ p ⟶
      curriedTensorPost p ⋙ (Functor.whiskeringLeft X P X).obj ps)
    (πf : curriedTensorInsertFunctor₁ f ⟶
      curriedTensorPost f ⋙ (Functor.whiskeringLeft S X S).obj fs)
    (bc : g ⋙ fs ⟶ ss ⋙ p) (c : h ≅ p ⋙ f)
    (κ : ∀ A B, f.obj A ⊗ g.obj B ⟶ h.obj (ps.obj A ⊗ ss.obj B))
    (expand : ∀ A B, κ A B =
      ((πf.app A).app (g.obj B) ≫ f.map (A ◁ bc.app B)) ≫
      f.map (((β_ (p.obj (ss.obj B)) A).inv ≫ (πp.app (ss.obj B)).app A) ≫
        p.map (β_ (ps.obj A) (ss.obj B)).inv) ≫ c.inv.app (ps.obj A ⊗ ss.obj B))
    (FP : P ⥤ P) (FX : X ⥤ X) (FY : Y ⥤ Y) (F : S ⥤ S)
    [FP.Monoidal] [FX.Monoidal] [F.Monoidal]
    (ep : p ⋙ FX ≅ FP ⋙ p) (ef : f ⋙ F ≅ FX ⋙ f) (eg : g ⋙ F ≅ FY ⋙ g)
    (eh : h ⋙ F ≅ FP ⋙ h)
    (dp : ps ⋙ FP ≅ FX ⋙ ps) (ds : ss ⋙ FP ≅ FY ⋙ ss) (df : fs ⋙ FX ≅ F ⋙ fs)
    (projP : ProjectionBaseChange.PFBaseChange FX FP ep.hom dp.symm πp πp)
    (projF : ProjectionBaseChange.PFBaseChange F FX ef.hom df.symm πf πf)
    (base : ∀ B, FX.map (bc.app B) ≫ ep.hom.app (ss.obj B) ≫ p.map (ds.hom.app B) =
      df.hom.app (g.obj B) ≫ fs.map (eg.hom.app B) ≫ bc.app (FY.obj B))
    (comp : ∀ N, eh.hom.app N ≫ c.hom.app (FP.obj N) =
      F.map (c.hom.app N) ≫ ef.hom.app (p.obj N) ≫ f.map (ep.hom.app N))
    (braidP : ∀ U V, FP.map (β_ U V).hom ≫ δ FP V U = δ FP U V ≫ (β_ (FP.obj U) (FP.obj V)).hom)
    (braidX : ∀ U V, FX.map (β_ U V).hom ≫ δ FX V U = δ FX U V ≫ (β_ (FX.obj U) (FX.obj V)).hom)
    (K : X) (L : Y)
    (src : F.obj (f.obj K ⊗ g.obj L) ⟶ f.obj (FX.obj K) ⊗ g.obj (FY.obj L))
    (tgt : F.obj (h.obj (ps.obj K ⊗ ss.obj L)) ⟶ h.obj (ps.obj (FX.obj K) ⊗ ss.obj (FY.obj L)))
    (src_eq : src = δ F _ _ ≫ (ef.hom.app K ⊗ₘ eg.hom.app L))
    (tgt_eq : tgt = eh.hom.app (ps.obj K ⊗ ss.obj L) ≫
      h.map (δ FP (ps.obj K) (ss.obj L) ≫ (dp.hom.app K ⊗ₘ ds.hom.app L))) :
    F.map (κ K L) ≫ tgt = src ≫ κ (FX.obj K) (FY.obj L) ∧
      ∀ {K' L'} (x : K ⟶ K') (y : L ⟶ L'),
        κ K L ≫ h.map (ps.map x ⊗ₘ ss.map y) = (f.map x ⊗ₘ g.map y) ≫ κ K' L' := by
  exact WeilII.KunnethComparison.paste p f g h ps ss fs πp πf bc c κ expand FP FX FY F
    ep.hom ef.hom eg.hom eh.hom dp.hom.app ds.hom.app df.hom.app projP projF base comp
    braidP braidX K L src tgt src_eq tgt_eq

end WeilII.KunnethComparison
