module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Multifunctor
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.CommSq

/-! # Pasting the comparison squares for the inverse compact-support Künneth map -/

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace WeilII.KunnethComparison

variable {C D : Type*} [Category* C] [Category* D]

-- Transport a coefficient map first by exchange, then by the functor on coefficients.
private abbrev push {F : C ⥤ C} {G : D ⥤ D} {T : C ⥤ D} (e : T ⋙ G ⟶ F ⋙ T)
    {A A' : C} (a : F.obj A ⟶ A') := e.app A ≫ T.map a

private theorem push_square {F : C ⥤ C} {G : D ⥤ D} {T : C ⥤ D} (e : T ⋙ G ⟶ F ⋙ T)
    {A B A' B' : C} {u : A ⟶ B} {v : A' ⟶ B'} {a : F.obj A ⟶ A'} {b : F.obj B ⟶ B'}
    (sq : CommSq (F.map u) a b v) :
    CommSq (G.map (T.map u)) (push e a) (push e b) (T.map v) :=
  (CommSq.mk (e.naturality u)).vert_comp (T.map_commSq sq)

variable [MonoidalCategory C] [MonoidalCategory D]

private abbrev tensor {F : C ⥤ C} [F.OplaxMonoidal] {A A' B B' : C}
    (a : F.obj A ⟶ A') (b : F.obj B ⟶ B') := δ F A B ≫ (a ⊗ₘ b)

private theorem tensorRight_square {F : C ⥤ C} [F.OplaxMonoidal] {A A' B B' N N' : C}
    (a : F.obj A ⟶ A') {b : F.obj B ⟶ B'} {n : F.obj N ⟶ N'} {u : B ⟶ N} {v : B' ⟶ N'}
    (sq : CommSq (F.map u) b n v) :
    CommSq (F.map (A ◁ u)) (tensor a b) (tensor a n) (A' ◁ v) := by
  constructor
  dsimp only [tensor]
  rw [← δ_natural_right_assoc]
  simp only [Category.assoc, ← id_tensorHom,
    tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, sq.w]

private theorem braid_square {F : C ⥤ C} [F.OplaxMonoidal] [BraidedCategory C]
    (hβ : ∀ U V, F.map (β_ U V).hom ≫ δ F V U = δ F U V ≫ (β_ (F.obj U) (F.obj V)).hom)
    {A A' B B' : C} (a : F.obj A ⟶ A') (b : F.obj B ⟶ B') :
    CommSq (F.map (β_ A B).inv) (tensor b a) (tensor a b) (β_ A' B').inv := by
  have h : CommSq (F.mapIso (β_ A B)).hom (tensor a b) (tensor b a) (β_ A' B').hom := by
    constructor
    simp only [Functor.mapIso_hom, tensor, Category.assoc, ← Category.assoc (F.map _),
      hβ, Category.assoc, BraidedCategory.braiding_naturality]
  exact h.horiz_inv

private abbrev Projection (T : C ⥤ D) (R : D ⥤ C) :=
  curriedTensorInsertFunctor₁ T ⟶ curriedTensorPost T ⋙ (Functor.whiskeringLeft D C D).obj R

private theorem projection_naturality {T : C ⥤ D} {R : D ⥤ C} (π : Projection T R)
    {A A' : C} {B B' : D} (a : A ⟶ A') (b : B ⟶ B') :
    CommSq ((π.app A).app B) (T.map a ⊗ₘ b) (T.map (a ⊗ₘ R.map b)) ((π.app A').app B') := by
  have l : T.map a ▷ B ≫ (π.app A').app B = (π.app A).app B ≫ T.map (a ▷ R.obj B) :=
    NatTrans.congr_app (π.naturality a) B
  have r : T.obj A' ◁ b ≫ (π.app A').app B' = (π.app A').app B ≫ T.map (A' ◁ R.map b) :=
    (π.app A').naturality b
  constructor
  simp only [tensorHom_def, T.map_comp, Category.assoc, Functor.id_obj, r, reassoc_of% l]

private theorem projection_square {T : C ⥤ D} {R : D ⥤ C} (π : Projection T R)
    {F : C ⥤ C} [F.Monoidal] {G : D ⥤ D} [G.Monoidal]
    (e : T ⋙ G ⟶ F ⋙ T) (d : ∀ B, F.obj (R.obj B) ⟶ R.obj (G.obj B))
    (compat : ∀ A B, G.map ((π.app A).app B) ≫ e.app (A ⊗ R.obj B) ≫
        T.map (δ F A (R.obj B)) ≫ T.map (F.obj A ◁ d B) =
      δ G (T.obj A) B ≫ (e.app A ▷ G.obj B) ≫ (π.app (F.obj A)).app (G.obj B))
    {A A' : C} {B B' : D} (a : F.obj A ⟶ A') (b : G.obj B ⟶ B') :
    CommSq (G.map ((π.app A).app B)) (tensor (push e a) b) (push e (tensor a (d B ≫ R.map b)))
      ((π.app A').app B') := by
  have core := compat A B
  have h := projection_naturality π a b
  constructor
  dsimp only [push, tensor]
  have top := congrArg (· ≫ T.map (a ⊗ₘ R.map b)) core
  simp only [Category.assoc, ← T.map_comp, ← id_tensorHom,
    ← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp] at top
  rw [h.w] at top
  simpa only [curriedTensor_obj_obj, Functor.id_obj, Category.assoc, tensorHom_comp_tensorHom_assoc, Category.id_comp] using top

/-- Pasting the componentwise comparison squares of compact-support Künneth. The four
endomorphism functors act on the corners of the product square. The comparison includes
arbitrary maps on both coefficients after applying those functors.

Proof. Expand the inverse Künneth map as in the pinned
`PoincareDuality/CompactSupportKunneth.lean`, definitions 84–139. The naturality of each
curried projection attaches the given coefficient maps to its base-change square. Tensor
the square for base change on the left with the first coefficient. The braided comparison
and naturality of the braiding give both inner squares. Apply the first direct image to
their composite and paste the inverse of the direct-image composition square. -/
public theorem paste
    {P X Y S : Type*} [Category* P] [Category* X] [Category* Y] [Category* S]
    [MonoidalCategory P] [MonoidalCategory X] [MonoidalCategory S]
    [BraidedCategory P] [BraidedCategory X]
    (p : P ⥤ X) (f : X ⥤ S) (g : Y ⥤ S) (h : P ⥤ S)
    (ps : X ⥤ P) (ss : Y ⥤ P) (fs : S ⥤ X)
    (πp : curriedTensorInsertFunctor₁ p ⟶ curriedTensorPost p ⋙ (Functor.whiskeringLeft X P X).obj ps)
    (πf : curriedTensorInsertFunctor₁ f ⟶ curriedTensorPost f ⋙ (Functor.whiskeringLeft S X S).obj fs)
    (bc : g ⋙ fs ⟶ ss ⋙ p) (c : h ≅ p ⋙ f)
    (κ : ∀ A B, f.obj A ⊗ g.obj B ⟶ h.obj (ps.obj A ⊗ ss.obj B))
    (expand : ∀ A B, κ A B =
      ((πf.app A).app (g.obj B) ≫ f.map (A ◁ bc.app B)) ≫
      f.map (((β_ (p.obj (ss.obj B)) A).inv ≫ (πp.app (ss.obj B)).app A) ≫
        p.map (β_ (ps.obj A) (ss.obj B)).inv) ≫ c.inv.app (ps.obj A ⊗ ss.obj B))
    (FP : P ⥤ P) (FX : X ⥤ X) (FY : Y ⥤ Y) (F : S ⥤ S)
    [FP.Monoidal] [FX.Monoidal] [F.Monoidal]
    (ep : p ⋙ FX ⟶ FP ⋙ p) (ef : f ⋙ F ⟶ FX ⋙ f) (eg : g ⋙ F ⟶ FY ⋙ g)
    (eh : h ⋙ F ⟶ FP ⋙ h)
    (dp : ∀ A, FP.obj (ps.obj A) ⟶ ps.obj (FX.obj A))
    (ds : ∀ B, FP.obj (ss.obj B) ⟶ ss.obj (FY.obj B))
    (df : ∀ B, FX.obj (fs.obj B) ⟶ fs.obj (F.obj B))
    (projP : ∀ M A, FX.map ((πp.app M).app A) ≫ ep.app (M ⊗ ps.obj A) ≫
        p.map (δ FP M (ps.obj A)) ≫ p.map (FP.obj M ◁ dp A) =
      δ FX (p.obj M) A ≫ (ep.app M ▷ FX.obj A) ≫ (πp.app (FP.obj M)).app (FX.obj A))
    (projF : ∀ A B, F.map ((πf.app A).app B) ≫ ef.app (A ⊗ fs.obj B) ≫
        f.map (δ FX A (fs.obj B)) ≫ f.map (FX.obj A ◁ df B) =
      δ F (f.obj A) B ≫ (ef.app A ▷ F.obj B) ≫ (πf.app (FX.obj A)).app (F.obj B))
    (base : ∀ B, FX.map (bc.app B) ≫ ep.app (ss.obj B) ≫ p.map (ds B) =
      df (g.obj B) ≫ fs.map (eg.app B) ≫ bc.app (FY.obj B))
    (comp : ∀ N, eh.app N ≫ c.hom.app (FP.obj N) =
      F.map (c.hom.app N) ≫ ef.app (p.obj N) ≫ f.map (ep.app N))
    (braidP : ∀ U V, FP.map (β_ U V).hom ≫ δ FP V U = δ FP U V ≫ (β_ (FP.obj U) (FP.obj V)).hom)
    (braidX : ∀ U V, FX.map (β_ U V).hom ≫ δ FX V U = δ FX U V ≫ (β_ (FX.obj U) (FX.obj V)).hom)
    (K : X) (L : Y)
    (src : F.obj (f.obj K ⊗ g.obj L) ⟶ f.obj (FX.obj K) ⊗ g.obj (FY.obj L))
    (tgt : F.obj (h.obj (ps.obj K ⊗ ss.obj L)) ⟶ h.obj (ps.obj (FX.obj K) ⊗ ss.obj (FY.obj L)))
    (src_eq : src = δ F _ _ ≫ (ef.app K ⊗ₘ eg.app L))
    (tgt_eq : tgt = eh.app _ ≫ h.map (δ FP _ _ ≫ (dp K ⊗ₘ ds L))) :
    F.map (κ K L) ≫ tgt = src ≫ κ (FX.obj K) (FY.obj L) ∧
      ∀ {K' L'} (x : K ⟶ K') (y : L ⟶ L'),
        κ K L ≫ h.map (ps.map x ⊗ₘ ss.map y) = (f.map x ⊗ₘ g.map y) ≫ κ K' L' := by
  have compare
    (FP : P ⥤ P) (FX : X ⥤ X) (FY : Y ⥤ Y) (F : S ⥤ S)
    [FP.Monoidal] [FX.Monoidal] [F.Monoidal]
    (ep : p ⋙ FX ⟶ FP ⋙ p) (ef : f ⋙ F ⟶ FX ⋙ f) (eg : g ⋙ F ⟶ FY ⋙ g)
    (eh : h ⋙ F ⟶ FP ⋙ h)
    (dp : ∀ A, FP.obj (ps.obj A) ⟶ ps.obj (FX.obj A))
    (ds : ∀ B, FP.obj (ss.obj B) ⟶ ss.obj (FY.obj B))
    (df : ∀ B, FX.obj (fs.obj B) ⟶ fs.obj (F.obj B))
    (projP : ∀ M A, FX.map ((πp.app M).app A) ≫ ep.app (M ⊗ ps.obj A) ≫
        p.map (δ FP M (ps.obj A)) ≫ p.map (FP.obj M ◁ dp A) =
      δ FX (p.obj M) A ≫ (ep.app M ▷ FX.obj A) ≫ (πp.app (FP.obj M)).app (FX.obj A))
    (projF : ∀ A B, F.map ((πf.app A).app B) ≫ ef.app (A ⊗ fs.obj B) ≫
        f.map (δ FX A (fs.obj B)) ≫ f.map (FX.obj A ◁ df B) =
      δ F (f.obj A) B ≫ (ef.app A ▷ F.obj B) ≫ (πf.app (FX.obj A)).app (F.obj B))
    (base : ∀ B, FX.map (bc.app B) ≫ ep.app (ss.obj B) ≫ p.map (ds B) =
      df (g.obj B) ≫ fs.map (eg.app B) ≫ bc.app (FY.obj B))
    (comp : ∀ N, eh.app N ≫ c.hom.app (FP.obj N) =
      F.map (c.hom.app N) ≫ ef.app (p.obj N) ≫ f.map (ep.app N))
    (braidP : ∀ U V, FP.map (β_ U V).hom ≫ δ FP V U = δ FP U V ≫ (β_ (FP.obj U) (FP.obj V)).hom)
    (braidX : ∀ U V, FX.map (β_ U V).hom ≫ δ FX V U = δ FX U V ≫ (β_ (FX.obj U) (FX.obj V)).hom)
      {K' : X} {L' : Y} (x : FX.obj K ⟶ K') (y : FY.obj L ⟶ L') :
      F.map (κ K L) ≫ eh.app _ ≫ h.map (δ FP _ _ ≫
          ((dp K ≫ ps.map x) ⊗ₘ (ds L ≫ ss.map y))) =
        (δ F _ _ ≫ ((ef.app K ≫ f.map x) ⊗ₘ (eg.app L ≫ g.map y))) ≫ κ K' L' := by
    let m := ds L ≫ ss.map y
    let n := tensor (dp K ≫ ps.map x) m
    have sqBC : CommSq (FX.map (bc.app L)) (df (g.obj L) ≫ fs.map (push eg y)) (push ep m) (bc.app L') := by
      constructor
      have e := congrArg (· ≫ p.map (ss.map y)) (base L)
      have natural := bc.naturality y
      change fs.map (g.map y) ≫ bc.app L' = bc.app (FY.obj L) ≫ p.map (ss.map y) at natural
      simpa only [m, push, Category.assoc, Functor.map_comp, ← natural] using e
    have sqComp : CommSq (F.mapIso (c.app _)).hom (push eh n) (push ef (push ep n))
        (c.app _).hom := by
      constructor
      have e := congrArg (· ≫ f.map (p.map n)) (comp (ps.obj K ⊗ ss.obj L))
      have natural := c.hom.naturality n
      change h.map n ≫ c.hom.app _ = c.hom.app _ ≫ f.map (p.map n) at natural
      simpa only [Functor.mapIso_hom, Iso.app_hom, push, Functor.map_comp, Category.assoc,
        natural] using e.symm
    have sq₁ := projection_square πf ef df projF x (push eg y)
    have sq₂ := push_square ef (tensorRight_square x sqBC)
    have outerBraid := braid_square braidX (push ep m) x
    have innerProj := projection_square πp ep dp projP m x
    have innerBraid := push_square ep (braid_square braidP (dp K ≫ ps.map x) m)
    have inner := outerBraid.horiz_comp (innerProj.horiz_comp innerBraid)
    simp only [← FX.map_comp] at inner
    have sq₃ := push_square ef inner
    have total := sq₁.horiz_comp (sq₂.horiz_comp (sq₃.horiz_comp sqComp.horiz_inv))
    simpa only [expand, Functor.id_obj, Functor.map_comp, Functor.mapIso_inv, Iso.app_inv, push, tensor, m, n,
      Category.assoc] using total.w
  constructor
  · have ids := compare FP FX FY F ep ef eg eh dp ds df projP projF base comp braidP braidX
      (𝟙 (FX.obj K)) (𝟙 (FY.obj L))
    rw [ps.map_id, ss.map_id, f.map_id, g.map_id] at ids
    simpa only [src_eq, tgt_eq, Functor.comp_obj, Category.comp_id] using ids
  · intro K' L' x y
    have ids := compare (𝟭 _) (𝟭 _) (𝟭 _) (𝟭 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
      (fun _ ↦ 𝟙 _) (fun _ ↦ 𝟙 _) (fun _ ↦ 𝟙 _)
      (by intro A B; simp) (by intro A B; simp)
      (by intro B; simp) (by intro N; simp)
      (by intro A B; simp) (by intro A B; simp) x y
    simpa only [Functor.comp_obj, Functor.id_obj, Functor.id_map, Functor.OplaxMonoidal.id_δ,
      NatTrans.id_app, Category.id_comp] using ids

end WeilII.KunnethComparison
