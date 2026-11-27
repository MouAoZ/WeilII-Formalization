module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans

/-! # Localization of a commutative transition diagram for exact functors -/

public section
open CategoryTheory Limits

namespace WeilII

private structure Presentation {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (X : DerivedCategory C) where
  complex : CochainComplex C ℤ
  iso : X ≅ DerivedCategory.Q.obj complex

private noncomputable def Presentation.map {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] {X : DerivedCategory C}
    (p : Presentation X) (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : Presentation (F.mapDerivedCategory.obj X) :=
  ⟨(F.mapHomologicalComplex (.up ℤ)).obj p.complex,
    F.mapDerivedCategory.mapIso p.iso ≪≫ F.mapDerivedCategoryFactors.app p.complex⟩

private def Represents {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {X Y : DerivedCategory C} (p : Presentation X) (q : Presentation Y)
    (f : X ⟶ Y) (g : p.complex ⟶ q.complex) : Prop :=
  f ≫ q.iso.hom = p.iso.hom ≫ DerivedCategory.Q.map g

private theorem Represents.comp {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {X Y Z : DerivedCategory C} {p : Presentation X} {q : Presentation Y} {r : Presentation Z}
    {f : X ⟶ Y} {g : Y ⟶ Z} {u : p.complex ⟶ q.complex} {v : q.complex ⟶ r.complex}
    (h : Represents p q f u) (k : Represents q r g v) : Represents p r (f ≫ g) (u ≫ v) := by
  change (_ ≫ _) ≫ _ = _ ≫ DerivedCategory.Q.map (_ ≫ _)
  rw [Category.assoc, k, ← Category.assoc, h, Category.assoc, Functor.map_comp]

private theorem Represents.changeChain {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {X Y : DerivedCategory C} {p : Presentation X} {q : Presentation Y} {f : X ⟶ Y}
    {u v : p.complex ⟶ q.complex} (h : Represents p q f u) (e : u = v) :
    Represents p q f v := e ▸ h

private theorem Represents.eq {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {X Y : DerivedCategory C} {p : Presentation X} {q : Presentation Y} {f g : X ⟶ Y}
    {u v : p.complex ⟶ q.complex} (h : Represents p q f u) (k : Represents p q g v)
    (e : u = v) : f = g := by
  apply (cancel_mono q.iso.hom).mp
  exact h.trans ((congrArg (fun m ↦ p.iso.hom ≫ DerivedCategory.Q.map m) e).trans k.symm)

private theorem Represents.map {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] {X Y : DerivedCategory C}
    {p : Presentation X} {q : Presentation Y} {f : X ⟶ Y} {g : p.complex ⟶ q.complex}
    (h : Represents p q f g) (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : Represents (p.map F) (q.map F) (F.mapDerivedCategory.map f)
      ((F.mapHomologicalComplex (.up ℤ)).map g) := by
  dsimp [Represents, Presentation.map]
  rw [← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc,
    Functor.mapDerivedCategoryFactors_hom_naturality, Category.assoc]

private theorem represents_transformation {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] {F G : C ⥤ D}
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (t : F ⟶ G)
    {X : DerivedCategory C} (p : Presentation X) :
    Represents (p.map F) (p.map G) ((Functor.mapDerivedCategoryNatTrans t).app X)
      ((NatTrans.mapHomologicalComplex t (.up ℤ)).app p.complex) := by
  dsimp [Represents, Presentation.map]
  rw [← reassoc_of% ((Functor.mapDerivedCategoryNatTrans t).naturality p.iso.hom),
    Functor.mapDerivedCategoryNatTrans_fac, Category.assoc]

private theorem represents_composition {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X : DerivedCategory C} (p : Presentation X) :
    Represents (p.map (F ⋙ G)) ((p.map F).map G) ((Functor.mapDerivedCategoryCompIso F G).inv.app X)
      (𝟙 _) := by
  dsimp [Represents, Presentation.map]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% ((Functor.mapDerivedCategoryCompIso F G).inv.naturality p.iso.hom),
    Functor.mapDerivedCategoryCompIso_hom_app_factors]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem Represents.inv {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {X Y : DerivedCategory C} {p : Presentation X} {q : Presentation Y} {e : X ≅ Y}
    {u : p.complex ≅ q.complex} (h : Represents p q e.hom u.hom) :
    Represents q p e.inv u.inv := by
  change e.inv ≫ _ = _ ≫ DerivedCategory.Q.map u.inv
  rw [← cancel_epi e.hom, Iso.hom_inv_id_assoc, ← Category.assoc, h, Category.assoc,
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

private theorem represents_square {C D E K : Type*} [Category C] [Category D] [Category E]
    [Category K] [Abelian C] [Abelian D] [Abelian E] [Abelian K]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory K]
    {F : C ⥤ D} {G : D ⥤ K} {H : C ⥤ E} {J : E ⥤ K}
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (e : F ⋙ G ≅ H ⋙ J) {X : DerivedCategory C} (p : Presentation X) :
    Represents ((p.map F).map G) ((p.map H).map J) ((Functor.mapDerivedCategorySquareIso e).hom.app X)
      ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app p.complex) := by
  have left := Represents.inv (p := p.map (F ⋙ G)) (q := (p.map F).map G) (e := ((Functor.mapDerivedCategoryCompIso F G).symm.app X))
    (u := Iso.refl _) (represents_composition F G p)
  have middle : Represents (p.map (F ⋙ G)) (p.map (H ⋙ J))
      ((Functor.mapDerivedCategoryNatIso e).hom.app X)
      ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app p.complex) := by
    dsimp [Represents, Presentation.map]
    rw [← reassoc_of% ((Functor.mapDerivedCategoryNatIso e).hom.naturality p.iso.hom),
      Functor.mapDerivedCategoryNatIso_fac, Category.assoc]
    rfl
  apply (left.comp (middle.comp (represents_composition H J p))).changeChain
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- Localizing an ordinary commuting transition diagram preserves its commutativity
with the specified composition comparisons. The horizontal transitions may be
noninvertible.

Source: WeilConjectures, MapDerivedCategoryNatTrans, mapDerivedCategoryNatTrans_fac,
and MapDerivedCategoryMate, mapDerivedCategoryCompIso_hom_app_factors. Every derived
object is isomorphic to the image of a complex, so naturality allows us to evaluate
at a localized complex. Insert the comparison from each sequence of derived functors
on that complex to the localization of their composite on complexes. For a single
transformation the formula mapDerivedCategoryNatTrans_fac identifies its conjugate
with its degreewise application. For the two-functor squares, expand the square
comparison and use mapDerivedCategoryCompIso_hom_app_factors to cancel the adjacent
composition isomorphisms. Naturality of these factors gives the same identifications
when a functor is applied on either side. The two paths are now the localizations of
chain maps whose components agree by the original square in each degree. Cancel the
invertible comparisons at the endpoints. -/
theorem mapDerivedCategory_transition_square
    {C D S₀ S₁ T₀ T₁ : Type*}
    [Category C] [Category D] [Category S₀] [Category S₁] [Category T₀] [Category T₁]
    [Abelian C] [Abelian D] [Abelian S₀] [Abelian S₁] [Abelian T₀] [Abelian T₁]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory S₀] [HasDerivedCategory S₁] [HasDerivedCategory T₀] [HasDerivedCategory T₁]
    {F : C ⥤ D} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {A₀ : C ⥤ S₀} [A₀.Additive] [PreservesFiniteLimits A₀] [PreservesFiniteColimits A₀]
    {A₁ : C ⥤ S₁} [A₁.Additive] [PreservesFiniteLimits A₁] [PreservesFiniteColimits A₁]
    {B₀ : D ⥤ T₀} [B₀.Additive] [PreservesFiniteLimits B₀] [PreservesFiniteColimits B₀]
    {B₁ : D ⥤ T₁} [B₁.Additive] [PreservesFiniteLimits B₁] [PreservesFiniteColimits B₁]
    {F₀ : S₀ ⥤ T₀} [F₀.Additive] [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    {F₁ : S₁ ⥤ T₁} [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    {P : S₀ ⥤ S₁} [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {Q : T₀ ⥤ T₁} [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (v₀ : F ⋙ B₀ ≅ A₀ ⋙ F₀) (v₁ : F ⋙ B₁ ≅ A₁ ⋙ F₁)
    (w : P ⋙ F₁ ≅ F₀ ⋙ Q) (s : A₁ ⟶ A₀ ⋙ P) (t : B₁ ⟶ B₀ ⋙ Q)
    (hs : ∀ X, v₁.hom.app X ≫ F₁.map (s.app X) ≫ w.hom.app (A₀.obj X) =
      t.app (F.obj X) ≫ Q.map (v₀.hom.app X)) (X : DerivedCategory C) :
    F₁.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatTrans s ≫ (Functor.mapDerivedCategoryCompIso A₀ P).inv).app X) ≫
      (Functor.mapDerivedCategorySquareIso w).hom.app (A₀.mapDerivedCategory.obj X) ≫
      Q.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso v₀).inv.app X) =
    (Functor.mapDerivedCategorySquareIso v₁).inv.app X ≫
      (Functor.mapDerivedCategoryNatTrans t ≫ (Functor.mapDerivedCategoryCompIso B₀ Q).inv).app
        (F.mapDerivedCategory.obj X) := by
  let p : Presentation X := ⟨DerivedCategory.Q.objPreimage X, (DerivedCategory.Q.objObjPreimageIso X).symm⟩
  have hs' (Y : C) : F₁.map (s.app Y) ≫ w.hom.app (A₀.obj Y) ≫ Q.map (v₀.inv.app Y) =
      v₁.inv.app Y ≫ t.app (F.obj Y) := by
    rw [← cancel_epi (v₁.hom.app Y), Iso.hom_inv_id_app_assoc, ← Category.assoc,
      ← Category.assoc, Category.assoc (v₁.hom.app Y), hs, Category.assoc, ← Q.map_comp,
      Iso.hom_inv_id_app]
    erw [Q.map_id, Category.comp_id]
  have ls := (represents_transformation s p).comp (represents_composition A₀ P p)
  have rs := (represents_transformation t (p.map F)).comp (represents_composition B₀ Q (p.map F))
  have la := Represents.inv (p := (p.map F).map B₀) (q := (p.map A₀).map F₀) (e := (Functor.mapDerivedCategorySquareIso v₀).app X)
    (u := (NatIso.mapHomologicalComplex v₀ (.up ℤ)).app p.complex) (represents_square v₀ p)
  have lb := Represents.inv (p := (p.map F).map B₁) (q := (p.map A₁).map F₁) (e := (Functor.mapDerivedCategorySquareIso v₁).app X)
    (u := (NatIso.mapHomologicalComplex v₁ (.up ℤ)).app p.complex) (represents_square v₁ p)
  have lhs := (ls.map F₁).comp ((represents_square w (p.map A₀)).comp (la.map Q))
  have rhs := lb.comp rs
  apply lhs.eq rhs
  ext n
  change F₁.map (s.app (p.complex.X n) ≫ 𝟙 _) ≫ w.hom.app _ ≫ Q.map (v₀.inv.app _) =
    v₁.inv.app _ ≫ t.app _ ≫ 𝟙 _
  simpa only [Category.comp_id] using hs' (p.complex.X n)

private theorem represents_composition_hom {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    [Abelian C₁] [Abelian C₂] [Abelian C₃] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {Y : DerivedCategory C₁} (p : Presentation Y) :
    Represents ((p.map F).map G) (p.map (F ⋙ G)) ((Functor.mapDerivedCategoryCompIso F G).hom.app Y)
      (𝟙 _) :=
  Represents.inv (p := p.map (F ⋙ G)) (q := (p.map F).map G)
    (e := (Functor.mapDerivedCategoryCompIso F G).symm.app Y) (u := Iso.refl _)
    (represents_composition F G p)

/-- A transition square with a change of coordinates on its two coefficient categories
localizes with the canonical derived composition isomorphisms. -/
theorem mapDerivedCategory_transition_coordinates_square
    {C A B A' B' : Type*} [Category C] [Category A] [Category B] [Category A'] [Category B']
    [Abelian C] [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
    [HasDerivedCategory C] [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory A'] [HasDerivedCategory B']
    {e : C ⥤ A} [e.Additive] [PreservesFiniteLimits e] [PreservesFiniteColimits e]
    {e' : C ⥤ A'} [e'.Additive] [PreservesFiniteLimits e'] [PreservesFiniteColimits e']
    {W : A ⥤ B} [W.Additive] [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    {W' : A' ⥤ B'} [W'.Additive] [PreservesFiniteLimits W'] [PreservesFiniteColimits W']
    {u : A' ⥤ A} [u.Additive] [PreservesFiniteLimits u] [PreservesFiniteColimits u]
    {v : B' ⥤ B} [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
    (w : u ⋙ W ≅ W' ⋙ v) (s : e ⟶ e' ⋙ u) (t : e ⋙ W ⟶ (e' ⋙ W') ⋙ v)
    (hs : ∀ M, W.map (s.app M) ≫ w.hom.app (e'.obj M) = t.app M)
    (X : DerivedCategory C) :
    W.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatTrans s ≫
        (Functor.mapDerivedCategoryCompIso e' u).inv).app X) ≫
      (Functor.mapDerivedCategorySquareIso w).hom.app (e'.mapDerivedCategory.obj X) ≫
        v.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso e' W').hom.app X) =
    (Functor.mapDerivedCategoryCompIso e W).hom.app X ≫
      (Functor.mapDerivedCategoryNatTrans t ≫
        (Functor.mapDerivedCategoryCompIso (e' ⋙ W') v).inv).app X := by
  let p : Presentation X := ⟨DerivedCategory.Q.objPreimage X, (DerivedCategory.Q.objObjPreimageIso X).symm⟩
  have lhs := (((represents_transformation s p).comp (represents_composition e' u p)).map W).comp
    ((represents_square w (p.map e')).comp ((represents_composition_hom e' W' p).map v))
  have rhs := (represents_composition_hom e W p).comp ((represents_transformation t p).comp
    (represents_composition (e' ⋙ W') v p))
  apply lhs.eq rhs
  ext q
  change W.map (s.app (p.complex.X q) ≫ 𝟙 _) ≫ w.hom.app _ ≫ v.map (𝟙 _) =
    𝟙 _ ≫ t.app (p.complex.X q) ≫ 𝟙 _
  erw [v.map_id, Category.comp_id (w.hom.app _)]
  simpa only [Category.comp_id, Category.id_comp] using hs (p.complex.X q)

end WeilII
