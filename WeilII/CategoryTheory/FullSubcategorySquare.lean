module

public import WeilII.CategoryTheory.ExactRightDerivedSquare
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Natural squares of exact functors restricted to full derived subcategories -/

open CategoryTheory CategoryTheory.Limits

namespace WeilII

universe u v u' v' w w'

/-- Restrict the total right derived projection isomorphisms to full subcategories
preserved by the three functors. Restriction takes each component of the ambient
isomorphism at the underlying object, and the faithful inclusion detects both naturality
in the complex and compatibility with every pair of coefficient transformations. -/
public theorem fullSubcategoryExactRightDerivedSquare
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (J : C ⥤ D) [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    {I : Type*} (eligible : I → Prop) (F : Subtype eligible → D ⥤ D) (G : Subtype eligible → C ⥤ C)
    [∀ t, (F t).Additive] [∀ t, (G t).Additive]
    [∀ t, PreservesFiniteLimits (F t)] [∀ t, PreservesFiniteColimits (F t)]
    [∀ t, PreservesFiniteLimits (G t)] [∀ t, PreservesFiniteColimits (G t)]
    (e : ∀ t, J ⋙ F t ≅ G t ⋙ J)
    (P : ObjectProperty (DerivedCategory C)) (S : ObjectProperty (DerivedCategory D))
    (hJ : ∀ K, P K → S (J.rightDerivedFunctor.obj K))
    (hF : ∀ t K, S K → S ((F t).rightDerivedFunctor.obj K))
    (hG : ∀ t K, P K → P ((G t).rightDerivedFunctor.obj K))
    {C' : Type (max u v)} {D' : Type (max u' v')}
    [cC : Category.{w} C'] [cD : Category.{w'} D']
    (eqC : C' = P.FullSubcategory) (eqD : D' = S.FullSubcategory)
    (catC : HEq cC (inferInstance : Category P.FullSubcategory))
    (catD : HEq cD (inferInstance : Category S.FullSubcategory))
    (push : C' ⥤ D') (src : ∀ x, eligible x → D' ⥤ D')
    (dst : ∀ x, eligible x → C' ⥤ C')
    (ep : HEq push (P.liftFullSubcategory S J.rightDerivedFunctor hJ))
    (es : ∀ (a : Subtype eligible), HEq (src a.val a.property) (S.liftFullSubcategory S (F a).rightDerivedFunctor (hF a)))
    (ed : ∀ (a : Subtype eligible), HEq (dst a.val a.property) (P.liftFullSubcategory P (G a).rightDerivedFunctor (hG a)))
    (Arr : I → I → Type*) (f : ∀ (a b : Subtype eligible), Arr b.val a.val → (F a ⟶ F b))
    (g : ∀ (a b : Subtype eligible), Arr b.val a.val → (G a ⟶ G b))
    (s : ∀ x y hx hy, Arr x y → (src y hy ⟶ src x hx)) (t : ∀ x y hx hy, Arr x y → (dst y hy ⟶ dst x hx))
    (hs : ∀ (a b : Subtype eligible) u, HEq (s b.val a.val b.property a.property u) (S.liftFullSubcategoryMap S
      (Functor.rightDerivedFunctorNatTrans (f a b u)) (hF a) (hF b)))
    (ht : ∀ (a b : Subtype eligible) u, HEq (t b.val a.val b.property a.property u) (P.liftFullSubcategoryMap P
      (Functor.rightDerivedFunctorNatTrans (g a b u)) (hG a) (hG b)))
    (h : ∀ a b u N, (e a).hom.app N ≫ J.map ((g a b u).app N) =
        (f a b u).app (J.obj N) ≫ (e b).hom.app N) :
    ∃ p : ∀ (x : I) (hx : eligible x),
        push ⋙ src x hx ≅ dst x hx ⋙ push,
      ∀ (x y : I) (hx : eligible x) (hy : eligible y) (u : Arr x y)
        (B : C'),
        (p y hy).hom.app B ≫ push.map ((t x y hx hy u).app B) =
          (s x y hx hy u).app (push.obj B) ≫ (p x hx).hom.app B := by
  subst C' D'
  obtain rfl := eq_of_heq catC
  obtain rfl := eq_of_heq catD
  obtain rfl := eq_of_heq ep
  have hs' : src = fun x hx ↦ S.liftFullSubcategory S (F ⟨x, hx⟩).rightDerivedFunctor (hF ⟨x, hx⟩) :=
    funext (fun x ↦ funext (fun hx ↦ eq_of_heq (es ⟨x, hx⟩)))
  have ht' : dst = fun x hx ↦ P.liftFullSubcategory P (G ⟨x, hx⟩).rightDerivedFunctor (hG ⟨x, hx⟩) :=
    funext (fun x ↦ funext (fun hx ↦ eq_of_heq (ed ⟨x, hx⟩)))
  subst src dst
  obtain ⟨p, hp⟩ := exactRightDerivedSquare J F G e
  refine ⟨fun x hx ↦ NatIso.ofComponents (fun B ↦ S.isoMk ((p ⟨x, hx⟩).app B.obj))
    (fun u ↦ S.hom_ext ((p ⟨x, hx⟩).hom.naturality u.hom)), ?_⟩
  intro x y hx hy u B
  let a : Subtype eligible := ⟨y, hy⟩
  let b : Subtype eligible := ⟨x, hx⟩
  rw [eq_of_heq (hs a b u), eq_of_heq (ht a b u)]
  exact S.hom_ext (hp a b (f a b u) (g a b u) (h a b u) B.obj)

end WeilII
