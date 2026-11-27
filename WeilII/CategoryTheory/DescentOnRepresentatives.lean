module

public import WeilConjectures.CategoryTheory.WeilEquivariance
public import Mathlib.CategoryTheory.CommSq

/-! # Transport of descent on representatives across two coefficient functors -/

open CategoryTheory

namespace WeilII

/-- A compatible morphism stays equivariant after replacing the target endofunctor
by a naturally isomorphic one, with both transported data expressed by their maps. -/
public theorem equivariant_of_pullback_square
    {C D : Type*} [Category* C] [Category* D] (P : C ⥤ D) (G : C ⥤ C)
    (F H : D ⥤ D) (t : F ≅ H) (d : G ⋙ P ≅ P ⋙ F)
    {J : C} {A : D} (s : G.obj J ⟶ J) (r : P.obj J ⟶ A) (v : F.obj A ⟶ A)
    (h : d.hom.app J ≫ F.map r ≫ v = P.map s ≫ r) :
    IsWeilEquivariant H
      (transportWeilDatum P (Functor.isoWhiskerLeft P t.symm ≪≫ d.symm).symm s)
      (t.inv.app A ≫ v) r := by
  change H.map r ≫ t.inv.app A ≫ v =
    ((t.inv.app (P.obj J) ≫ d.inv.app J) ≫ P.map s) ≫ r
  rw [reassoc_of% (t.inv.naturality r)]
  simp only [Category.assoc]
  exact congrArg (t.inv.app _ ≫ ·) ((d.app J).eq_inv_comp.mpr h)

/-- Conjugating a morphism by its source and target descent data commutes with
transport across an equivariant comparison at each endpoint. -/
public theorem preimage_conjugate_descent
    {C D V : Type*} [Category* C] [Category* D] [Category* V]
    (F : C ⥤ C) (G : D ⥤ D) (H : V ⥤ V)
    (E : C ⥤ V) [E.Full] [E.Faithful] (P : D ⥤ V)
    (c : E ⋙ H ≅ F ⋙ E) (d : P ⋙ H ≅ G ⋙ P)
    {A B : C} {J K : D} (u : F.obj A ≅ A) (z : F.obj B ⟶ B)
    (r : G.obj J ≅ J) (t : G.obj K ⟶ K)
    (a : E.obj A ⟶ P.obj J) (b : P.obj K ⟶ E.obj B)
    (ha : IsWeilEquivariant H (transportWeilDatum E c.symm u.hom)
      (transportWeilDatum P d.symm r.hom) a)
    (hb : IsWeilEquivariant H (transportWeilDatum P d.symm t)
      (transportWeilDatum E c.symm z) b) (v : J ⟶ K) :
    E.preimage (a ≫ P.map (r.inv ≫ G.map v ≫ t) ≫ b) =
      u.inv ≫ F.map (E.preimage (a ≫ P.map v ≫ b)) ≫ z := by
  let l := c.app A ≪≫ E.mapIso u
  let m := d.app J ≪≫ P.mapIso r
  have sq : CommSq (H.map a) l.hom m.hom a := ⟨ha⟩
  have ai : a ≫ P.map r.inv = E.map u.inv ≫ c.inv.app A ≫ H.map a ≫ d.hom.app J := by
    have h := congrArg (· ≫ d.hom.app J) sq.vert_inv.w
    simpa [l, m, Category.assoc] using h
  have hP : d.hom.app J ≫ P.map (G.map v) = H.map (P.map v) ≫ d.hom.app K :=
    (d.hom.naturality v).symm
  have hB : d.hom.app K ≫ P.map t ≫ b = H.map b ≫ c.hom.app B ≫ E.map z := by
    simpa only [IsWeilEquivariant, transportWeilDatum, Iso.symm_inv, Category.assoc] using hb.symm
  let w := E.preimage (a ≫ P.map v ≫ b)
  have hE : H.map a ≫ H.map (P.map v) ≫ H.map b ≫ c.hom.app B =
      c.hom.app A ≫ E.map (F.map w) := by
    have ht : H.map (E.map w) ≫ c.hom.app B = c.hom.app A ≫ E.map (F.map w) :=
      c.hom.naturality w
    simpa only [w, E.map_preimage, H.map_comp, Category.assoc] using ht
  apply E.map_injective
  simp only [E.map_preimage, E.map_comp, P.map_comp, Category.assoc]
  rw [reassoc_of% ai, reassoc_of% hP, hB, reassoc_of% hE, Iso.inv_hom_id_app_assoc]

end WeilII
