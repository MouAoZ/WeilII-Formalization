module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointLift
import WeilConjectures.CategoryTheory.Exact.ExactDerivedCohomologyCoherence

/-! # Descent on homology of a map out of a single complex -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor DerivedCategory

namespace WeilII

universe u v w

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Applying homology to the conjugate of a representative by a derived descent
datum gives the conjugate of the map on homology by the original descent datum. -/
theorem homSingleToHomology_descent
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    (F : C ⥤ C) [F.Additive] [F.IsEquivalence] [HasDerivedCategory.{w} C]
    [HasDerivedCategory.{w} (IsoAlgebra F)]
    (P : C) (uP : P ⟶ F.obj P) (K : DerivedCategory (IsoAlgebra F)) (i : ℤ)
    (v : (singleFunctor C i).obj P ⟶ (IsoAlgebra.forget F).mapDerivedCategory.obj K) :
    let U := IsoAlgebra.forget F
    let h := U.mapDerivedCategoryHomologyFunctorIso i
    let v' := (singleFunctor C i).map uP ≫ (F.mapDerivedCategorySingleFunctor i).inv.app P ≫
      F.mapDerivedCategory.map v ≫ (IsoAlgebra.derivedStrIso F).hom.app K
    homSingleToHomology P i _ v' ≫ h.inv.app K =
      uP ≫ F.map (homSingleToHomology P i _ v ≫ h.inv.app K) ≫
        ((homologyFunctor (IsoAlgebra F) i).obj K).str.hom := by
  let U := IsoAlgebra.forget F
  let h := U.mapDerivedCategoryHomologyFunctorIso i
  let H := homologyFunctor C i
  let S := singleFunctor C i
  let t := singleFunctorCompHomologyFunctorIso C i
  let b := F.mapDerivedCategoryHomologyFunctorIso i
  let s := F.mapDerivedCategorySingleFunctor i
  let d := (IsoAlgebra.derivedStrIso F).hom.app K
  let W := (homologyFunctor (IsoAlgebra F) i).obj K
  have hs : b.app (S.obj P) ≪≫ H.mapIso (s.app P) ≪≫ t.app (F.obj P) =
      F.mapIso (t.app P) := Iso.ext (F.mapDerivedCategoryHomologyFunctorIso_hom_app_singleFunctor i P)
  have hu : t.inv.app (F.obj P) ≫ H.map (s.inv.app P) =
      F.map (t.inv.app P) ≫ b.hom.app (S.obj P) := by
    have ee := congrArg Iso.inv hs
    change (t.inv.app (F.obj P) ≫ H.map (s.inv.app P)) ≫ b.inv.app (S.obj P) =
      F.map (t.inv.app P) at ee
    rw [← ee, Category.assoc, Iso.inv_hom_id_app]
    exact (Category.comp_id _).symm
  have hc : F.map (h.hom.app K) ≫ b.hom.app (U.mapDerivedCategory.obj K) ≫ H.map d =
      W.str.hom ≫ h.hom.app K :=
    (Functor.exactDerivedCohomologyCoherence U F i).2 U (IsoAlgebra.strNatIso F) K
  have hd : b.hom.app (U.mapDerivedCategory.obj K) ≫ H.map d ≫ h.inv.app K =
      F.map (h.inv.app K) ≫ W.str.hom := by
    apply (cancel_epi (F.map (h.hom.app K))).1
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, F.map_id]
    erw [Category.id_comp]
    have c := congrArg (· ≫ h.inv.app K) hc
    simp only [Category.assoc, Iso.hom_inv_id_app] at c
    exact c.trans (Category.comp_id _)
  have hn : b.hom.app (S.obj P) ≫ H.map (F.mapDerivedCategory.map v) =
      F.map (H.map v) ≫ b.hom.app (U.mapDerivedCategory.obj K) := (b.hom.naturality v).symm
  have ht : t.inv.app P ≫ H.map (S.map uP) = uP ≫ t.inv.app (F.obj P) :=
    (t.inv.naturality uP).symm
  change (t.inv.app P ≫ H.map (S.map uP ≫ s.inv.app P ≫ F.mapDerivedCategory.map v ≫ d)) ≫
    h.inv.app K = uP ≫ F.map ((t.inv.app P ≫ H.map v) ≫ h.inv.app K) ≫ W.str.hom
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% ht, reassoc_of% hu, reassoc_of% hn, hd]

end WeilII
