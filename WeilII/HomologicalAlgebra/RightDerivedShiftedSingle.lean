module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

open CategoryTheory Limits

namespace WeilII

/-- Evaluation of exact right derived functors on a shifted single, naturally in the exact
functor. Apply the resolution unit to the single in degree `-s`. Its components are invertible
by exactness, and its defining Kan extension identity gives naturality in coefficient maps. -/
public theorem rightDerivedShiftedSingle
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (W : C) (s : ℤ) :
    let K := DerivedCategory.singleFunctor C 0 ⋙ shiftFunctor _ s
    let L := DerivedCategory.singleFunctor D 0 ⋙ shiftFunctor _ s
    ∃ e : ∀ (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F],
      F.rightDerivedFunctor.obj (K.obj W) ≅ L.obj (F.obj W),
      ∀ (F G : C ⥤ D) [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
        [PreservesFiniteColimits F] [PreservesFiniteColimits G] (η : F ⟶ G),
        (Functor.rightDerivedFunctorNatTrans η).app (K.obj W) ≫ (e G).hom =
          (e F).hom ≫ L.map (η.app W) := by
  intro K L
  let P := (CochainComplex.singleFunctor C (-s)).obj W
  let a := ((DerivedCategory.singleFunctors C).shiftIso s (-s) 0 (add_neg_cancel s)).app W
  let b := (DerivedCategory.singleFunctors D).shiftIso s (-s) 0 (add_neg_cancel s)
  let c (F : C ⥤ D) [F.Additive] :=
    (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) (-s)).app W
  let u (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
      DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj P) ≅
        F.rightDerivedFunctor.obj (DerivedCategory.Q.obj P) := by
    have : IsIso (F.rightDerivedFunctorUnitQ P) := by
      unfold Functor.rightDerivedFunctorUnitQ
      infer_instance
    exact asIso (F.rightDerivedFunctorUnitQ P)
  refine ⟨fun F _ _ _ ↦ F.rightDerivedFunctor.mapIso a ≪≫ (u F).symm ≪≫
    DerivedCategory.Q.mapIso (c F) ≪≫ (b.app _).symm, ?_⟩
  intro F G _ _ _ _ _ _ η
  have h : (u F).hom ≫ (Functor.rightDerivedFunctorNatTrans η).app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((η.mapHomologicalComplex _).app P) ≫ (u G).hom := by
    change F.rightDerivedFunctorUnitQ P ≫ _ = _ ≫ G.rightDerivedFunctorUnitQ P
    simp only [Functor.rightDerivedFunctorUnitQ, Category.assoc]
    rw [(Functor.rightDerivedFunctorNatTrans η).naturality]
    simp only [Functor.rightDerivedFunctorNatTrans, Functor.rightDerivedNatTrans_app_assoc]
    erw [← DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  have hc : (η.mapHomologicalComplex _).app P ≫ (c G).hom =
      (c F).hom ≫ (CochainComplex.singleFunctor D (-s)).map (η.app W) := by
    rw [HomologicalComplex.natTransMapHomologicalComplex_app_single_obj]
    simp [c]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [← NatTrans.naturality_assoc]
  apply congrArg (F.rightDerivedFunctor.map a.hom ≫ ·)
  rw [← cancel_epi (u F).hom]
  erw [reassoc_of% h]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc,
    ← Functor.map_comp_assoc, hc, Functor.map_comp_assoc]
  exact congrArg ((DerivedCategory.Q.map (c F).hom) ≫ ·) (b.inv.naturality (η.app W))

end WeilII
