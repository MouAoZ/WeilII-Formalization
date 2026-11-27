/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The degree-zero projection generalizes the native Weil-sheaf calculation in
WeilConjectures.WeilSheaf.DerivedHomSingleResolution.
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedHomComplex

/-! # Internal Hom complexes with a single source and an exact second variable -/

open CategoryTheory Limits Opposite

namespace WeilII

variable {C : Type*} [Category* C] [Abelian C] [HasCountableProducts C]
  (H : Cᵒᵖ ⥤ C ⥤ C) [H.Additive] [∀ A, (H.obj A).Additive]

private noncomputable def projection (A : C) (I : CochainComplex C ℤ) :
    CochainComplex.bifunctorHomObj H
        ((CochainComplex.singleFunctor _ 0).obj A) I ⟶
      ((H.obj (op A)).mapHomologicalComplex (.up ℤ)).obj I where
  f n := CochainComplex.bifunctorHomπ H
      ((CochainComplex.singleFunctor _ 0).obj A) I n 0 n (zero_add n) ≫
    (H.map
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv.op).app (I.X n)
  comm' n m _ := by
    rw [Category.assoc,
      CochainComplex.bifunctorHomObj_d_π_assoc _ _ _ n m 0 m (zero_add m) n
        (m - n) (zero_add n) (by omega)]
    simp only [CochainComplex.singleFunctor_obj_d, op_zero, Functor.map_zero,
      NatTrans.app_zero, comp_zero, sub_zero, Int.negOnePow_zero, one_smul,
      Functor.mapHomologicalComplex_obj_d, Category.assoc]
    exact congrArg (CochainComplex.bifunctorHomπ H
      ((CochainComplex.singleFunctor _ 0).obj A) I n 0 n (zero_add n) ≫ ·)
      ((H.map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv.op).naturality (I.d n m)).symm

private theorem projection_isIso (A : C) (I : CochainComplex C ℤ) :
    IsIso (projection H A I) := by
  classical
  have : ∀ n, IsIso ((projection H A I).f n) := by
    intro n
    let j : (((H.obj (op A)).mapHomologicalComplex (.up ℤ)).obj I).X n ⟶
        (CochainComplex.bifunctorHomObj H
          ((CochainComplex.singleFunctor _ 0).obj A) I).X n :=
      CochainComplex.bifunctorHomLift _ _ _ n fun p q hpq ↦
        if h : p = 0 then by
          subst p
          simp only [zero_add] at hpq
          cases (show q = n by omega)
          exact (H.map
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom.op).app (I.X n)
        else 0
    refine ⟨⟨j, ?_, ?_⟩⟩
    · apply CochainComplex.bifunctorHomObj_hom_ext
      intro p q hpq
      by_cases h : p = 0
      · subst p
        simp only [zero_add] at hpq
        cases (show q = n by omega)
        simp only [projection, j, Category.assoc,
          CochainComplex.bifunctorHomLift_π, ↓reduceDIte, ← NatTrans.comp_app,
          ← Functor.map_comp, ← op_comp, Iso.hom_inv_id, op_id,
          H.map_id, NatTrans.id_app, Category.id_comp]
        erw [Category.comp_id]
      · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 A p h
        have hz' := ((evaluation _ _).obj (I.X q)).map_isZero
          (H.map_isZero hz.op)
        exact hz'.eq_of_tgt _ _
    · simp [projection, j, ← NatTrans.comp_app,
        ← Functor.map_comp, ← op_comp]
  exact HomologicalComplex.Hom.isIso_of_components _

private lemma projection_left (A B : C) (a : A ⟶ B)
    (I : CochainComplex C ℤ) :
    CochainComplex.bifunctorHomMapLeft (H := H) (Y := I)
        ((CochainComplex.singleFunctor _ 0).map a) ≫ projection H A I =
      projection H B I ≫
        (NatTrans.mapHomologicalComplex (H.map a.op) (.up ℤ)).app I := by
  apply HomologicalComplex.Hom.ext
  funext n
  dsimp only [HomologicalComplex.comp_f, projection]
  rw [Category.assoc, CochainComplex.bifunctorHomMapLeft_f_π_assoc]
  change _ ≫ (H.map
    (((CochainComplex.singleFunctor _ 0).map a).f 0).op).app (I.X n) ≫ _ =
    _ ≫ _ ≫ (H.map a.op).app (I.X n)
  rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]
  rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]
  congr 3
  simp [CochainComplex.singleFunctor, HomologicalComplex.single_map_f_self]

private def termwise (I : CochainComplex C ℤ) : Cᵒᵖ ⥤ CochainComplex C ℤ where
  obj A := ((H.obj A).mapHomologicalComplex _).obj I
  map f := ((H.map f).mapHomologicalComplex _).app I
  map_id A := by ext k; simp
  map_comp f g := by ext k; simp

/-- For a family of sources on which the second variable of an additive bifunctor is exact,
the Hom complex from a degree-zero single into a resolution of a degree-`d` single represents
the ordinary bifunctor placed in degree `d`, naturally in the source. -/
public theorem nonempty_bifunctorHomQSingleIso [HasDerivedCategory C]
    {B : Type*} [Category* B] (U : B ⥤ C) (T : C) (d : ℤ) (I : CochainComplex C ℤ)
    (g : (CochainComplex.singleFunctor C d).obj T ⟶ I) [QuasiIso g]
    (hlim : ∀ M, PreservesFiniteLimits (H.obj (op (U.obj M))))
    (hcolim : ∀ M, PreservesFiniteColimits (H.obj (op (U.obj M)))) :
    Nonempty ((U ⋙ CochainComplex.singleFunctor C 0).op ⋙ DerivedCategory.bifunctorHomQFunctor H I ≅
      U.op ⋙ H.flip.obj T ⋙ DerivedCategory.singleFunctor C d) := by
  let S := (CochainComplex.singleFunctor C d).obj T
  let p : (U ⋙ CochainComplex.singleFunctor C 0).op ⋙ DerivedCategory.bifunctorHomQFunctor H I ≅
      U.op ⋙ termwise H I ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun M ↦ by
      exact DerivedCategory.Q.mapIso (@asIso _ _ _ _ _ (projection_isIso H (U.obj M.unop) I)))
      (fun f ↦ by
        exact (DerivedCategory.Q.map_comp _ _).symm.trans
          ((DerivedCategory.Q.congr_map (projection_left H _ _ (U.map f.unop) I)).trans
            (DerivedCategory.Q.map_comp _ _)))
  let r : U.op ⋙ termwise H S ⋙ DerivedCategory.Q ≅ U.op ⋙ termwise H I ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun M ↦ by
      have h₁ := hlim M.unop
      have h₂ := hcolim M.unop
      let g' := ((H.obj (op (U.obj M.unop))).mapHomologicalComplex _).map g
      have hg : IsIso (DerivedCategory.Q.map g') :=
        (DerivedCategory.isIso_Q_map_iff_quasiIso C g').2 (inferInstanceAs (QuasiIso g'))
      exact @asIso _ _ _ _ _ hg)
      (fun f ↦ by
        exact (DerivedCategory.Q.map_comp _ _).symm.trans
          ((DerivedCategory.Q.congr_map
            ((((H.map (U.op.map f)).mapHomologicalComplex _).naturality g).symm)).trans
            (DerivedCategory.Q.map_comp _ _)))
  let e : termwise H S ≅ H.flip.obj T ⋙ CochainComplex.singleFunctor C d :=
    NatIso.ofComponents (fun M ↦ (HomologicalComplex.singleMapHomologicalComplex
      (H.obj M) (.up ℤ) d).app T) (fun {M M'} f ↦ by
        change ((H.map f).mapHomologicalComplex _).app S ≫ _ = _
        rw [HomologicalComplex.natTransMapHomologicalComplex_app_single_obj]
        simp
        rfl)
  exact ⟨p ≪≫ r.symm ≪≫ Functor.isoWhiskerLeft U.op (Functor.isoWhiskerRight e DerivedCategory.Q)⟩

end WeilII
