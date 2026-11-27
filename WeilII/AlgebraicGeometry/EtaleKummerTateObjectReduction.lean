module

public import WeilII.AlgebraicGeometry.EtaleKummerTateSheafReduction
public import WeilConjectures.WeilSheaf.SmoothPuritySingleFlatNaturality

/-! # The direct positive Tate comparison in the derived category -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] {ρ : A →+* B}
  {V : Scheme.{u}} {C : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}}
  (φ : C ⟶ V.gmSheaf) {d : ℕ} (hd : ringChar A = ringChar B * d)

variable [NeZero (ringChar A)] [NeZero (ringChar B)]
  [HasInvertibleExponent A V] [HasInvertibleExponent B V]

variable (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})

/-- Compose a flat base-change square with isomorphisms to the single-complex models. -/
private theorem pasteFlatIso {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {M T Q : C} {N T' Q' U W : D} (u : M ≅ T) (a : T ≅ Q) (v : N ≅ T') (b : T' ≅ Q')
    (c : F.obj T ≅ U) (e : F.obj Q ≅ W) (t : U ≅ T') (k : F.obj Q ⟶ Q')
    (r : W ⟶ Q') (z : U ⟶ W) (hn : F.map a.hom ≫ e.hom = c.hom ≫ z)
    (hs : t.hom ≫ b.hom = z ≫ r) (ht : k = e.hom ≫ r) :
    (F.mapIso u ≪≫ c ≪≫ t ≪≫ v.symm).hom = F.map (u ≪≫ a).hom ≫ k ≫ (v ≪≫ b).inv := by
  apply (cancel_mono (v ≪≫ b).hom).1
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp, ht]
  rw [hs, reassoc_of% hn]

private theorem pasteSheaf {C D : Type*} [Category C] [Category D]
    (S : C ⥤ D) {E G : Type*} [Category E] [Category G] (T : E ⥤ G)
    (J : C ⥤ E) (F : D ⥤ G)
    {A B : C} {A' B' : E} {X : D} {Y : G}
    (u : X ≅ S.obj A) (v : Y ≅ T.obj A') (a : A ≅ B) (b : A' ≅ B')
    (c : F.obj (S.obj A) ≅ T.obj (J.obj A)) (e : F.obj (S.obj B) ≅ T.obj (J.obj B))
    (t : J.obj A ≅ A') (r : J.obj B ≅ B') (k : F.obj (S.obj B) ⟶ T.obj B')
    (hs : t.hom ≫ b.hom = J.map a.hom ≫ r.hom)
    (hn : F.map (S.map a.hom) ≫ e.hom = c.hom ≫ T.map (J.map a.hom))
    (ht : k = e.hom ≫ T.map r.hom) :
    (F.mapIso u ≪≫ c ≪≫ T.mapIso t ≪≫ v.symm).hom =
      F.map (u ≪≫ S.mapIso a).hom ≫ k ≫ (v ≪≫ T.mapIso b).inv := by
  have h := congrArg T.map hs
  rw [T.map_comp, T.map_comp] at h
  exact pasteFlatIso F u (S.mapIso a) v (T.mapIso b) c e (T.mapIso t) k (T.map r.hom)
    (T.map (J.map a.hom)) hn h ht
/-- The direct (unshifted) positive Tate comparison is the first Kummer transpose
in the degree-zero models of the two roots-of-unity sheaves. -/
theorem positiveTateObjectReduction_eq_kummer :
    (derivedExtendScalarsTateObjectIso hρ ha V 1).hom =
      (derivedExtendScalars hρ ha V).map (tateTwistObjectOneIso V A).hom ≫
        ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars V.smallEtaleTopology ρ)
          (derivedExtendScalarsAdjunction hρ ha V) (kummerSequenceReductionMap ρ φ hd).τ₁ ≫
        (tateTwistObjectOneIso V B).inv := by
  let E := Sheaf.extendScalars V.smallEtaleTopology ρ
  have := preservesKFlatQuasiIso_extendScalars hρ ha V
  let S := _root_.DerivedCategory.singleFunctor (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) 0
  have hP := flat_tateTwistSheaf A V 1
  have hQ := ObjectProperty.prop_of_iso ObjectProperty.flat (tateTwistSheafOneIso V A) hP
  exact pasteSheaf (_root_.DerivedCategory.singleFunctor _ 0) S E (derivedExtendScalars hρ ha V)
    (tateTwistObjectIsoSingleFunctor A V 1) (tateTwistObjectIsoSingleFunctor B V 1)
    (tateTwistSheafOneIso V A) (tateTwistSheafOneIso V B)
    (E.leftDerivedFunctorSingleFunctorIsoOfFlat hP) (E.leftDerivedFunctorSingleFunctorIsoOfFlat hQ)
    (sheafExtendScalarsTateTwistSheafIso ρ V 1) (sheafExtendScalarsTateSheafIso ρ V)
    (ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars _ ρ)
      (derivedExtendScalarsAdjunction hρ ha V) (kummerSequenceReductionMap ρ φ hd).τ₁)
    (tateTwistSheafOne_reduction (ρ := ρ) (V := V))
    (E.leftDerivedFunctorSingleFunctorIsoOfFlat_naturality hP hQ (tateTwistSheafOneIso V A).hom)
    (kummerFirstTranspose_flat φ hd hρ ha)

end WeilII
