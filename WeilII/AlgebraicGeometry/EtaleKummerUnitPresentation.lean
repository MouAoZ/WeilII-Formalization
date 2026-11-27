module

public import WeilII.AlgebraicGeometry.EtaleKummerDerivedUnit
public import WeilII.AlgebraicGeometry.EtaleKummerFreeGenerator

/-! # The coefficient unit in the free integral presentation -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Etale
open CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

private theorem transpose_basis_square {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (G : D ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {F : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D} (adj : F ⊣ G.mapDerivedCategory)
    {M M' : C} {N N' : D} (g : M ⟶ G.obj N) (g' : M' ⟶ G.obj N') (i : M ⟶ M') (j : N ⟶ N')
    (h : g ≫ G.map j = i ≫ g') :
    ShortComplex.ShortExact.singleTranspose G adj g ≫ (_root_.DerivedCategory.singleFunctor D 0).map j =
      F.map ((_root_.DerivedCategory.singleFunctor C 0).map i) ≫ ShortComplex.ShortExact.singleTranspose G adj g' := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_left]
  simp only [ShortComplex.ShortExact.singleTranspose, Equiv.apply_symm_apply, Category.assoc]
  have hn := (G.mapDerivedCategorySingleFunctor 0).inv.naturality j
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc]

private theorem eta_basis {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {M U T : C} {N V W : D} (i : M ≅ U) (j : U ≅ T) (k : N ≅ V) (l : V ≅ W)
    (η : F.obj T ⟶ W) (t : F.obj M ⟶ N) (v : F.obj U ⟶ V)
    (hv : F.map j.hom ≫ η ≫ l.inv = v) (ht : t ≫ k.hom = F.map i.hom ≫ v) :
    η = F.map (j.inv ≫ i.inv) ≫ t ≫ k.hom ≫ l.hom := by
  rw [← Category.assoc t, ht, ← hv]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← F.map_comp_assoc i.inv i.hom, Iso.inv_hom_id, F.map_id, Category.id_comp,
    ← F.map_comp_assoc j.inv j.hom, Iso.inv_hom_id, F.map_id, Category.id_comp]

private theorem transpose_presentations {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (G : D ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {F : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D} (adj : F ⊣ G.mapDerivedCategory)
    {M U : C} {N V : D} {T : _root_.DerivedCategory C} {W : _root_.DerivedCategory D}
    (i : M ≅ U) (k : N ≅ V) (j : (_root_.DerivedCategory.singleFunctor C 0).obj U ≅ T)
    (l : (_root_.DerivedCategory.singleFunctor D 0).obj V ≅ W) (η : F.obj T ⟶ W)
    (g : M ⟶ G.obj N) (v : U ⟶ G.obj V) (h : g ≫ G.map k.hom = i.hom ≫ v)
    (hv : F.map j.hom ≫ η ≫ l.inv = ShortComplex.ShortExact.singleTranspose G adj v) :
    η = F.map (j.symm ≪≫ (_root_.DerivedCategory.singleFunctor C 0).mapIso i.symm).hom ≫
      ShortComplex.ShortExact.singleTranspose G adj g ≫
      (l.symm ≪≫ (_root_.DerivedCategory.singleFunctor D 0).mapIso k.symm).inv :=
  eta_basis F ((_root_.DerivedCategory.singleFunctor C 0).mapIso i) j
    ((_root_.DerivedCategory.singleFunctor D 0).mapIso k) l η _ _ hv
    (transpose_basis_square _ _ _ _ _ _ h)

/-- The coefficient unit computed on the direct free integral presentations agrees with
the monoidal coefficient unit. -/
theorem etaleKummer_eta_freePresentation {A B : Type (u+1)} [CommRing A] [CommRing B]
    {ρ : A →+* B} (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})
    (X : Scheme.{u}) :
    (derivedExtendScalarsConstantComplexEtaIso hρ ha X).hom =
      (derivedExtendScalars hρ ha X).map (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit X A).hom ≫
        ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars _ ρ)
          (derivedExtendScalarsAdjunction hρ ha X) ((extendScalarsToRestrictScalars ρ X).app X.constantSheafInt) ≫
        (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit X B).inv := by
  exact transpose_presentations (Sheaf.restrictScalars _ ρ) (derivedExtendScalarsAdjunction hρ ha X)
    (extendScalarsConstantZModIso X (Λ := A) (n := 0) (by simp))
    (extendScalarsConstantZModIso X (Λ := B) (n := 0) (by simp))
    (singleFunctorObjUnitIso (ModuleCat.{u+1} A) X) (singleFunctorObjUnitIso (ModuleCat.{u+1} B) X)
    _ _ _ (etaleKummer_freeBasis_reduction ρ X) (etaleKummer_singleTranspose_unit hρ ha X)

end WeilII
