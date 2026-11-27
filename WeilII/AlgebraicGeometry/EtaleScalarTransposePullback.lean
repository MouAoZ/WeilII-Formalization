module

public import WeilII.AlgebraicGeometry.EtaleScalarRestrictionPullbackSingle
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionKummerClass
public import WeilConjectures.CategoryTheory.Adjunction.MateTransposeIsIso

/-! # Pullback of the derived transpose of a semilinear map -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false

namespace WeilII

private theorem transposeSquare {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {G : A ⥤ C} {H : B ⥤ D} {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (s : TwoSquare R H G R') {M : A} {N : B} {M' : C} {N' : D}
    (u : M ⟶ R.obj N) (v : M' ⟶ R'.obj N') (i : G.obj M ⟶ M') (j : H.obj N ⟶ N')
    (h : G.map u ≫ s.app N ≫ R'.map j = i ≫ v) :
    L'.map i ≫ (b.homEquiv _ _).symm v =
      ((mateEquiv a b).symm s).app M ≫ H.map ((a.homEquiv _ _).symm u) ≫ j := by
  rw [← b.homEquiv_naturality_left_symm, ← h, ← Category.assoc, b.homEquiv_naturality_right_symm,
    a.homEquiv_symm_map_comp_app b, Category.assoc]

private theorem singleArrowSquare {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (P : A ⥤ D) (R : B ⥤ D)
    {SY SZ W : A} {TY TX T' : B} {K A' Z N : D}
    (g : SY ⟶ SZ) (e : W ≅ SZ) (s : P.obj W ⟶ R.obj TY)
    (t : TY ⟶ TX) (j : TX ⟶ T') (b : R.obj TX ≅ Z) (b' : R.obj T' ≅ N)
    (c : P.obj SZ ⟶ K) (u : P.obj SY ⟶ A') (l : A' ⟶ K) (σ : K ⟶ Z) (z : Z ⟶ N)
    {Z' : D} (i : A' ⟶ Z') (g' : Z' ⟶ N)
    (h1 : s ≫ R.map t ≫ b.hom = P.map e.hom ≫ c ≫ σ)
    (h2 : R.map j ≫ b'.hom = b.hom ≫ z)
    (h3 : P.map g ≫ c = u ≫ l) (h4 : l ≫ σ ≫ z = i ≫ g') :
    P.map (g ≫ e.inv) ≫ s ≫ R.map (t ≫ j) = (u ≫ i) ≫ g' ≫ b'.inv := by
  apply (cancel_mono b'.hom).1
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h2, reassoc_of% h1, ← P.map_comp_assoc e.inv e.hom, e.inv_hom_id,
    P.map_id, Category.id_comp, reassoc_of% h3, h4]

open CategoryTheory.Limits in
private theorem singleTransposeSquare {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D] [Abelian A] [Abelian B]
    [Abelian C] [Abelian D] [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : B ⥤ A) (V : D ⥤ C) [U.Additive] [V.Additive] [PreservesFiniteLimits U]
    [PreservesFiniteColimits U] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    {J : _root_.DerivedCategory A ⥤ _root_.DerivedCategory B}
    {K : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D}
    (a : J ⊣ U.mapDerivedCategory) (b : K ⊣ V.mapDerivedCategory)
    (p : A ⥤ C) (q : B ⥤ D) (P : _root_.DerivedCategory A ⥤ _root_.DerivedCategory C)
    (Q : _root_.DerivedCategory B ⥤ _root_.DerivedCategory D)
    (s : U.mapDerivedCategory ⋙ P ⟶ Q ⋙ V.mapDerivedCategory) (σ : U ⋙ p ⟶ q ⋙ V)
    (s' : P ⋙ K ⟶ J ⋙ Q) (hs' : s' = (mateEquiv a b).symm s)
    (c : _root_.DerivedCategory.singleFunctor A 0 ⋙ P ⟶ p ⋙ _root_.DerivedCategory.singleFunctor C 0)
    (e : _root_.DerivedCategory.singleFunctor B 0 ⋙ Q ⟶ q ⋙ _root_.DerivedCategory.singleFunctor D 0)
    {M : A} {N : B} {M' : C} {N' : D}
    (g : M ⟶ U.obj N) (g' : M' ⟶ V.obj N') (i : p.obj M ⟶ M') (j : q.obj N ⟶ N')
    (h1 : s.app ((_root_.DerivedCategory.singleFunctor _ 0).obj N) ≫
      V.mapDerivedCategory.map (e.app N) ≫ (V.mapDerivedCategorySingleFunctor 0).hom.app (q.obj N) =
      P.map ((U.mapDerivedCategorySingleFunctor 0).hom.app N) ≫ c.app _ ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map (σ.app N))
    (h : p.map g ≫ σ.app N ≫ V.map j = i ≫ g') :
    K.map (c.app M ≫ (_root_.DerivedCategory.singleFunctor _ 0).map i) ≫
        ShortComplex.ShortExact.singleTranspose V b g' =
      s'.app ((_root_.DerivedCategory.singleFunctor _ 0).obj M) ≫
        Q.map (ShortComplex.ShortExact.singleTranspose U a g) ≫ e.app N ≫
          (_root_.DerivedCategory.singleFunctor _ 0).map j := by
  subst s'
  let S := _root_.DerivedCategory.singleFunctor C 0
  let T := _root_.DerivedCategory.singleFunctor D 0
  let S₀ := _root_.DerivedCategory.singleFunctor A 0
  let u := U.mapDerivedCategorySingleFunctor 0
  let v := V.mapDerivedCategorySingleFunctor 0
  let raw := S₀.map g ≫ u.inv.app N
  let raw' := S.map g' ≫ v.inv.app N'
  have hw : P.map raw ≫ s.app _ ≫ V.mapDerivedCategory.map (e.app N ≫ T.map j) =
      (c.app M ≫ S.map i) ≫ raw' := by
    exact singleArrowSquare P V.mapDerivedCategory (S₀.map g) (u.app N) (s.app _) (e.app N) (T.map j)
      (v.app (q.obj N)) (v.app N') (c.app _) (c.app M) (S.map (p.map g))
      (S.map (σ.app N)) (S.map (V.map j)) (S.map i) (S.map g') h1 (v.hom.naturality j)
      (c.naturality g) (by simpa only [Functor.map_comp] using congrArg S.map h)
  exact transposeSquare a b s raw raw' _ _ hw
variable {A B : Type (u + 1)} [CommRing A] [CommRing B] (ρ : A →+* B)
  {X Y : Scheme.{u}} (f : X ⟶ Y)

variable {a : A} (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})

set_option maxHeartbeats 65000 in
/-- A square of semilinear maps of sheaves gives a pullback square on their derived
transposes between single complexes. -/
theorem singleTranspose_pullback
    {M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)}
    {M' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {N' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (g : M ⟶ (Sheaf.restrictScalars _ ρ).obj N) (g' : M' ⟶ (Sheaf.restrictScalars _ ρ).obj N')
    (i : (f)^*[ModuleCat.{u + 1} A].obj M ⟶ M') (j : (f)^*[ModuleCat.{u + 1} B].obj N ⟶ N')
    (h : (f)^*[ModuleCat.{u + 1} A].map g ≫ (upperStarRestrictScalarsIso ρ f).hom.app N ≫
        (Sheaf.restrictScalars _ ρ).map j = i ≫ g') :
    (derivedExtendScalars hρ ha X).map ((singleFunctorCompLeftDerivedUpperStarIso _ f).hom.app M ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map i) ≫
      ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars _ ρ)
        (derivedExtendScalarsAdjunction hρ ha X) g' =
    (derivedExtendScalarsPullbackIso hρ ha f).hom.app ((_root_.DerivedCategory.singleFunctor _ 0).obj M) ≫
      L((f)^*[ModuleCat.{u + 1} B]).map (ShortComplex.ShortExact.singleTranspose
        (Sheaf.restrictScalars _ ρ) (derivedExtendScalarsAdjunction hρ ha Y) g) ≫
      (singleFunctorCompLeftDerivedUpperStarIso _ f).hom.app N ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map j :=
  singleTransposeSquare (Sheaf.restrictScalars _ ρ) (Sheaf.restrictScalars _ ρ)
    (derivedExtendScalarsAdjunction hρ ha Y) (derivedExtendScalarsAdjunction hρ ha X)
    ((f)^*[ModuleCat.{u + 1} A]) ((f)^*[ModuleCat.{u + 1} B])
    L((f)^*[ModuleCat.{u + 1} A]) L((f)^*[ModuleCat.{u + 1} B])
    (leftDerivedUpperStarRestrictScalarsIso ρ f).hom (upperStarRestrictScalarsIso ρ f).hom
    (derivedExtendScalarsPullbackIso hρ ha f).hom rfl
    (singleFunctorCompLeftDerivedUpperStarIso _ f).hom (singleFunctorCompLeftDerivedUpperStarIso _ f).hom
    g g' i j (etaleRestrictScalarsPullback_single ρ f N) h

end WeilII
