module

public import WeilII.AlgebraicGeometry.EtaleScalarTransposePullback

/-! # Geometric pullback in degree-zero models of coefficient reduction -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

/-- Transport a commuting coefficient square along isomorphisms of its four objects. -/
private theorem transportPullSquare {C D E F : Type*}
    [Category* C] [Category* D] [Category* E] [Category* F]
    (P : C ⥤ D) (J : C ⥤ E) (K : D ⥤ F) (Q : E ⥤ F) (s : P ⋙ K ⟶ J ⋙ Q)
    {A M : C} {B N : E} {A' M' : D} {B' N' : F}
    (u : A ≅ M) (v : B ≅ N) (u' : A' ≅ M') (v' : B' ≅ N')
    (i : P.obj A ⟶ A') (j : Q.obj B ⟶ B') (ii : P.obj M ⟶ M') (jj : Q.obj N ⟶ N')
    (g : J.obj M ⟶ N) (g' : K.obj M' ⟶ N')
    (b₀ : J.obj A ⟶ B) (b₁ : K.obj A' ⟶ B')
    (hb₀ : b₀ = J.map u.hom ≫ g ≫ v.inv) (hb₁ : b₁ = K.map u'.hom ≫ g' ≫ v'.inv)
    (hi : P.map u.hom ≫ ii = i ≫ u'.hom) (hj : Q.map v.hom ≫ jj = j ≫ v'.hom)
    (h : K.map ii ≫ g' = s.app M ≫ Q.map g ≫ jj) :
    s.app A ≫ Q.map b₀ ≫ j = K.map i ≫ b₁ := by
  rw [hb₀, hb₁]
  apply (cancel_mono v'.hom).1
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hj, ← Q.map_comp_assoc v.inv v.hom, Iso.inv_hom_id, Q.map_id, Category.id_comp]
  have hn : K.map (P.map u.hom) ≫ s.app M = s.app A ≫ Q.map (J.map u.hom) := s.naturality _
  rw [← reassoc_of% hn, ← h, ← K.map_comp_assoc, hi, K.map_comp, Category.assoc]

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] {ρ : A →+* B}
  {X Y : Scheme.{u}} (f : X ⟶ Y) (hρ : Function.Surjective ρ)
  {a : A} (ha : RingHom.ker ρ = Ideal.span {a})

/-- Naturality of coefficient reduction in a pair of degree-zero sheaf models. -/
theorem etaleReductionPullback_of_singleModels
    {M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)} {N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)}
    {M' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)} {N' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (g : M ⟶ (Sheaf.restrictScalars _ ρ).obj N) (g' : M' ⟶ (Sheaf.restrictScalars _ ρ).obj N')
    (i : (f)^*[ModuleCat.{u + 1} A].obj M ⟶ M') (j : (f)^*[ModuleCat.{u + 1} B].obj N ⟶ N')
    (h : (f)^*[ModuleCat.{u + 1} A].map g ≫ (upperStarRestrictScalarsIso ρ f).hom.app N ≫
        (Sheaf.restrictScalars _ ρ).map j = i ≫ g')
    {T : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u+1} A))}
    {U : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u+1} B))}
    {T' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A))}
    {U' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} B))}
    (o : T ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj M)
    (p : U ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj N)
    (o' : T' ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj M')
    (p' : U' ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj N')
    (k : (L((f)^*[ModuleCat.{u+1} A])).obj T ⟶ T') (l : (L((f)^*[ModuleCat.{u+1} B])).obj U ⟶ U')
    (b : (derivedExtendScalars hρ ha Y).obj T ⟶ U) (b' : (derivedExtendScalars hρ ha X).obj T' ⟶ U')
    (hb : b = (derivedExtendScalars hρ ha Y).map o.hom ≫ ShortComplex.ShortExact.singleTranspose
      (Sheaf.restrictScalars _ ρ) (derivedExtendScalarsAdjunction hρ ha Y) g ≫ p.inv)
    (hb' : b' = (derivedExtendScalars hρ ha X).map o'.hom ≫ ShortComplex.ShortExact.singleTranspose
      (Sheaf.restrictScalars _ ρ) (derivedExtendScalarsAdjunction hρ ha X) g' ≫ p'.inv)
    (hi : L((f)^*[ModuleCat.{u + 1} A]).map o.hom ≫ (singleFunctorCompLeftDerivedUpperStarIso _ f).hom.app M ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map i = k ≫ o'.hom)
    (hj : L((f)^*[ModuleCat.{u + 1} B]).map p.hom ≫ (singleFunctorCompLeftDerivedUpperStarIso _ f).hom.app N ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map j = l ≫ p'.hom) :
    (derivedExtendScalarsPullbackIso hρ ha f).hom.app T ≫ L((f)^*[ModuleCat.{u + 1} B]).map b ≫ l =
      (derivedExtendScalars hρ ha X).map k ≫ b' :=
  transportPullSquare L((f)^*[ModuleCat.{u + 1} A]) (derivedExtendScalars hρ ha Y)
    (derivedExtendScalars hρ ha X) L((f)^*[ModuleCat.{u + 1} B]) (derivedExtendScalarsPullbackIso hρ ha f).hom
    o p o' p' k l _ _ _ _ b b' hb hb' hi hj (singleTranspose_pullback ρ f hρ ha g g' i j h)

end WeilII
