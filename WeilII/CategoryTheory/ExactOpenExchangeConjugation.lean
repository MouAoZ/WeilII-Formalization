module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedExactLift
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareCube
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeFormalism

/-! # Deriving an exchange of exact left adjoints after changing Frobenius coordinates -/

public section

open CategoryTheory CategoryTheory.Endofunctor
namespace WeilII

private theorem openMateChange {A B : Type*} [Category A] [Category B]
    {J : A ⥤ B} {U : B ⥤ A} (adj : J ⊣ U)
    {P F : A ⥤ A} {Q G : B ⥤ B} (x : P ≅ F) (y : Q ≅ G)
    (b : J ⋙ Q ≅ P ⋙ J) (e : J ⋙ G ≅ F ⋙ J)
    (h : mateEquiv adj adj e.inv ≫ Functor.whiskerRight y.inv U =
      Functor.whiskerLeft U x.inv ≫ mateEquiv adj adj b.inv) :
    Functor.isoWhiskerLeft J y ≪≫ e = b ≪≫ Functor.isoWhiskerRight x J := by
  apply Iso.ext
  apply (Iso.inv_eq_inv _ _).mp
  apply (mateEquiv adj adj).injective
  exact (mateEquiv_comp_whiskerLeft adj adj e.inv y.inv).trans
    (h.trans (mateEquiv_whiskerRight_comp adj adj x.inv b.inv).symm)

private theorem deriveOpenConjugation {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (J : A ⥤ B) [J.Additive] [Limits.PreservesFiniteLimits J] [Limits.PreservesFiniteColimits J]
    {P F : A ⥤ A} [P.Additive] [F.Additive] [Limits.PreservesFiniteLimits P]
    [Limits.PreservesFiniteColimits P] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    {Q G : B ⥤ B} [Q.Additive] [G.Additive] [Limits.PreservesFiniteLimits Q]
    [Limits.PreservesFiniteColimits Q] [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    (x : P ≅ F) (y : Q ≅ G) (b : J ⋙ Q ≅ P ⋙ J) (e : J ⋙ G ≅ F ⋙ J)
    (h : Functor.isoWhiskerLeft J y ≪≫ e = b ≪≫ Functor.isoWhiskerRight x J)
    (K : DerivedCategory A) :
    (Functor.mapDerivedCategoryNatIso y).hom.app (J.mapDerivedCategory.obj K) ≫
        (Functor.mapDerivedCategorySquareIso e).hom.app K =
      (Functor.mapDerivedCategorySquareIso b).hom.app K ≫
        J.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso x).hom.app K) := by
  have hh := congrArg (fun z ↦ (Functor.mapDerivedCategorySquareIso
    (F₁ := J) (F₂ := Q) (G₁ := F) (G₂ := J) z).hom) h
  rw [Functor.mapDerivedCategorySquareIso_trans_hom (H₁ := J) (H₂ := G),
    Functor.mapDerivedCategorySquareIso_trans_hom (H₁ := P) (H₂ := J),
    Functor.mapDerivedCategorySquareIso_isoWhiskerLeft_hom,
    Functor.mapDerivedCategorySquareIso_isoWhiskerRight_hom] at hh
  exact congr_app hh K

private theorem pullConjugationHom {C : Type*} [Category C] {A B D E : C}
    (ex : A ≅ B) (θ : A ≅ D) (ey : D ≅ E) (a : B ≅ E)
    (h : a = ex.symm ≪≫ θ ≪≫ ey) :
    a.hom ≫ ey.inv = ex.inv ≫ θ.hom := by
  subst a
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem openExchangeOfPull {A B : Type*} [Category A] [Category B]
    {J : A ⥤ B} {U : B ⥤ A} (adj : J ⊣ U)
    {P F : A ⥤ A} {Q G : B ⥤ B} (x : P ≅ F) (y : Q ≅ G)
    (b : J ⋙ Q ≅ P ⋙ J) (e : J ⋙ G ≅ F ⋙ J)
    (θ : U ⋙ P ≅ Q ⋙ U) (a : U ⋙ F ≅ G ⋙ U)
    (hb : b.inv = Adjunction.exchangeLeft adj adj θ)
    (he : mateEquiv adj adj e.inv = a.hom)
    (h : a = (Functor.isoWhiskerLeft U x).symm ≪≫ θ ≪≫ Functor.isoWhiskerRight y U) :
    Functor.isoWhiskerLeft J y ≪≫ e = b ≪≫ Functor.isoWhiskerRight x J := by
  apply openMateChange adj
  rw [he, hb, Adjunction.exchangeLeft_eq_mateEquiv_symm, Equiv.apply_symm_apply]
  exact pullConjugationHom (Functor.isoWhiskerLeft U x) θ (Functor.isoWhiskerRight y U) a h

/-- For an exact left adjoint, changing the endpoint coordinates in its restriction
square changes the exact derived exchange by the derived endpoint isomorphisms.
The inverse open exchange is the left mate of restriction. Apply the mate bijection
to the two paths and then derive the resulting equality of squares. -/
theorem exactOpenExchangeConjugation {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (J : A ⥤ B) [J.Additive] [Limits.PreservesFiniteLimits J] [Limits.PreservesFiniteColimits J]
    {P F : A ⥤ A} [P.Additive] [F.Additive] [Limits.PreservesFiniteLimits P]
    [Limits.PreservesFiniteColimits P] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    {Q G : B ⥤ B} [Q.Additive] [G.Additive] [Limits.PreservesFiniteLimits Q]
    [Limits.PreservesFiniteColimits Q] [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    {U : B ⥤ A} (adj : J ⊣ U) [F.IsEquivalence] [G.IsEquivalence]
    (x : P ≅ F) (y : Q ≅ G) (b : J ⋙ Q ≅ P ⋙ J) (e : J ⋙ G ≅ F ⋙ J)
    (θ : U ⋙ P ≅ Q ⋙ U) (a : U ⋙ F ≅ G ⋙ U)
    (hb : b.inv = Adjunction.exchangeLeft adj adj θ)
    (he : mateEquiv adj adj e.inv = a.hom)
    (h : a = (Functor.isoWhiskerLeft U x).symm ≪≫ θ ≪≫ Functor.isoWhiskerRight y U)
    (K : DerivedCategory A) :
    (Functor.mapDerivedCategoryNatIso y).hom.app (J.mapDerivedCategory.obj K) ≫
        (IsoAlgebra.derivedExactCommIso e).hom.app K =
      (Functor.mapDerivedCategoryCompIsoOfIso b).hom.app K ≫
        J.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso x).hom.app K) := by
  have hg := openExchangeOfPull adj x y b e θ a hb he h
  have v := deriveOpenConjugation J x y b e hg K
  simpa only [IsoAlgebra.derivedExactCommIso, Functor.mapDerivedCategoryCompIsoOfIso,
    Functor.mapDerivedCategorySquareIso, Iso.trans_assoc] using v

end WeilII
