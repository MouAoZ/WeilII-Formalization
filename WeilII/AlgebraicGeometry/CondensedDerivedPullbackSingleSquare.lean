module

import WeilConjectures.Tactic.TransportExact
import WeilII.CategoryTheory.PullbackSquareInSingleCharts

public import WeilII.AlgebraicGeometry.WeilSingleFrobenius
public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar

/-! # The geometric pullback square on a degree-zero representative -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII.ExternalProduct
open CompactSupportClasses

universe u
variable {ℓ : ℕ} [Fact ℓ.Prime]
set_option quotPrecheck false
local notation "Λ" => Profinite.padicAlgClRingObj ℓ
local notation "U" => CondensedRing.upperStar Λ
local notation "H" => pull (ℓ := ℓ)
local notation "S" X => DerivedCategory.singleFunctor (Coeff ℓ X) 0
local notation "λ₀" f => (U f).singleFunctorCompLeftDerivedFunctorIso.hom

/-- Composition of exact pullbacks in the degree-zero chart. -/
private lemma compSingle {X Y Z : Scheme.{u}} (a : X ⟶ Y) (f : Y ⟶ Z)
    (M : Coeff ℓ Z) :
    (leftDerivedUpperStarComp Λ a f).hom.app ((S Z).obj M) ≫
        (H a).map ((λ₀ f).app M) ≫ (λ₀ a).app ((U f).obj M) =
      (λ₀ (a ≫ f)).app M ≫ (S X).map ((CondensedRing.upperStarComp Λ a f).hom.app M) := by
  have hc := Functor.leftDerivedFunctorCompIso_hom_app_singleFunctor_obj (U f) (U a) M
  have hn := Functor.leftDerivedFunctorNatIso_hom_app_singleFunctor_obj
    (U (a ≫ f)) (U f ⋙ U a) (CondensedRing.upperStarComp Λ a f) M
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hc).trans hn)

private lemma compareCompositeSquares {C D T T₀ : Type*}
    [Category* C] [Category* D] [Category* T] [Category* T₀]
    (J : C ⥤ D) {A B L R : T ⥤ D} {A₀ B₀ L₀ R₀ : T₀ ⥤ C}
    (l : A ≅ L) (r : B ≅ R) (t : A ≅ B) (q : L ≅ R) (m : T)
    (l₀ : A₀ ≅ L₀) (r₀ : B₀ ≅ R₀) (t₀ : A₀ ≅ B₀) (n : T₀)
    (q₀ : L₀.obj n ≅ R₀.obj n)
    (a : A.obj m ⟶ J.obj (A₀.obj n)) (b : B.obj m ⟶ J.obj (B₀.obj n))
    {I K : D} (u : L.obj m ⟶ I) (v : I ⟶ J.obj (L₀.obj n))
    (x : R.obj m ⟶ K) (y : K ⟶ J.obj (R₀.obj n))
    (hq : q = l.symm ≪≫ t ≪≫ r) (hq₀ : q₀ = (l₀.app n).symm ≪≫ t₀.app n ≪≫ r₀.app n)
    (hl : l.hom.app m ≫ u ≫ v = a ≫ J.map (l₀.hom.app n))
    (hr : r.hom.app m ≫ x ≫ y = b ≫ J.map (r₀.hom.app n))
    (ht : t.hom.app m ≫ b = a ≫ J.map (t₀.hom.app n)) :
    q.hom.app m ≫ x ≫ y = u ≫ v ≫ J.map q₀.hom := by
  subst q q₀
  apply (cancel_epi (l.hom.app m)).1
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, NatTrans.comp_app,
    Category.assoc, Iso.hom_inv_id_app_assoc, hr, reassoc_of% ht, reassoc_of% hl,
    ← J.map_comp]

private abbrev squarePull {X W : Scheme.{u}} (h : X ⟶ W) :=
  (fun {L : _ ⥤ _} {R : _ ⥤ _} (_ : L ⊣ R) ↦ L) (derivedUpperStarLowerStarAdjunction Λ h)

private lemma congrSingle {X W : Scheme.{u}} {i j : X ⟶ W} (e : i = j)
    (M : Coeff ℓ W) :
    (eqToIso (congrArg (squarePull (ℓ := ℓ)) e)).hom.app ((S W).obj M) ≫ (λ₀ j).app M =
      (λ₀ i).app M ≫ (S X).map ((CondensedRing.upperStarCongr Λ e).hom.app M) := by
  subst j
  simp [CondensedRing.upperStarCongr]

private theorem square_iso {X Y Z W : Scheme.{u}} {a : X ⟶ Y} {f : Y ⟶ W}
    {b : X ⟶ Z} {g : Z ⟶ W} (w : a ≫ f = b ≫ g) :
    pullbackSquareComparison Λ (CommSq.mk w).flip =
      (leftDerivedUpperStarComp Λ a f).symm ≪≫
      eqToIso (congrArg (squarePull (ℓ := ℓ)) w) ≪≫ leftDerivedUpperStarComp Λ b g := rfl

/-- In the single chart, the derived pullback square is the ordinary pullback square. -/
theorem derivedPullbackSquare_single {X Y Z W : Scheme.{u}} {a : X ⟶ Y} {f : Y ⟶ W}
    {b : X ⟶ Z} {g : Z ⟶ W} (w : a ≫ f = b ≫ g) (M : Coeff ℓ W) :
    (pullbackSquareComparison Λ (CommSq.mk w).flip).hom.app ((S W).obj M) ≫
        (H b).map ((λ₀ g).app M) ≫ (λ₀ b).app ((U g).obj M) =
      (H a).map ((λ₀ f).app M) ≫ (λ₀ a).app ((U f).obj M) ≫
        (S X).map ((CondensedRing.upperStarSquareIso Λ w M).hom) := by
  exact compareCompositeSquares (S X)
    (leftDerivedUpperStarComp Λ a f) (leftDerivedUpperStarComp Λ b g)
    (eqToIso (congrArg (squarePull (ℓ := ℓ)) w)) (pullbackSquareComparison Λ (CommSq.mk w).flip)
    ((S W).obj M)
    (CondensedRing.upperStarComp Λ a f) (CondensedRing.upperStarComp Λ b g)
    (CondensedRing.upperStarCongr Λ w) M (CondensedRing.upperStarSquareIso Λ w M)
    ((λ₀ (a ≫ f)).app M) ((λ₀ (b ≫ g)).app M)
    ((H a).map ((λ₀ f).app M)) ((λ₀ a).app ((U f).obj M))
    ((H b).map ((λ₀ g).app M)) ((λ₀ b).app ((U g).obj M))
    (square_iso (ℓ := ℓ) w) rfl (compSingle a f M) (compSingle b g M)
    (by transport_exact (congrSingle w M))

/-- Pull an equivariant single chart through a commuting square of endomorphisms of schemes.
The chosen coefficient map and its ordinary square determine the action in the new chart. -/
theorem derivedPullbackSingleChart {X Y : Scheme.{u}}
    (r : X ⟶ Y) (f : Y ⟶ Y) (g : X ⟶ X) (w : g ≫ r = r ≫ f)
    (K : DerivedCategory (Coeff ℓ Y)) (A : Coeff ℓ Y) (B : Coeff ℓ X)
    (b : K ⟶ (S Y).obj A) (v : (U r).obj A ⟶ B) (φ : (H f).obj K ⟶ K)
    (u : (U f).obj A ⟶ A) (u' : (U g).obj B ⟶ B)
    (a : (H r).obj K ⟶ (S X).obj B) (p : (H r).obj ((H f).obj K) ⟶ (H r).obj K)
    (d : (H g).obj ((H r).obj K) ⟶ (H r).obj ((H f).obj K))
    (t : (H f).obj ((S Y).obj A) ⟶ (S Y).obj A)
    (t' : (H g).obj ((S X).obj B) ⟶ (S X).obj B)
    (ha : a = (H r).map b ≫ (λ₀ r).app A ≫ (S X).map v)
    (hp : p = (H r).map φ)
    (hd : d = (pullbackSquareComparison Λ (CommSq.mk w).flip).hom.app K)
    (ht : t = (λ₀ f).app A ≫ (S Y).map u)
    (ht' : t' = (λ₀ g).app B ≫ (S X).map u')
    (hu : (U g).map v ≫ u' = (CondensedRing.upperStarSquareIso Λ w A).hom ≫ (U r).map u ≫ v)
    (hφ : φ ≫ b = (H f).map b ≫ t) : (H g).map a ≫ t' = d ≫ p ≫ a := by
  exact pullChartOfSingleSquare (S Y) (S X) (H r) (H f) (H g) (U r) (U f) (U g)
    (pullbackSquareComparison Λ (CommSq.mk w).flip).hom (λ₀ r) (λ₀ f) (λ₀ g) b v φ u u'
    (CondensedRing.upperStarSquareIso Λ w A).hom a p d t t' ha hp hd ht ht' hu hφ
    (by transport_exact (derivedPullbackSquare_single w A))

end WeilII.ExternalProduct
