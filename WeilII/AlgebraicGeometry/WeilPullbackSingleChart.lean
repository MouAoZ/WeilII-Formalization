module

public import WeilII.AlgebraicGeometry.SingleFrobeniusUpperStar
import WeilII.AlgebraicGeometry.CondensedPullbackWeilSquare
import WeilII.AlgebraicGeometry.CondensedDerivedPullbackSingleSquare
import WeilConjectures.Tactic.TransportExact

/-! # Pullback of an equivariant degree-zero chart of a Weil sheaf -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII.ExternalProduct
open CompactSupportClasses

universe u
variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
set_option quotPrecheck false
local notation "Λ" => Profinite.padicAlgClRingObj ℓ
local notation "γ" Z => (Z ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.hom
local notation "fib" Z => (Z ↘ Spec (.of k)).geometricFiber
local notation "E" Z => (adicSheafEquivCondensedMod ℓ (fib Z)).functor
local notation "S" Z => DerivedCategory.singleFunctor (Coeff ℓ (fib Z)) 0
local notation "U" => CondensedRing.upperStar Λ
local notation "H" => pull (ℓ := ℓ)
local notation "φ₀" Z "," W => ((ProEtaleWeilSheaf.toCondensedUpperStar k ℓ Z).obj W).str.hom

variable (r : X ⟶ Y) [r.IsOver (Spec (.of k))] (W : ProEtaleWeilSheaf k ℓ Y)
local notation "r̄" => Scheme.Hom.geometricFiberMap r (comp_over r (Spec (.of k)))
local notation "sq" => Scheme.Hom.commSq_geometricGaloisFrobenius r (comp_over r (Spec (.of k)))
local notation "W'" => (ProEtaleWeilSheaf.upperStar k ℓ r).obj W
local notation "ξ" => (adicUpperStarCompCondensedModIso ℓ r̄).inv.app W.carrier

/-- An equivariant presentation of a native single remains equivariant after geometric
pullback and passage to the canonical single chart of the pulled-back Weil sheaf. -/
theorem weilPullbackSingleChart (K : DerivedCategory (Coeff ℓ (fib Y)))
    (b : K ⟶ (S Y).obj ((E Y).obj W.carrier)) (φ : (H (γ Y)).obj K ⟶ K)
    (a : (H r̄).obj K ⟶ (S X).obj ((E X).obj (W').carrier))
    (p : (H r̄).obj ((H (γ Y)).obj K) ⟶ (H r̄).obj K)
    (d : (H (γ X)).obj ((H r̄).obj K) ⟶ (H r̄).obj ((H (γ Y)).obj K))
    (ha : a = (H r̄).map b ≫ (U r̄).singleFunctorCompLeftDerivedFunctorIso.hom.app
      ((E Y).obj W.carrier) ≫ (S X).map (X := (U r̄).obj ((E Y).obj W.carrier))
        (Y := (E X).obj (W').carrier) ξ)
    (hp : p = (H r̄).map φ) (hd : d = (pullbackSquareComparison Λ (sq).flip).hom.app K)
    (hφ : φ ≫ b = (H (γ Y)).map b ≫ singleFrobenius W) :
    (H (γ X)).map a ≫ singleFrobenius (X := X) (W') = d ≫ p ≫ a := by
  fo_apply (derivedPullbackSingleChart (ℓ := ℓ) r̄ (γ Y) (γ X) (sq).w K
    ((E Y).obj W.carrier) ((E X).obj (W').carrier)) using
    b, ξ, φ, (φ₀ Y, W), (φ₀ X, (W')), a, p, d,
    (singleFrobenius (X := Y) W), (singleFrobenius (X := X) (W')),
    fo_late ha, fo_late hp, fo_late hd,
    fo_late (singleFrobenius_upperStar (X := Y) W),
    fo_late (singleFrobenius_upperStar (X := X) (W')),
    fo_late (condensedPullbackWeilSquare r W), fo_late hφ

private theorem chartHom {C D C₀ : Type*} [Category* C] [Category* D] [Category* C₀]
    (R : C ⥤ D) (J : C₀ ⥤ D) {K A : C} {B N : C₀}
    (b : K ≅ A) (l : R.obj A ≅ J.obj B) (v : N ≅ B) (a : R.obj K ≅ J.obj N)
    (h : a = R.mapIso b ≪≫ l ≪≫ J.mapIso v.symm) :
    a.hom = R.map b.hom ≫ l.hom ≫ J.map v.inv := by subst a; rfl

/-- In isomorphism charts, the chart factorization can be supplied before passing to
underlying morphisms. -/
theorem weilPullbackSingleIsoChart (K : DerivedCategory (Coeff ℓ (fib Y)))
    (b : K ≅ (S Y).obj ((E Y).obj W.carrier)) (φ : (H (γ Y)).obj K ⟶ K)
    (a : (H r̄).obj K ≅ (S X).obj ((E X).obj (W').carrier))
    (p : (H r̄).obj ((H (γ Y)).obj K) ⟶ (H r̄).obj K)
    (d : (H (γ X)).obj ((H r̄).obj K) ⟶ (H r̄).obj ((H (γ Y)).obj K))
    (ha : a = (H r̄).mapIso b ≪≫ (U r̄).singleFunctorCompLeftDerivedFunctorIso.app
      ((E Y).obj W.carrier) ≪≫ (S X).mapIso (((adicUpperStarCompCondensedModIso ℓ r̄).app W.carrier).symm))
    (hp : p = (H r̄).map φ) (hd : d = (pullbackSquareComparison Λ (sq).flip).hom.app K)
    (hφ : φ ≫ b.hom = (H (γ Y)).map b.hom ≫ singleFrobenius W) :
    (H (γ X)).map a.hom ≫ singleFrobenius (X := X) (W') = d ≫ p ≫ a.hom := by
  refine weilPullbackSingleChart r W K b.hom φ a.hom p d ?_ hp hd hφ
  exact chartHom (H r̄) (S X) b
    ((U r̄).singleFunctorCompLeftDerivedFunctorIso.app ((E Y).obj W.carrier))
    ((adicUpperStarCompCondensedModIso ℓ r̄).app W.carrier) a ha

end WeilII.ExternalProduct
