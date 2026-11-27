module

public import WeilConjectures.WeilSheaf.SmoothPurityNativeDescent
public import WeilConjectures.WeilSheaf.CondensedModelGeometricFiberPullback
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Descent of a finite-base complex presented in native coefficients -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- If a native adic cochain complex presents a bounded constructible condensed object,
its termwise geometric pullback presents the native Weil descent of that object. The
ordinary change-of-model square identifies geometric pullback, after the Weil coefficient
equivalence, with a composite of exact functors. The equivalence reflects finite limits
and colimits, so all four functors in the square are exact. Derive the square, evaluate
on the given representative and apply the inverse derived equivalence and its unit.
Source: `WeilSheaf/CondensedModelGeometricFiberPullback`. -/
public theorem finiteBaseDescentComplex {k : Type u} [Field k] [Finite k]
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] (V : Scheme.{u}) [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (P : Dᵇc(V)⟦Profinite.padicAlgClRingObj ℓ⟧)
    [(ProEtaleWeilSheaf.geometricFiberPullback k ℓ V).PreservesZeroMorphisms]
    (C : CochainComplex (AdicSheaf ℓ V) ℤ)
    (h : P.obj ≅ DerivedCategory.Q.obj
      (((adicSheafEquivCondensedMod ℓ V).functor.mapHomologicalComplex (.up ℤ)).obj C)) :
    Nonempty (((WeilComplex.finiteBaseNativeDescent (k₀ := k)).obj P).obj ≅
      DerivedCategory.Q.obj (((ProEtaleWeilSheaf.geometricFiberPullback k ℓ V).mapHomologicalComplex
        (.up ℤ)).obj C)) := by
  let p := ProEtaleWeilSheaf.geometricFiberPullback k ℓ V
  let g := geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj ℓ) (V ↘ Spec (.of k))
  let E := (adicSheafEquivCondensedMod ℓ V).functor
  let D := ProEtaleWeilSheaf.toCondensed k ℓ V
  let q := ProEtaleWeilSheaf.geometricFiberPullbackCompToCondensedIso k ℓ V
  let : Limits.PreservesFiniteLimits (p ⋙ D) := Limits.preservesFiniteLimits_of_natIso q.symm
  let : Limits.PreservesFiniteColimits (p ⋙ D) := Limits.preservesFiniteColimits_of_natIso q.symm
  let : Limits.PreservesFiniteLimits p := Limits.preservesFiniteLimits_of_reflects_of_preserves p D
  let : Limits.PreservesFiniteColimits p := Limits.preservesFiniteColimits_of_reflects_of_preserves p D
  let : p.Additive := Functor.additive_of_preserves_binary_products p
  let T := ProEtaleWeilSheaf.derivedEquivCondensed k ℓ V
  let s := (Functor.mapDerivedCategorySquareIso (F₁ := E) (F₂ := g) (G₁ := p) (G₂ := D) q.symm).app
    (DerivedCategory.Q.obj C)
  let W := DerivedCategory.Q.obj ((p.mapHomologicalComplex (.up ℤ)).obj C)
  let m := (eqToIso (ProEtaleWeilSheaf.derivedEquivCondensed_functor
    (k₀ := k) (l := ℓ) (X := V)).symm).app W
  let e : g.mapDerivedCategory.obj P.obj ≅ T.functor.obj W :=
    g.mapDerivedCategory.mapIso (h ≪≫ (E.mapDerivedCategoryFactors.app C).symm) ≪≫
      s ≪≫ D.mapDerivedCategory.mapIso (p.mapDerivedCategoryFactors.app C) ≪≫ m
  exact ⟨T.inverse.mapIso e ≪≫ T.unitIso.symm.app W⟩

end WeilII
